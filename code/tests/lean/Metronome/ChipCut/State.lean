/-
# ChipCut: the whole-chip product of the verification cuts (item 4Q)

This file is the first half of the whole-chip assembly: the product state, the
canonical abstraction to `Metronome.Machine.State`, and the chip-level reset.
It contains no proof of refinement yet; `Metronome/ChipCut/Proof.lean` states
`chip_step_refines` from explicitly named premises.

The product has one component per instance of every cut in the suite:

| component | instances | cut |
|---|---|---|
| `sync` | 1 | `SpiPins.Sync` (the 16-bit pin synchronisers) |
| `rst` | 1 | `Debug.Reset` (`rst_m`, `rst_q`) |
| `rqh` | 1 | the two-cycle configuration-write window counter |
| `freeze` | 1 | `CoreCtl.FreezeState` (`FREEZE`, `FRZ`, `FRZD`) |
| `lines` | 4 | `Line.State` |
| `threads` | 6 | `Thread.State` |
| `cores` | 2 | `Core.State` |
| `cnt` | 3 | `Units.Counter.State` |
| `sh` | 2 | `Units.Shifter.State` |
| `lf` | 2 | `Units.Lfsr.State` |
| `acc` | 1 | `Units.Acc.State` |
| `p0` | 1 | `Mem.State` (the data-RAM arbiter and the host request slot) |
| `streams` | 2 | `Stream.State` |
| `hostCmd` | 1 | `HostCmd.State` |
| `hostRead` | 1 | `HostRead.State` |
| `hostWr` | 1 | `Host.State` (the host-link write/bit-count view) |
| `cq` | 1 | `CoreQueue.State` |
| `arb` | 1 | `Config.State` (the configuration-write arbiter) |
| `bank` | 1 | `Bank.State` (the latch bank contents) |
| `glue` | 1 | `Glue.GlueState` (control, mailbox, flags) |
| `dbgCtrl` | 1 | `Debug.Ctrl.State` |
| `dbgDigest` | 1 | `Debug.Digest.State` |
| `outPins`, `oenPins` | 1 each | `Glue.outNext`/`oeNext` registers (item 4N) |
| `conflict`, `memhaz` | 1 each | the `Moves` sticky error bits |
| `cont` | 1 | memory/configuration contents (SRAM macro and latch bank) |

`Contents` is the explicit boundary the brief asks for: the latch-bank byte
image (`Machine.Config`), program and data memory, the program-memory output
registers `mout`, and the RAM output/owner/lane registers.  Their transition is
the machine's own memory path (`Metronome.Machine.runStep`); that is a stated
trusted contract (SRAM macro black box + configuration decode), not a cut.
`Bank.State` is kept and stepped so the product is complete, and a `BankRel`
invariant records the intended correspondence; it is not used to derive
`Machine.Config` (see CHIPCUT_NOTES.md).
-/

import Metronome
import Metronome.ChipCut.Discharge.BankWire

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace Metronome.ChipCut

open Metronome

/-! ## Packing helpers

The cut inputs are packed buses.  These two recursive packers put item `0` in
the low bits (fixed 2026-11-21: they had item `0` high; found by the CoreUnits
discharge, witness `core_rel_unsatisfiable`), which is the Little-endian order every cut `slice`/`bitAt`
expects. -/

/-- `n` bytes, item `0` in the low bits, as a `BitVec (8n)`. -/
def pack8s : (n : Nat) → (Nat → BitVec 8) → BitVec (8 * n)
  | 0, _ => 0
  | n + 1, f => (f n ++ pack8s n f).cast (by omega)

/-- `n` bits, item `0` in the low bit, as a `BitVec n`. -/
def packBools : (n : Nat) → (Nat → Bool) → BitVec n
  | 0, _ => 0
  | n + 1, f => ((if f n then (1 : BitVec 1) else 0) ++ packBools n f).cast (by omega)

/-- Bit `i` of `packBools n f` is item `i` (item `0` is the low bit). -/
theorem packBools_getLsbD (n : Nat) (f : Nat → Bool) (i : Nat) :
    (packBools n f).getLsbD i = (decide (i < n) && f i) := by
  induction n generalizing i with
  | zero => simp [packBools]
  | succ n ih =>
    simp only [packBools, BitVec.getLsbD_cast, BitVec.getLsbD_append, ih]
    by_cases h : i < n
    · simp [h]; omega
    · by_cases h2 : i = n
      · subst h2; cases f i <;> simp
      · have : ¬ i < n + 1 := by omega
        simp [h, this]
        have hge : 1 ≤ i - n := by omega
        split <;> exact BitVec.getLsbD_of_ge _ _ hge

/-- Order witnesses: item `0` lands in the low bits. -/
theorem packBools_order : packBools 3 (fun i => i == 0) = 1 := by decide
theorem pack8s_order : pack8s 2 (fun i => if i == 0 then 0x12 else 0x34) = 0x3412 := by decide

/-- A byte replicated to all four lanes of a 32-bit scratch word. -/
def quad (b : BitVec 8) : BitVec 32 := ((b ++ b) ++ b) ++ b

/-! ## Contents: the memory and configuration boundary -/

/-- Everything the cuts take as a black-box input: the configuration latch byte
image, the two program memories, the data RAM, the program-memory output
registers, and the data-RAM output register with its owner and lane. -/
structure Contents where
  /-- The configuration latch contents, as the machine's byte image. -/
  cfg : Machine.Config
  /-- Program memory of each core (byte image, word `w` at bytes `8w..8w+7`). -/
  pmem : Vector ByteArray 2
  /-- The data RAM (2,048 bytes). -/
  dmem : ByteArray
  /-- The program-memory output register of each core. -/
  mout : Vector (BitVec 64) 2
  /-- The data-RAM output register. -/
  ramOut : BitVec 32
  /-- The data-RAM output owner: 0 none, 1 S0, 2 S1, 3 P0, 4 host. -/
  ramOwner : Nat
  /-- The data-RAM output byte lane. -/
  ramLane : BitVec 2

/-- Power-on contents. -/
def Contents.init : Contents where
  cfg := Machine.Config.zero
  pmem := Vector.replicate 2 (Machine.Util.bzero 2048)
  dmem := Machine.Util.bzero 2048
  mout := Vector.replicate 2 0
  ramOut := 0
  ramOwner := 0
  ramLane := 0

/-! ## The product state -/

structure State where
  sync : SpiPins.Sync
  rst : Debug.Reset.State
  /-- The two-cycle `rst_q` window counter of the configuration write. -/
  rqh : BitVec 2
  freeze : CoreCtl.FreezeState
  lines : Vector Line.State 4
  threads : Vector Thread.State 6
  cores : Vector Core.State 2
  cnt : Vector Units.Counter.State 3
  sh : Vector Units.Shifter.State 2
  lf : Vector Units.Lfsr.State 2
  acc : Units.Acc.State
  p0 : Mem.State
  streams : Vector Stream.State 2
  hostCmd : HostCmd.State
  hostRead : HostRead.State
  hostWr : Host.State
  cq : CoreQueue.State
  arb : Config.State
  bank : Bank.State
  glue : Glue.GlueState
  dbgCtrl : Debug.Ctrl.State
  dbgDigest : Debug.Digest.State
  outPins : BitVec 14
  oenPins : BitVec 8
  conflict : Bool
  memhaz : Bool
  cont : Contents

/-- The zero product state of the reset branch.  The memory/configuration
contents are supplied by `contentsReset` in `Step.lean`, which follows the
machine's reset. -/
def resetState (cont : Contents) : State where
  sync := SpiPins.resetState
  rst := Debug.Reset.resetState
  rqh := 0
  freeze := CoreCtl.freezeReset
  lines := Vector.replicate 4 Line.resetState
  threads := Vector.replicate 6 Thread.resetState
  cores := Vector.replicate 2 ⟨false, false, 0, 0, 0, 0, 0⟩
  cnt := Vector.replicate 3 Units.Counter.resetState
  sh := Vector.replicate 2 Units.Shifter.resetState
  lf := Vector.replicate 2 Units.Lfsr.resetState
  acc := Units.Acc.resetState
  p0 := Mem.resetState
  streams := Vector.replicate 2 Stream.resetState
  hostCmd := HostCmd.resetState
  hostRead := HostRead.resetState
  hostWr := Host.resetState
  cq := ⟨0, false, 0, 0, false⟩
  arb := ⟨false, false, ⟨0, 0⟩, ⟨0, 0⟩⟩
  bank := ⟨Discharge.BankWire.cfgMaskFin, fun _ => 0⟩
  glue := Glue.resetState
  dbgCtrl := Debug.Ctrl.resetState
  dbgDigest := Debug.Digest.resetState
  outPins := 0
  oenPins := 0
  conflict := false
  memhaz := false
  cont := cont

/-! ## The abstraction to `Metronome.Machine.State` -/

/-- The machine's `nbyte` from the cut's byte state: `CMD → 0`, `IGN → 1`,
`AH → 1`, `AL → 2`, `DATA → 3`. -/
def nbyteOf (ph : BitVec 3) : BitVec 2 :=
  if ph = 0 then 0 else if ph = 1 then 1 else if ph = 2 then 2 else if ph = 3 then 3 else 1

/-- The machine's 2-bit command from the cut's command byte: `0x03 → 2`,
`0x02 → 1`, otherwise `0`. -/
def cmdOf (c : BitVec 8) : BitVec 2 :=
  if c = 0x03 then 2 else if c = 0x02 then 1 else 0

/-- The cut's `lvl`/`rise`/`fall` pin vectors from the synchroniser words; the
`Debug.Pins` cut owns this map (replay overlay included). -/
def pinLvl (s : State) : BitVec 13 :=
  Debug.Pins.level (Debug.Pins.pinVec s.sync.s2) s.dbgCtrl.rlv s.dbgCtrl.emask
    s.dbgCtrl.replay

/-- The previous pin level under the same replay overlay. -/
def pinPrev (s : State) : BitVec 13 :=
  Debug.Pins.previous (Debug.Pins.pinVec s.sync.sp) s.dbgCtrl.rlvPrev s.dbgCtrl.emask
    s.dbgCtrl.replay

/-- The 16-bit line pin level `{3'd0, PIN[12:0]}`. -/
def lvlVec (s : State) : BitVec 16 := Debug.Pins.lvl (pinLvl s)

/-- The 16-bit rising-edge vector. -/
def riseVec (s : State) : BitVec 16 := Debug.Pins.rise (pinLvl s) (pinPrev s)

/-- The 16-bit falling-edge vector. -/
def fallVec (s : State) : BitVec 16 := Debug.Pins.fall (pinLvl s) (pinPrev s)

/-- The canonical abstraction of the product to the whole-chip machine.  The
host link is relational (its `wdata`/`rackv` are only observable under `wr` /
`rack`); `absChip` is the canonical representative, and `ChipRel` in
`Proof.lean` records the relation. -/
def absChip (s : State) : Machine.State where
  r1 := s.rst.rstM
  rq := s.rst.rstQ
  rqh := s.rqh
  sync :=
    { ui1 := BitVec.truncate 8 (BitVec.ushiftRight s.sync.s1 8)
      ui2 := BitVec.truncate 8 (BitVec.ushiftRight s.sync.s2 8)
      uip := BitVec.truncate 8 (BitVec.ushiftRight s.sync.sp 8)
      uio1 := BitVec.truncate 8 s.sync.s1
      uio2 := BitVec.truncate 8 s.sync.s2
      uiop := BitVec.truncate 8 s.sync.sp }
  lines := Vector.ofFn fun l => Bridge.Line.absSt s.lines[l.val]
  threads := Vector.ofFn fun t => Bridge.Thread.absState s.threads[t.val]
  cores := Vector.ofFn fun c => Bridge.Core.absCore s.cont.mout[c.val] s.cores[c.val]
  units :=
    { f := s.glue.fl
      fp := s.glue.flp
      a := s.acc.a
      z := s.acc.z
      c := s.acc.c
      n := s.acc.n
      r := Vector.ofFn fun k => BitVec.truncate 8 (BitVec.ushiftRight s.acc.r (8 * k.val))
      sh := Vector.ofFn fun k =>
        { d := s.sh[k.val].dr, cnt := s.sh[k.val].cnt, len := s.sh[k.val].len,
          msb := s.sh[k.val].msb }
      cnt := Vector.ofFn fun k => s.cnt[k.val].v
      lf := Vector.ofFn fun k => s.lf[k.val].s }
  p0 := Bridge.Mem.absP0 s.p0
  streams := Vector.ofFn fun k => Bridge.StreamB.abs s.streams[k.val]
  host :=
    { rx := BitVec.setWidth 8 s.hostCmd.rx
      tx := s.hostRead.tx
      nbit := s.hostCmd.bitc
      nbyte := nbyteOf s.hostCmd.phase
      cmd := cmdOf s.hostCmd.cmd
      addr := s.hostCmd.addr
      wPend := s.hostCmd.wr
      wData := s.hostCmd.wdata
      rPend := s.hostCmd.rd
      ldV := s.hostRead.rack
      ldD := s.hostRead.rackv
      req := Bridge.Mem.absSlot s.p0 }
  ctrl :=
    { run := s.glue.runG
      irqen := s.glue.irqEn
      conflict := s.conflict
      memhaz := s.memhaz
      cwovr := s.cq.overrun
      inb := s.glue.inB
      inv := s.glue.inv
      invp := s.glue.invp
      outb := s.glue.outB
      outv := s.glue.outv
      db := s.glue.db
      irq := s.glue.irq }
  dbg :=
    { freeze := s.freeze.freeze
      frz := s.freeze.frz
      frzd := s.freeze.frzd
      men := s.dbgDigest.men
      misr := s.dbgDigest.misr
      cen := s.dbgCtrl.cen
      rpl := s.dbgCtrl.replay
      emask := s.dbgCtrl.emask
      dc := s.dbgCtrl.dc
      rlv := s.dbgCtrl.rlv
      rlvp := s.dbgCtrl.rlvPrev }
  cw := Bridge.CfgWrite.cwOf s.cq s.arb
  out := s.outPins
  oen := s.oenPins
  cfg := s.cont.cfg
  pmem := s.cont.pmem
  dmem := s.cont.dmem
  ramOut := s.cont.ramOut
  ramOwner := s.cont.ramOwner
  ramLane := s.cont.ramLane

end Metronome.ChipCut
