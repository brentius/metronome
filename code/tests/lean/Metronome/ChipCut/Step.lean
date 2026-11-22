/-
# ChipCut: one cycle

`step` is the machine-shaped two-phase cycle: it samples the pins, evaluates
the combinational wiring of `Wire.lean` from the current cut states, and runs
every cut's own `step`.  The reset branch (`¬(rst_q ∧ rst_n)`) loads the cut
reset states and the machine's reset contents; the active branch runs the
cuts with `resetN = rst_q ∧ rst_n`.

The two-cycle reset window counter `rqh` and the memory contents are not owned
by a cut: `rqh` is the `Machine.runStep`/`resetStep` shift, and `Contents` is
the machine's own memory path (the SRAM macro and the configuration latch
decode are the stated black-box contract).
-/

import Metronome.ChipCut.Wire

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace Metronome.ChipCut

open Metronome

/-! ## Combinational line outputs and the thread input -/

/-- The four line combinational bundles, from the cut's line state and the cut's
pin/debug registers. -/
def lcsOf (s : State) : Vector Machine.LineComb 4 :=
  Vector.ofFn fun l =>
    Machine.lineComb ((Machine.cfgView s.cont.cfg).lines[l.val]!)
      (Bridge.Line.absSt (lineAt s l.val))
      (Machine.pinView (absChip s).sync (absChip s).dbg) s.freeze.frz

/-- One slot's winner bit. -/
def slotWin (s : State) (pin : Machine.PinIn) (q : Nat) : Bool :=
  Machine.Util.bit (mvWin s pin) q

/-- One slot's destination code. -/
def slotDst (s : State) (pin : Machine.PinIn) (q : Nat) : BitVec 6 :=
  BitVec.truncate 6 (BitVec.ushiftRight (mvDst s pin) (6 * q))

/-- One slot's thread. -/
def slotThread (s : State) (pin : Machine.PinIn) (q : Nat) : BitVec 3 :=
  BitVec.truncate 3 (BitVec.ushiftRight (mvXt s) (3 * (q / 3)))

/-- "The predicate holds of some one of the six move slots". -/
def anySix (f : Nat → Bool) : Bool :=
  f 0 || f 1 || f 2 || f 3 || f 4 || f 5

/-- The paused core's `npc` for thread `t`, if this cycle pauses it. -/
def pauseNpc (s : State) (pin : Machine.PinIn) (t : Nat) : Option (BitVec 8) :=
  let c0 := Core.out false s.cores[0] (coreIn s pin 0)
  let c1 := Core.out true s.cores[1] (coreIn s pin 1)
  if c0.pauseO && c0.xtO.toNat == t then some c0.npcO
  else if c1.pauseO && c1.xtO.toNat == t then some c1.npcO
  else none

/-- Thread `t`'s input. -/
def threadIn (s : State) (pin : Machine.PinIn) (t : Nat) : Thread.Input where
  resetN := runRst s pin
  ev := !s.freeze.frz && Machine.trigEvent (absChip s) (Machine.cfgView s.cont.cfg)
    (Machine.pinView (absChip s).sync (absChip s).dbg) (lcsOf s) t
  db := !s.freeze.frz && Machine.Util.bit s.glue.db t
  disp :=
    ((Core.out false s.cores[0] (coreIn s pin 0)).dispO &&
        (Core.out false s.cores[0] (coreIn s pin 0)).dispE.toNat == t) ||
      ((Core.out true s.cores[1] (coreIn s pin 1)).dispO &&
        (Core.out true s.cores[1] (coreIn s pin 1)).dispE.toNat == t)
  pause := (pauseNpc s pin t).isSome
  npc := (pauseNpc s pin t).getD 0
  stop := anySix fun q => slotValid s pin q && slotDst s pin q == 4 &&
    slotThread s pin q == BitVec.ofNat 3 t
  lateSet := anySix fun q => slotValid s pin q && slotDst s pin q <= 3 && slotDst s pin q != 0 &&
    slotThread s pin q == BitVec.ofNat 3 t && !(threadAt s t).armed
  lineBeat :=
    Line.beat (lineAt s ((Machine.cfgView s.cont.cfg).threads[t]!).line)
      (lineIn s pin ((Machine.cfgView s.cont.cfg).threads[t]!).line)
  hPcWe := hwIsSome s "TRT" t "PC"
  hStatWe := hwIsSome s "TRT" t "STAT"
  hD := hwData s

/-! ## Contents transition (the memory/config contract) -/

/-- The next contents on an active cycle: the machine's own memory/config path
evaluated on the cut state.  `mout` is the program-memory output register of
each core, which the machine keeps inside `CoreSt`. -/
def contentsNext (s : State) (pin : Machine.PinIn) : Contents :=
  let m := (Machine.runStep (absChip s) pin).1
  { cfg := m.cfg
    pmem := m.pmem
    dmem := m.dmem
    mout := Vector.ofFn fun c => m.cores[c.val].mout
    ramOut := m.ramOut
    ramOwner := m.ramOwner
    ramLane := m.ramLane }

/-- The next contents on a reset cycle. -/
def contentsReset (s : State) (pin : Machine.PinIn) : Contents :=
  let m := Machine.resetStep (absChip s) pin
  { cfg := m.cfg
    pmem := m.pmem
    dmem := m.dmem
    mout := Vector.replicate 2 0
    ramOut := m.ramOut
    ramOwner := 0
    ramLane := 0 }

/-! ## The active cycle -/

/-- The cycle's SPI synchroniser input. -/
def spiIn (s : State) (pin : Machine.PinIn) : SpiPins.Input :=
  ⟨runRst s pin, pin.ui, pin.uio⟩

/-- The next reset-window counter. -/
def rqhNext (s : State) (pin : Machine.PinIn) : BitVec 2 :=
  if runRst s pin then BitVec.ofNat 2 ((s.rqh.toNat % 2) * 2 + 1)
  else BitVec.ofNat 2 ((s.rqh.toNat % 2) * 2)

/-- One active clock cycle. -/
def activeStep (s : State) (pin : Machine.PinIn) : State where
  sync := SpiPins.step s.sync (spiIn s pin)
  rst := Debug.Reset.step s.rst ⟨pin.rstn⟩
  rqh := rqhNext s pin
  freeze := CoreCtl.freezeStep s.freeze (freezeIn s pin)
  lines := Vector.ofFn fun l => Line.step (lineAt s l.val) (lineIn s pin l.val)
  threads := Vector.ofFn fun t => Thread.step (threadAt s t.val) (threadIn s pin t.val)
  cores := Vector.ofFn fun c => Core.step (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)
  cnt := Vector.ofFn fun k => Units.Counter.step (cntAt s k.val) (cntIn s pin k.val)
  sh := Vector.ofFn fun k => Units.Shifter.step (shAt s k.val) (shIn s pin k.val)
  lf := Vector.ofFn fun k => Units.Lfsr.step (lfAt s k.val) (lfIn s pin k.val)
  acc := Units.Acc.step s.acc (accIn s pin)
  p0 := Mem.step s.p0 (memIn s pin)
  streams := Vector.ofFn fun k => Stream.step (k.val == 0) (streamAt s k.val) (streamIn s pin k.val)
  hostCmd := HostCmd.step s.hostCmd (hostCmdIn s pin)
  hostRead := HostRead.step s.hostRead (hostReadIn s pin)
  hostWr := Host.step s.hostWr (hostWrIn s pin)
  cq := CoreQueue.step s.cq (cqIn s pin)
  arb := (arbStep s).next
  -- project.v 149-157: the latch cells take u_cfg_stage's REGISTERED we1/addr1/data1, i.e. the
  -- stage state (previousWrite, staged), not this cycle's arbiter grant (fixed 2026-11-21, found by
  -- the MemHostCfg discharge, `bank_lag_witness`).
  bank := Bank.step s.bank s.arb.previousWrite s.arb.staged.addr s.arb.staged.data
  glue := Glue.step s.glue (glueIn s pin)
  dbgCtrl := Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)
  dbgDigest := Debug.Digest.step s.dbgDigest (dbgDigestIn s pin)
  outPins := outNextPins s pin
  oenPins := oenNextPins s pin
  conflict := Moves.stickyNext s.conflict
    ⟨runRst s pin, Moves.conflictOf (mvEn s pin) (mvGrp s pin) (mvXl s) (mvXt s), stickyClear s 0⟩
  memhaz := Moves.stickyNext s.memhaz
    ⟨runRst s pin, Moves.memhazEvent (mvEn s pin) (mvSrc s pin) (Mem.haz s.p0 (memIn s pin))
      s.p0.rdy, stickyClear s 1⟩
  cont := contentsNext s pin

/-! ## The chip -/

/-- The reset cycle: every register takes its cut reset state (except the reset
synchroniser, which still samples `rst_n`, and the window counter) and the
contents follow the machine's reset. -/
def resetChip (s : State) (pin : Machine.PinIn) : State :=
  { resetState (contentsReset s pin) with
    rst := Debug.Reset.step s.rst ⟨pin.rstn⟩
    rqh := rqhNext s pin }

/-- One clock cycle at the pin boundary, with the reset sample of the machine. -/
def step (s : State) (pin : Machine.PinIn) : State :=
  if runRst s pin then activeStep s pin else resetChip s pin

end Metronome.ChipCut
