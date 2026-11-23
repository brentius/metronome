/-
# ChipCut discharge: the host `DBG`-map byte geometry (W5)

This file closes the last eight fields of `ChipCut.Assembly.OpenWiring`'s `dbg`
group, the host-map byte geometry of `MCTL`, `ECTL`, `EMASK` and `RLV`: which
host write byte and which drained core write byte reach which register lane, and
the host-over-core priority per byte (SPEC_V2 §12.4/§13.1/§13.2).

| leaf | result |
|---|---|
| `dbgHmctl` (`DBG.MCTL`, host only, one byte) | proved (`dbgHmctl`) |
| `dbgHectl` (`DBG.ECTL`, host or drain, one byte) | proved (`dbgHectl`) |
| `dbgHEH` (host half of `EMASK`) | **false**: `dbgHEH_false` |
| `dbgHEC` (drain half of `EMASK`) | **false**: `dbgHEC_false` |
| `dbgHESH` (host-selected byte exclusivity, `EMASK`) | **false**: `dbgHESH_false` |
| `dbgHRH` (host half of `RLV`) | **false**: `dbgHRH_false` |
| `dbgHRC` (drain half of `RLV`) | **false**: `dbgHRC_false` |
| `dbgHRSH` (host-selected byte exclusivity, `RLV`) | **false**: `dbgHRSH_false` |

The six refutations have two independent causes, both recorded in
`WIRE_DBGMAP_NOTES.md`:

* the **cut's** `Wire.dbgCtrlIn.hEm0`/`hRlv0` are register-level
  (`hwIsSome`, true for a host write of *either* byte) while the RTL compares
  the window offset (`src/project.v:662/664`, `h_em0 = w_dbg & (o_dbg == 8)`);
  the one-line repair is `byteStrobe (hwAt …) 0`;
* the **machine's** host write and drained core write are separate `Option`s
  (§13.1: a drained runtime write applies before a host write of the same cycle,
  which wins), while the cut's per-byte strobe is their `||`; a host byte and a
  drain byte of the same register in one cycle are therefore not separable by
  `hostOpt2`/`coreOpt2` (`hEH/hEC` for `EMASK`, `hRH/hRC` for `RLV`).

Everything is a kernel proof: no `sorry`, no `native_decide`.

Namespace `Metronome.ChipCut.Discharge.DbgMapWire`; see
`data/raw/lean_chipcut_wire_dbgmap_v4_20261122/` for the evidence.
-/

import Metronome.ChipCut.Discharge.StreamDbg
import Metronome.ChipCut.Discharge.Glue

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Metronome.ChipCut.Discharge.DbgMapWire

open Metronome

/-! ## 1. The machine's host write of the cycle -/

/-- The machine's host write depends only on its host link state. -/
theorem machHw_eq' (m : Machine.State) :
    machHw m = (if m.host.wPend then
      some ⟨m.host.addr.toNat, m.host.wData.toNat, Machine.hostLocate m.host.addr.toNat⟩
      else none) := rfl

/-- The machine's host write of the cycle is the cut's `hwOf` (§9). -/
theorem machHw_eq_hwOf {s : State} {m : Machine.State} (hrel : ChipRel s m) (hinv : Inv s) :
    machHw m = hwOf s := by
  obtain ⟨-, -, -, -, ha5, ha6, ha7, -, -⟩ := hinv.hostAgrees
  obtain ⟨-, -, -, -, -, -, haddr, hwr, hwd, -, -⟩ := hrel.host.base
  have hwr' : m.host.wPend = s.hostRead.wr := hwr.symm
  have haddr' : m.host.addr = s.hostRead.addr := haddr.symm
  have hwd' : s.hostRead.wr = true → s.hostRead.wdata = m.host.wData := hwd
  rw [machHw_eq', hwr', haddr', hwOf]
  simp only [← ha5, ← ha6, ← ha7]
  by_cases hw : s.hostRead.wr = true
  · rw [if_pos hw, if_pos hw, hwd' hw]
  · rw [if_neg hw, if_neg hw]

/-! ## 2. A witness family

One host write byte of a `DBG` register and one drained core write byte, chosen
independently: `witState cont ha hq` is the reset product with `hostCmd.wr`
(and the matching `hostRead` registers) writing `0x5A` to address `ha`, and the
core queue holding one pending runtime write of `0x3C` to address `hq`. -/

/-- The cut's host command machine in a data-byte write of address `a`. -/
def witHostCmd (a : BitVec 16) : HostCmd.State :=
  { phase := HostCmd.ST_DATA, bitc := 0, rx := 0, isRd := false, addr := a, wr := true,
    wdata := 0x5A, rd := false, rack := false, cmd := 0x02 }

/-- The cut's host read machine on the same shared registers. -/
def witHostRead (a : BitVec 16) : HostRead.State :=
  { phase := HostCmd.ST_DATA, bitc := 0, rx := 0, isRd := false, addr := a, wr := true,
    wdata := 0x5A, rd := false, rack := false, tx := 0, rackv := 0 }

/-- The core write queue with one pending runtime write of `0x3C` to `q`. -/
def witCq (q : BitVec 16) : CoreQueue.State :=
  { addr := 0, pending := true, pendingAddr := q, pendingData := 0x3C, overrun := false }

/-- The reset product with the witness host write and queue state. -/
def witState (cont : Contents) (ha hq : BitVec 16) : State :=
  { resetState cont with
    rst := { Debug.Reset.resetState with rstQ := true }
    hostCmd := witHostCmd ha
    hostRead := witHostRead ha
    cq := witCq hq }

theorem lineAt_wit (cont : Contents) (ha hq : BitVec 16) (n : Nat) :
    lineAt (witState cont ha hq) n = Line.resetState := by
  unfold lineAt witState resetState
  split <;> simp

theorem threadAt_wit (cont : Contents) (ha hq : BitVec 16) (n : Nat) :
    threadAt (witState cont ha hq) n = Thread.resetState := by
  unfold threadAt witState resetState
  split <;> simp

theorem streamAt_wit (cont : Contents) (ha hq : BitVec 16) (n : Nat) :
    streamAt (witState cont ha hq) n = Stream.resetState := by
  unfold streamAt witState resetState
  split <;> simp

theorem shAt_wit (cont : Contents) (ha hq : BitVec 16) (n : Nat) :
    shAt (witState cont ha hq) n = Units.Shifter.resetState := by
  unfold shAt witState resetState
  split <;> simp

theorem cntAt_wit (cont : Contents) (ha hq : BitVec 16) (n : Nat) :
    cntAt (witState cont ha hq) n = Units.Counter.resetState := by
  unfold cntAt witState resetState
  split <;> simp

theorem lfAt_wit (cont : Contents) (ha hq : BitVec 16) (n : Nat) :
    lfAt (witState cont ha hq) n = Units.Lfsr.resetState := by
  unfold lfAt witState resetState
  split <;> simp

/-- The witness host link satisfies `LinkRel` (the phase round-trip needs the
data phase, which `absChip` represents as `nbyte = 3`). -/
theorem wit_linkRel (cont : Contents) (ha hq : BitVec 16) :
    Bridge.Host.LinkRel ((witHostRead ha).toHostCmd (witHostCmd ha).cmd)
      (absChip (witState cont ha hq)) := by
  let H : Machine.HostSt :=
    { rx := BitVec.setWidth 8 (witHostRead ha).rx, tx := (witHostRead ha).tx,
      nbit := (witHostCmd ha).bitc, nbyte := nbyteOf (witHostCmd ha).phase,
      cmd := cmdOf (witHostCmd ha).cmd, addr := (witHostCmd ha).addr,
      wPend := (witHostCmd ha).wr, wData := (witHostCmd ha).wdata,
      rPend := (witHostCmd ha).rd, ldV := (witHostRead ha).rack,
      ldD := (witHostRead ha).rackv,
      req := Bridge.Mem.absSlot (witState cont ha hq).p0 }
  have hphase : ((witHostRead ha).toHostCmd (witHostCmd ha).cmd).phase = Bridge.Host.phaseOf H := by
    simp [H, witHostRead, witHostCmd, HostRead.State.toHostCmd, Bridge.Host.phaseOf, nbyteOf, cmdOf]
  have hrx : ((witHostRead ha).toHostCmd (witHostCmd ha).cmd).rx.toNat = H.rx.toNat % 128 := by
    simp [H, witHostRead, HostRead.State.toHostCmd, BitVec.toNat_setWidth]
  have hcz : H.cmd = 0 ↔
      ((witHostRead ha).toHostCmd (witHostCmd ha).cmd).cmd ≠ HostCmd.CMD_WRITE ∧
        ((witHostRead ha).toHostCmd (witHostCmd ha).cmd).cmd ≠ HostCmd.CMD_READ := by
    simp [H, witHostCmd, HostRead.State.toHostCmd, cmdOf]
  have hcn : H.cmd ≠ (3 : BitVec 2) := by
    simp [H, witHostCmd, cmdOf]
  have hir : ((witHostRead ha).toHostCmd (witHostCmd ha).cmd).isRd = true ↔ H.cmd = 2 := by
    simp [H, witHostRead, witHostCmd, HostRead.State.toHostCmd, cmdOf]
  have hwd : ((witHostRead ha).toHostCmd (witHostCmd ha).cmd).wr = true →
      ((witHostRead ha).toHostCmd (witHostCmd ha).cmd).wdata = H.wData := by
    intro _
    rfl
  have hh : (absChip (witState cont ha hq)).host = H := rfl
  refine linkRel_host_congr (s := (witHostRead ha).toHostCmd (witHostCmd ha).cmd)
    (m := absChip (witState cont ha hq))
    (m' := { absChip (witState cont ha hq) with host := H }) hh ?_
  refine Bridge.Host.LinkRel.mk hphase ?_ hrx hcz hcn hir ?_ ?_ hwd ?_ ?_
  · show ((witHostRead ha).toHostCmd (witHostCmd ha).cmd).bitc = H.nbit
    simp [H, witHostRead, witHostCmd, HostRead.State.toHostCmd]
  · show ((witHostRead ha).toHostCmd (witHostCmd ha).cmd).addr = H.addr
    simp [H, witHostRead, witHostCmd, HostRead.State.toHostCmd]
  · show ((witHostRead ha).toHostCmd (witHostCmd ha).cmd).wr = H.wPend
    simp [H, witHostRead, witHostCmd, HostRead.State.toHostCmd]
  · show ((witHostRead ha).toHostCmd (witHostCmd ha).cmd).rd = H.rPend
    simp [H, witHostRead, witHostCmd, HostRead.State.toHostCmd]
  · show ((witHostRead ha).toHostCmd (witHostCmd ha).cmd).rack = H.ldV
    simp [H, witHostRead, HostRead.State.toHostCmd]

/-- The witness host link satisfies `LinkRelR`. -/
theorem wit_linkRelR (cont : Contents) (ha hq : BitVec 16) :
    Bridge.Host.LinkRelR (witHostRead ha) (witHostCmd ha).cmd
      (absChip (witState cont ha hq)) := by
  let H : Machine.HostSt :=
    { rx := BitVec.setWidth 8 (witHostRead ha).rx, tx := (witHostRead ha).tx,
      nbit := (witHostCmd ha).bitc, nbyte := nbyteOf (witHostCmd ha).phase,
      cmd := cmdOf (witHostCmd ha).cmd, addr := (witHostCmd ha).addr,
      wPend := (witHostCmd ha).wr, wData := (witHostCmd ha).wdata,
      rPend := (witHostCmd ha).rd, ldV := (witHostRead ha).rack,
      ldD := (witHostRead ha).rackv,
      req := Bridge.Mem.absSlot (witState cont ha hq).p0 }
  have hh : (absChip (witState cont ha hq)).host = H := rfl
  have hbase : Bridge.Host.LinkRel ((witHostRead ha).toHostCmd (witHostCmd ha).cmd)
      { absChip (witState cont ha hq) with host := H } := by
    have hl := wit_linkRel cont ha hq
    exact linkRel_host_congr (s := (witHostRead ha).toHostCmd (witHostCmd ha).cmd)
      (m := absChip (witState cont ha hq))
      (m' := { absChip (witState cont ha hq) with host := H }) hh hl
  refine linkRelR_host_congr (s := witHostRead ha) (cmd := (witHostCmd ha).cmd)
    (m := absChip (witState cont ha hq))
    (m' := { absChip (witState cont ha hq) with host := H }) hh ?_
  refine Bridge.Host.LinkRelR.mk hbase ?_ ?_
  · show (witHostRead ha).tx = H.tx
    simp [H, witHostRead]
  · show (witHostRead ha).rack = true → (witHostRead ha).rackv = H.ldD
    intro hr
    simp [H, witHostRead] at hr

/-- The witness state relates to its canonical abstraction. -/
theorem wit_chipRel (cont : Contents) (ha hq : BitVec 16) (hzero : BankWire.MaskedZero cont.cfg) :
    ChipRel (witState cont ha hq) (absChip (witState cont ha hq)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- sync
    unfold SyncRel
    simp [witState, resetState, absChip, SpiPins.resetState]
  · -- lines
    intro l
    rw [lineAt_wit]
    simp [witState, resetState, absChip, Bridge.Line.absSt, Line.resetState]
  · -- threads
    intro t
    rw [threadAt_wit]
    simp [witState, resetState, absChip, Bridge.Thread.absState, Thread.resetState]
  · -- cores
    intro c
    simp only [absChip, vecGet_ofFn]
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    intro _
    rfl
  · -- mout
    intro c
    simp only [absChip, vecGet_ofFn, Bridge.Core.absCore]
  · -- units
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro k
      simp only [absChip, vecGet_ofFn]
    · intro k
      show (absChip (witState cont ha hq)).units.sh[k] =
        ({ d := (shAt (witState cont ha hq) k.val).dr,
           cnt := (shAt (witState cont ha hq) k.val).cnt,
           len := (shAt (witState cont ha hq) k.val).len,
           msb := (shAt (witState cont ha hq) k.val).msb } : Machine.ShSt)
      rw [shAt_wit]
      simp [witState, resetState, absChip, Units.Shifter.resetState]
    · intro k
      show (absChip (witState cont ha hq)).units.cnt[k] =
        (cntAt (witState cont ha hq) k.val).v
      rw [cntAt_wit]
      simp [witState, resetState, absChip, Units.Counter.resetState]
    · intro k
      show (absChip (witState cont ha hq)).units.lf[k] =
        (lfAt (witState cont ha hq) k.val).s
      rw [lfAt_wit]
      simp [witState, resetState, absChip, Units.Lfsr.resetState]
  · -- p0
    show P0Rel (Bridge.Mem.absP0 (witState cont ha hq).p0) (witState cont ha hq).p0
    exact p0Rel_abs _
  · -- streams
    intro k
    rw [streamAt_wit]
    unfold Bridge.StreamB.AbsRelB Bridge.StreamB.BufRel
    simp [witState, resetState, absChip, Bridge.StreamB.abs, Stream.resetState]
  · -- host
    exact wit_linkRelR cont ha hq
  · -- hostReq
    rfl
  · -- ctrl
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- dbg
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- cw
    show CwRel (Bridge.CfgWrite.cwOf (witState cont ha hq).cq (witState cont ha hq).arb)
      (witState cont ha hq).cq (witState cont ha hq).arb
    exact cwRel_abs _ _
  · -- bank
    show BankRel (witState cont ha hq).bank (witState cont ha hq).cont.cfg
    exact bankRel_reset _ hzero
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The witness state satisfies the reachable-state invariant. -/
theorem wit_inv (cont : Contents) (ha hq : BitVec 16) : Inv (witState cont ha hq) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (Mem.resetState).req ≠ (3 : BitVec 2)
    decide
  · intro c
    show (Core.State.rr (Vector.replicate 2
      (⟨false, false, 0, 0, 0, 0, 0⟩ : Core.State))[c.val]).toNat < 6
    simp
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro h
    simp [witState, resetState, Mem.resetState] at h

/-- The witness state is in an active (reset-released) cycle. -/
theorem wit_runRst (cont : Contents) (ha hq : BitVec 16) :
    runRst (witState cont ha hq) (⟨0, 0, true⟩ : Machine.PinIn) = true := by
  simp [runRst, witState]

/-! ## 3. The host map's `DBG` byte geometry

The host map is a concrete table; the facts here are its `DBG` row (a compiled
`decide` check), the register offsets (`0x00 DBG`, `0x01 MCTL`, `0x02 ECTL`,
`0x08/0x09 EMASK`, `0x12/0x13 RLV`) and the resulting address equalities. -/

/-- The `DBG` block's register map. -/
def dbgRegs : Array (Nat × String × Nat × String) :=
  #[(0x00, "DBG", 1, "RW"), (0x01, "MCTL", 1, "RW"), (0x02, "ECTL", 1, "RW"),
    (0x04, "MISR", 4, "R"), (0x08, "EMASK", 2, "RW"), (0x0A, "ACC", 1, "R"),
    (0x0B, "AFLG", 1, "R"), (0x0C, "FLAGS", 2, "R"), (0x0E, "CST", 2, "R"),
    (0x10, "FPC", 2, "R"), (0x12, "RLV", 2, "RW")]

theorem hostLocate_emask0 :
    (Machine.hostLocate 0x2468).map (fun l => (l.blk, l.inst, l.reg, l.byte)) =
      some ("DBG", 0, "EMASK", (0 : Nat)) := by decide

theorem hostLocate_emask1 :
    (Machine.hostLocate 0x2469).map (fun l => (l.blk, l.inst, l.reg, l.byte)) =
      some ("DBG", 0, "EMASK", (1 : Nat)) := by decide

theorem hostLocate_rlv0 :
    (Machine.hostLocate 0x2472).map (fun l => (l.blk, l.inst, l.reg, l.byte)) =
      some ("DBG", 0, "RLV", (0 : Nat)) := by decide

theorem hostLocate_rlv1 :
    (Machine.hostLocate 0x2473).map (fun l => (l.blk, l.inst, l.reg, l.byte)) =
      some ("DBG", 0, "RLV", (1 : Nat)) := by decide

/-- The block table's `DBG` row (compiled evaluation of the host map). -/
theorem hostBlocks_dbg :
    (Machine.Tables.hostBlocks.toList.all (fun b =>
      !(b.1 == "DBG") || b == ("DBG", 0x2460, 0x20, 1, dbgRegs))) = true := by decide

theorem dbgRegs_emask :
    (dbgRegs.toList.all (fun (ro, rn, bytes, _acc) =>
      !(rn == "EMASK") || (ro == 8 && bytes == 2))) = true := by decide

theorem dbgRegs_ectl :
    (dbgRegs.toList.all (fun (ro, rn, bytes, _acc) =>
      !(rn == "ECTL") || (ro == 2 && bytes == 1))) = true := by decide

theorem dbgRegs_mctl :
    (dbgRegs.toList.all (fun (ro, rn, bytes, _acc) =>
      !(rn == "MCTL") || (ro == 1 && bytes == 1))) = true := by decide

theorem dbgRegs_rlv :
    (dbgRegs.toList.all (fun (ro, rn, bytes, _acc) =>
      !(rn == "RLV") || (ro == 18 && bytes == 2))) = true := by decide

/-- A `DBG`-located address's offset within the block and its register lane. -/
theorem hostLocate_fields {a : Nat} {blk : String} {inst : Nat} {reg : String} {b : Nat}
    (hmap : (Machine.hostLocate a).map (fun l => (l.blk, l.inst, l.reg, l.byte))
      = some (blk, inst, reg, b)) :
    ∃ l : Machine.HostLoc, Machine.hostLocate a = some l ∧ l.blk = blk ∧ l.inst = inst ∧
      l.reg = reg ∧ l.byte = b := by
  obtain ⟨l, hl, hf⟩ := Option.map_eq_some_iff.mp hmap
  exact ⟨l, hl, by simpa using congrArg (·.1) hf, by simpa using congrArg (·.2.1) hf,
    by simpa using congrArg (·.2.2.1) hf, by simpa using congrArg (·.2.2.2) hf⟩

/-- A `DBG`-located address's offset within the block and its register lane. -/
theorem hostLocate_dbg_off (a : Nat) (l : Machine.HostLoc)
    (h : Machine.hostLocate a = some l) (hb : l.blk = "DBG") :
    ∃ ro rn bytes acc, (ro, rn, bytes, acc) ∈ dbgRegs.toList ∧ rn = l.reg ∧
      a = 0x2460 + ro + l.byte ∧ l.byte < bytes := by
  rw [hostLocate_eq] at h
  obtain ⟨ys, blk, zs, hpush, hfa, -⟩ := Array.findSome?_eq_some_iff.mp h
  obtain ⟨name, base, stride0, inst, regs⟩ := blk
  have hmem : (name, base, stride0, inst, regs) ∈ Machine.Tables.hostBlocks.toList := by
    have h' : (name, base, stride0, inst, regs) ∈
        (ys.push (name, base, stride0, inst, regs) ++ zs).toList := by simp
    rwa [← hpush] at h'
  have hbn : name = "DBG" := by
    have h' := hostLoc_blk a name base stride0 inst regs l hfa
    exact h'.symm.trans hb
  have hball := List.all_eq_true.mp hostBlocks_dbg (name, base, stride0, inst, regs) hmem
  rw [hbn] at hball
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq] at hball
  have heq : ("DBG", base, stride0, inst, regs) = ("DBG", 0x2460, 0x20, 1, dbgRegs) := hball
  have hbase : base = 0x2460 := congrArg (fun x => x.2.1) heq
  have hstride : stride0 = 0x20 := congrArg (fun x => x.2.2.1) heq
  have hinst : inst = 1 := congrArg (fun x => x.2.2.2.1) heq
  have hregs : regs = dbgRegs := congrArg (fun x => x.2.2.2.2) heq
  subst hbase
  subst hstride
  subst hinst
  subst hregs
  dsimp only at hfa
  have hstr : (if (0x20 == 0) = true then
      dbgRegs.foldl (fun m (o, _, n, _) => max m (o + n)) 0 else 0x20) = 0x20 := by decide
  rw [hstr] at hfa
  by_cases hc : (0x2460 ≤ a && a < 0x2460 + 0x20 * 1) = true
  · rw [if_pos hc] at hfa
    have hcs := hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcs
    obtain ⟨hle, hlt⟩ := hcs
    obtain ⟨ro, rn, bytes, acc, hrmem, hoffle, hofflt, hbyte, hreg⟩ :=
      findSome_byte dbgRegs name ((a - 0x2460) / 0x20) ((a - 0x2460) % 0x20) l hfa
    refine ⟨ro, rn, bytes, acc, hrmem, hreg.symm, ?_, ?_⟩
    · omega
    · omega
  · rw [if_neg hc] at hfa
    simp at hfa

/-- A `DBG.EMASK`-located address is byte 0 or 1 of `0x2468`. -/
theorem hostLocate_emask_off (a : Nat) (l : Machine.HostLoc)
    (h : Machine.hostLocate a = some l) (hb : l.blk = "DBG") (hr : l.reg = "EMASK") :
    a = 0x2468 + l.byte ∧ l.byte < 2 := by
  obtain ⟨ro, rn, bytes, acc, hmem, hrn, ha, hlt⟩ := hostLocate_dbg_off a l h hb
  have hchk := List.all_eq_true.mp dbgRegs_emask (ro, rn, bytes, acc) hmem
  rw [hrn, hr] at hchk
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    beq_iff_eq] at hchk
  obtain ⟨hro, hby⟩ := hchk
  subst hro
  subst hby
  exact ⟨by omega, by omega⟩

/-- A `DBG.RLV`-located address is byte 0 or 1 of `0x2472`. -/
theorem hostLocate_rlv_off (a : Nat) (l : Machine.HostLoc)
    (h : Machine.hostLocate a = some l) (hb : l.blk = "DBG") (hr : l.reg = "RLV") :
    a = 0x2472 + l.byte ∧ l.byte < 2 := by
  obtain ⟨ro, rn, bytes, acc, hmem, hrn, ha, hlt⟩ := hostLocate_dbg_off a l h hb
  have hchk := List.all_eq_true.mp dbgRegs_rlv (ro, rn, bytes, acc) hmem
  rw [hrn, hr] at hchk
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    beq_iff_eq] at hchk
  obtain ⟨hro, hby⟩ := hchk
  subst hro
  subst hby
  exact ⟨by omega, by omega⟩

/-- A `DBG.ECTL`-located address is `0x2462`. -/
theorem hostLocate_ectl_off (a : Nat) (l : Machine.HostLoc)
    (h : Machine.hostLocate a = some l) (hb : l.blk = "DBG") (hr : l.reg = "ECTL") :
    a = 0x2462 ∧ l.byte = 0 := by
  obtain ⟨ro, rn, bytes, acc, hmem, hrn, ha, hlt⟩ := hostLocate_dbg_off a l h hb
  have hchk := List.all_eq_true.mp dbgRegs_ectl (ro, rn, bytes, acc) hmem
  rw [hrn, hr] at hchk
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    beq_iff_eq] at hchk
  obtain ⟨hro, hby⟩ := hchk
  subst hro
  subst hby
  exact ⟨by omega, by omega⟩

/-- A `DBG.MCTL`-located address is `0x2461`. -/
theorem hostLocate_mctl_off (a : Nat) (l : Machine.HostLoc)
    (h : Machine.hostLocate a = some l) (hb : l.blk = "DBG") (hr : l.reg = "MCTL") :
    a = 0x2461 ∧ l.byte = 0 := by
  obtain ⟨ro, rn, bytes, acc, hmem, hrn, ha, hlt⟩ := hostLocate_dbg_off a l h hb
  have hchk := List.all_eq_true.mp dbgRegs_mctl (ro, rn, bytes, acc) hmem
  rw [hrn, hr] at hchk
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    beq_iff_eq] at hchk
  obtain ⟨hro, hby⟩ := hchk
  subst hro
  subst hby
  exact ⟨by omega, by omega⟩

/-! ## 4. Widening and window arithmetic -/

/-- Widening to 32 bits is injective on 16-bit words (a `Nat` value below
`2^16`). -/
theorem setWidth32_eq_ofNat {a : BitVec 16} {n : Nat} (hn : n < 65536)
    (h : BitVec.setWidth 32 a = BitVec.ofNat 32 n) : a = BitVec.ofNat 16 n := by
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h'
  have ha : a.toNat < 2 ^ 32 := by omega
  have hn' : n < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hn'] at h'
  apply BitVec.eq_of_toNat_eq
  rw [h', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- A host `DBG`-window byte strobe holds exactly for a write of that offset. -/
theorem hostDbg_eq {w : Bool} {a : BitVec 16} {D : Nat} (hD : D < 0x20) :
    Strobes.hostDbg w a D = true ↔ w = true ∧ a = BitVec.ofNat 16 D := by
  unfold Strobes.hostDbg
  rw [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hw, he⟩
    exact ⟨hw, setWidth32_eq_ofNat (by omega) he⟩
  · rintro ⟨hw, rfl⟩
    refine ⟨hw, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : D < 65536), Nat.mod_eq_of_lt (by omega : D < 2 ^ 32)]

/-- `dbgOff a`'s value. -/
theorem dbgOff_toNat (a : BitVec 16) : (dbgOff a).toNat = (a.toNat + 56224) % 65536 := by
  have h9312 : BitVec.toNat (9312 : BitVec 16) = 9312 := by decide
  have h316 : (2 : Nat) ^ 16 = 65536 := by decide
  unfold dbgOff
  rw [BitVec.toNat_sub, h9312, h316]
  show (65536 - 9312 + a.toNat) % 65536 = (a.toNat + 56224) % 65536
  congr 1
  omega

/-- `dbgOff a = D` pins the address (`D` inside the window). -/
theorem dbgOff_eq_addr {a : BitVec 16} {D : Nat} (hD : D < 0x20)
    (h : dbgOff a = BitVec.ofNat 16 D) : a = BitVec.ofNat 16 (0x2460 + D) := by
  have hh : (dbgOff a).toNat = D := by
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : D < 65536)]
  rw [dbgOff_toNat] at hh
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 0x2460 + D < 65536)]
  by_cases hge : (9312 : Nat) ≤ a.toNat
  · have hval : (a.toNat + 56224) % 65536 = a.toNat - 9312 := by
      rw [show a.toNat + 56224 = (a.toNat - 9312) + 65536 from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    omega
  · have hval : (a.toNat + 56224) % 65536 = a.toNat + 56224 := Nat.mod_eq_of_lt (by omega)
    omega

/-- The value of the RTL's 32-bit `cw_dbg_off`. -/
theorem cwDbgOff_toNat (a : BitVec 16) :
    (Strobes.cwDbgOff a).toNat = (a.toNat + (2 ^ 32 - 9312)) % 2 ^ 32 := by
  have h9312 : BitVec.toNat (BitVec.setWidth 32 (9312 : BitVec 16)) = 9312 := by decide
  have ha : BitVec.toNat (BitVec.setWidth 32 a) = a.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := a.isLt; omega)]
  unfold Strobes.cwDbgOff Strobes.haDbgBase
  rw [BitVec.toNat_sub, h9312, ha]
  show (2 ^ 32 - 9312 + a.toNat) % 2 ^ 32 = (a.toNat + (2 ^ 32 - 9312)) % 2 ^ 32
  congr 1
  omega

/-- The RTL's 32-bit `cw_dbg_off` equal to `D` (inside the window) pins the
queued address. -/
theorem cwDbgOff_eq_addr {a : BitVec 16} {D : Nat} (hD : D < 0x20)
    (h : (Strobes.cwDbgOff a == BitVec.ofNat 32 D) = true) : a.toNat = 0x2460 + D := by
  have he : Strobes.cwDbgOff a = BitVec.ofNat 32 D := beq_iff_eq.mp h
  have hh : (Strobes.cwDbgOff a).toNat = D := by
    rw [he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : D < 2 ^ 32)]
  rw [cwDbgOff_toNat] at hh
  by_cases hge : (9312 : Nat) ≤ a.toNat
  · have hval : (a.toNat + (2 ^ 32 - 9312)) % 2 ^ 32 = a.toNat - 9312 := by
      rw [show a.toNat + (2 ^ 32 - 9312) = (a.toNat - 9312) + 2 ^ 32 from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hval : (a.toNat + (2 ^ 32 - 9312)) % 2 ^ 32 = a.toNat + (2 ^ 32 - 9312) :=
      Nat.mod_eq_of_lt (by omega)
    omega

/-! ## 5. The drained core write -/

/-- No `DBG`-window address is a configuration address. -/
theorem isCfgAddr_false_of (a : Nat) (h : 0x21E0 ≤ a) :
    Machine.Config.isCfgAddr a = false := by
  rcases hc : Machine.Config.isCfgAddr a with _ | _
  · rfl
  · have hw := Bridge.CfgWrite.isCfgAddr_window a hc
    omega

/-- The machine's drained core write (`cwNext`'s runtime output) is the cut's
pending queue write (in the machine's own drain form). -/
private theorem machCw_eq_of_cw {s : State} {m : Machine.State}
    (hcw : CwRel m.cw s.cq s.arb) (hfrz : m.dbg.frz = s.freeze.frz) :
    machCw m = (if !s.freeze.frz && s.cq.pending &&
        !(s.cq.pending && Machine.Config.isCfgAddr s.cq.pendingAddr.toNat) &&
        Machine.cwRuntimeTarget s.cq.pendingAddr.toNat then
      some ⟨s.cq.pendingAddr.toNat, s.cq.pendingData.toNat,
        Machine.hostLocate s.cq.pendingAddr.toNat⟩ else none) := by
  unfold machCw
  dsimp only
  unfold Machine.cwNext
  dsimp only
  rw [show m.cw.cwv = s.cq.pending from hcw.cwv,
      show m.cw.cwqa = s.cq.pendingAddr from hcw.cwqa,
      show m.cw.cwqd = s.cq.pendingData from hcw.cwqd,
      show m.dbg.frz = s.freeze.frz from hfrz]

theorem machCw_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    machCw m = (if !s.freeze.frz && s.cq.pending &&
        !(s.cq.pending && Machine.Config.isCfgAddr s.cq.pendingAddr.toNat) &&
        Machine.cwRuntimeTarget s.cq.pendingAddr.toNat then
      some ⟨s.cq.pendingAddr.toNat, s.cq.pendingData.toNat,
        Machine.hostLocate s.cq.pendingAddr.toNat⟩ else none) :=
  machCw_eq_of_cw hrel.cw (DbgRel.frz_eq hrel.dbg)

/-- The witness state's drained core write. -/
theorem wit_cw (cont : Contents) (ha q : BitVec 16) (hq : q = 0x2468 ∨ q = 0x2472) :
    machCw (absChip (witState cont ha q)) =
      some ⟨q.toNat, 0x3C, Machine.hostLocate q.toNat⟩ := by
  have hic : Machine.Config.isCfgAddr (q.toNat) = false := isCfgAddr_false_of _ (by
    rcases hq with rfl | rfl <;> decide)
  have hrt : Machine.cwRuntimeTarget q.toNat = true := by
    rcases hq with rfl | rfl <;> decide
  have hcond : (!(witState cont ha q).freeze.frz &&
      (witState cont ha q).cq.pending &&
      !((witState cont ha q).cq.pending &&
        Machine.Config.isCfgAddr (witState cont ha q).cq.pendingAddr.toNat) &&
      Machine.cwRuntimeTarget (witState cont ha q).cq.pendingAddr.toNat) = true := by
    simp only [witState, witCq, resetState, CoreCtl.freezeReset, Bool.not_false, Bool.true_and]
    rw [hic, hrt]
    rfl
  rw [machCw_eq_of_cw (cwRel_abs (witState cont ha q).cq (witState cont ha q).arb) rfl, if_pos hcond]
  rfl

/-! ## 6. The witness state's byte strobes and host writes -/

theorem wit_cwDrain_q (cont : Contents) (ha : BitVec 16) (q : BitVec 16)
    (hic : Machine.Config.isCfgAddr q.toNat = false) :
    cwDrain (witState cont ha q) = true := by
  simp [cwDrain, witState, witCq, resetState, CoreCtl.freezeReset, hic]

theorem wit_cwDrain (cont : Contents) : cwDrain (witState cont 0x2469 0x2468) = true :=
  wit_cwDrain_q cont 0x2469 0x2468 (isCfgAddr_false_of _ (by decide))

theorem wit_hwAt_core_emask0 (cont : Contents) (ha : BitVec 16) :
    Machine.Util.hwAt (machCw (absChip (witState cont ha 0x2468))) "DBG" 0 "EMASK" =
      some (0, 0x3C) := by
  obtain ⟨l, hl, hb, hi, hr, hby⟩ := hostLocate_fields hostLocate_emask0
  have hl' : Machine.hostLocate ((0x2468 : BitVec 16).toNat) = some l := by simpa using hl
  rw [wit_cw cont ha 0x2468 (Or.inl rfl)]
  simp only [Machine.Util.hwAt, hl', hb, hi, hr, hby, Bool.and_self, if_true]
  decide

theorem wit_hwAt_core_rlv0 (cont : Contents) (ha : BitVec 16) :
    Machine.Util.hwAt (machCw (absChip (witState cont ha 0x2472))) "DBG" 0 "RLV" =
      some (0, 0x3C) := by
  obtain ⟨l, hl, hb, hi, hr, hby⟩ := hostLocate_fields hostLocate_rlv0
  have hl' : Machine.hostLocate ((0x2472 : BitVec 16).toNat) = some l := by simpa using hl
  rw [wit_cw cont ha 0x2472 (Or.inr rfl)]
  simp only [Machine.Util.hwAt, hl', hb, hi, hr, hby, Bool.and_self, if_true]
  decide

/-- `hostOpt2` when the low `EMASK` byte is host-selected and strobed. -/
theorem hostOpt2_em0 (i : Debug.Ctrl.Input) (p1 : Bridge.Debug.Port)
    (hst : i.dWrEm0 = true) (hh : i.hEm0 = true) :
    Bridge.Debug.hostOpt2 (Bridge.Debug.emaskPort0 i) p1 = some (0, i.hWd.toNat) := by
  unfold Bridge.Debug.hostOpt2 Bridge.Debug.emaskPort0
  rw [hst, hh]
  rfl

/-- A host-selected port is never core-selected. -/
theorem port_not_core (p : Bridge.Debug.Port) (h : p.host = true) :
    (p.strobe && !p.host) = false := by
  simp [h]

/-! ## 7. The one-byte host-only register `MCTL` -/

/-- **`DbgWire.hmctl`.**  The machine's host `MCTL` byte is the cut's located
`DBG.MCTL` write (one byte, host only; no address geometry is needed because
both sides read the same `hwAt` option). -/
theorem dbgHmctl (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    Machine.Util.hwByte (machHw m) "DBG" 0 "MCTL" =
      (if (dbgDigestIn s pin).dWrMctl then some (dbgDigestIn s pin).hWd.toNat else none) := by
  rw [machHw_eq_hwOf hrel hinv, hwByte_hwOf]
  rfl

/-! ## 8. The one-byte host-or-drain register `ECTL` -/

/-- `DBG.ECTL` byte 0 at `0x2462`. -/
theorem hostLocate_ectl :
    (Machine.hostLocate 0x2462).map (fun l => (l.blk, l.inst, l.reg, l.byte)) =
      some ("DBG", 0, "ECTL", (0 : Nat)) := by decide

/-- The exact `ECTL` location. -/
theorem hostLocate_ectl_fields {l : Machine.HostLoc}
    (h : Machine.hostLocate 0x2462 = some l) :
    l.blk = "DBG" ∧ l.inst = 0 ∧ l.reg = "ECTL" ∧ l.byte = 0 := by
  obtain ⟨l₀, hl₀, hb, hi, hr, hby⟩ := hostLocate_fields hostLocate_ectl
  have he : l = l₀ := Option.some.inj (h.symm.trans hl₀)
  subst he
  exact ⟨hb, hi, hr, hby⟩

/-- A host write of `DBG.ECTL` byte 0 is at `0x2462`. -/
theorem hostDbg_ectl_addr {s : State}
    (h : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEctl = true) :
    s.hostCmd.addr = 0x2462 := by
  have h' : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) 2 = true := by
    simpa [Strobes.hoDbgEctl] using h
  obtain ⟨-, hoff⟩ := (hostDbg_eq (D := 2) (by decide)).mp h'
  have h'' := dbgOff_eq_addr (D := 2) (by decide) hoff
  simpa using h''

/-- A located `DBG.ECTL` write needs the registered host byte. -/
theorem hwIsSome_ectl_wr {s : State} (h : hwIsSome s "DBG" 0 "ECTL" = true) :
    s.hostCmd.wr = true := by
  rcases hw : s.hostCmd.wr with _ | _
  · simp [hwIsSome, hwOf, hw, Machine.Util.hwAt] at h
  · rfl

/-- A located `DBG.ECTL` write is at `0x2462`. -/
theorem hwIsSome_ectl_addr {s : State} (h : hwIsSome s "DBG" 0 "ECTL" = true) :
    s.hostCmd.addr = 0x2462 := by
  have hwr := hwIsSome_ectl_wr h
  have hw : hwOf s = some ⟨s.hostCmd.addr.toNat, s.hostCmd.wdata.toNat,
      Machine.hostLocate s.hostCmd.addr.toNat⟩ := by
    unfold hwOf
    rw [if_pos hwr]
  unfold hwIsSome at h
  rw [hw] at h
  unfold Machine.Util.hwAt at h
  dsimp only at h
  cases hl : Machine.hostLocate s.hostCmd.addr.toNat with
  | none =>
    rw [hl] at h
    exact absurd h (by simp)
  | some l =>
    rw [hl] at h
    dsimp only at h
    cases hloc : (l.blk == "DBG" && l.inst == 0 && l.reg == "ECTL")
    · have hc : ¬((l.blk == "DBG" && l.inst == 0 && l.reg == "ECTL") = true) := by
        rw [hloc]
        decide
      rw [if_neg hc] at h
      exact absurd h (by simp)
    · have hf : (l.blk == "DBG" && l.inst == 0 && l.reg == "ECTL") = true := hloc
      simp only [Bool.and_eq_true, beq_iff_eq] at hf
      obtain ⟨⟨hb, -⟩, hr⟩ := hf
      obtain ⟨ha, -⟩ := hostLocate_ectl_off s.hostCmd.addr.toNat l hl hb hr
      have hnum : (0x2462 : BitVec 16).toNat = 9314 := by decide
      have htoNat : s.hostCmd.addr.toNat = (0x2462 : BitVec 16).toNat := by rw [ha, hnum]
      exact BitVec.eq_of_toNat_eq htoNat
/-- The `ECTL` host byte strobe is exactly the located `ECTL` write (§12.4:
the RTL's `h_ectl = w_dbg & (o_dbg == HO_DBG_ECTL)`). -/
theorem hwIsSome_ectl_eq (s : State) :
    hwIsSome s "DBG" 0 "ECTL" =
      Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEctl := by
  by_cases hh : hwIsSome s "DBG" 0 "ECTL" = true
  · have haddr := hwIsSome_ectl_addr hh
    have hwr := hwIsSome_ectl_wr hh
    have hd : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEctl = true := by
      have hoff : dbgOff s.hostCmd.addr = (2 : BitVec 16) := by rw [haddr]; decide
      have hin : inDbg s.hostCmd.addr = true := by
        simp [inDbg, hoff]
      have hset : (BitVec.setWidth 32 (dbgOff s.hostCmd.addr) == BitVec.ofNat 32 2) = true := by
        rw [hoff]
        decide
      simp only [Strobes.hostDbg, Strobes.hoDbgEctl, hwDbg, hwr, hin, hset, Bool.true_and]
    rw [hh, hd]
  · have hh' : hwIsSome s "DBG" 0 "ECTL" = false := by simpa using hh
    by_cases hd : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEctl = true
    · have haddr := hostDbg_ectl_addr hd
      have hdw : hwDbg s = true := by
        have h2 := (hostDbg_eq (D := 2) (by decide)).mp (by simpa [Strobes.hoDbgEctl] using hd)
        exact h2.1
      have hwr : s.hostCmd.wr = true := by
        have h3 : (s.hostCmd.wr && inDbg s.hostCmd.addr) = true := by simpa [hwDbg] using hdw
        rw [Bool.and_eq_true] at h3
        exact h3.1
      have hsome : hwIsSome s "DBG" 0 "ECTL" = true := by
        obtain ⟨l₀, hl₀, hb, hi, hr, hby⟩ := hostLocate_fields hostLocate_ectl
        have haddrn : s.hostCmd.addr.toNat = 9314 := by
          rw [haddr]
          decide
        have hloc : Machine.hostLocate s.hostCmd.addr.toNat = some l₀ := by
          rw [haddrn]
          exact hl₀
        simp [hwIsSome, hwOf, hwr, hloc, Machine.Util.hwAt, hb, hi, hr]
      rw [hh'] at hsome
      exact absurd hsome (by decide)
    · have hd' : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEctl =
          false := by simpa using hd
      rw [hh', hd']

/-- The target of a machine runtime drain is a `DBG` register byte. -/
theorem cwRuntimeTarget_loc {qa : Nat} (h : Machine.cwRuntimeTarget qa = true) :
    ∃ l : Machine.HostLoc, Machine.hostLocate qa = some l ∧ l.blk = "DBG" ∧
      (l.reg = "ECTL" ∨ l.reg = "EMASK" ∨ l.reg = "RLV") := by
  unfold Machine.cwRuntimeTarget at h
  cases hl : Machine.hostLocate qa with
  | none => simp [hl] at h
  | some l =>
    simp only [hl] at h
    have hb : l.blk = "DBG" := by
      have h2 := h
      rw [Bool.and_eq_true] at h2
      exact beq_iff_eq.mp h2.1
    refine ⟨l, rfl, hb, ?_⟩
    have h2 := h
    rw [Bool.and_eq_true] at h2
    have h3 := h2.2
    rw [Bool.or_eq_true] at h3
    rcases h3 with h4 | h4
    · rw [Bool.or_eq_true] at h4
      rcases h4 with h5 | h5
      · exact Or.inl (beq_iff_eq.mp h5)
      · exact Or.inr (Or.inl (beq_iff_eq.mp h5))
    · exact Or.inr (Or.inr (beq_iff_eq.mp h4))

/-- **The machine's drained `ECTL` byte.**  A drained core write reaches `ECTL`
exactly when the cut's `cw_drain` strobe targets its offset (§13.1). -/
theorem machCw_hwByte_ectl {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    Machine.Util.hwByte (machCw m) "DBG" 0 "ECTL" =
      (if cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
        BitVec.ofNat 32 Strobes.hoDbgEctl) then some s.cq.pendingData.toNat else none) := by
  rw [machCw_eq hrel]
  by_cases hD : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
      BitVec.ofNat 32 Strobes.hoDbgEctl)) = true
  · rw [if_pos hD]
    have hdD := hD
    rw [Bool.and_eq_true] at hdD
    obtain ⟨hdrain, hoff⟩ := hdD
    have hoff2 : (Strobes.cwDbgOff s.cq.pendingAddr ==
        BitVec.ofNat 32 2) = true := by simpa [Strobes.hoDbgEctl] using hoff
    have hqa : s.cq.pendingAddr.toNat = 0x2462 := cwDbgOff_eq_addr (D := 2) (by decide) hoff2
    have hd := hdrain
    rw [cwDrain] at hd
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hd
    obtain ⟨⟨hp, hf⟩, -⟩ := hd
    have hic : Machine.Config.isCfgAddr s.cq.pendingAddr.toNat = false := by
      rw [hqa]
      exact isCfgAddr_false_of _ (by decide)
    have hrt : Machine.cwRuntimeTarget s.cq.pendingAddr.toNat = true := by
      rw [hqa]
      decide
    have hC : (!s.freeze.frz && s.cq.pending &&
        !(s.cq.pending && Machine.Config.isCfgAddr s.cq.pendingAddr.toNat) &&
        Machine.cwRuntimeTarget s.cq.pendingAddr.toNat) = true := by
      rw [hf, hp, hic, hrt]
      rfl
    rw [if_pos hC]
    obtain ⟨l₀, hl₀, hb, hi, hr, hby⟩ := hostLocate_fields hostLocate_ectl
    have hloc : Machine.hostLocate s.cq.pendingAddr.toNat = some l₀ := by
      rw [hqa]
      exact hl₀
    simp only [Machine.Util.hwByte, Machine.Util.hwAt, hloc, hb, hi, hr]
    rfl
  · rw [if_neg hD]
    by_cases hC : (!s.freeze.frz && s.cq.pending &&
        !(s.cq.pending && Machine.Config.isCfgAddr s.cq.pendingAddr.toNat) &&
        Machine.cwRuntimeTarget s.cq.pendingAddr.toNat) = true
    · rw [if_pos hC]
      have hC' := hC
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hC'
      obtain ⟨⟨⟨hf, hp⟩, hni⟩, -⟩ := hC'
      obtain ⟨l, hl, hblk, -⟩ := cwRuntimeTarget_loc (by
        have h2 := hC
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h2
        exact h2.2)
      have hic : Machine.Config.isCfgAddr s.cq.pendingAddr.toNat = false := by
        rcases hc0 : Machine.Config.isCfgAddr s.cq.pendingAddr.toNat with _ | _
        · rfl
        · rw [hp, hc0] at hni
          exact absurd hni (by decide)
      have hdrain : cwDrain s = true := by
        unfold cwDrain
        rw [hp, hf, hic]
        simp
      have hres : (l.blk == "DBG" && l.inst == 0 && l.reg == "ECTL") = false := by
        rw [hblk]
        simp only [beq_self_eq_true, Bool.true_and]
        cases hi : l.inst
        · have hr : l.reg ≠ "ECTL" := by
            intro hre
            exfalso
            apply hD
            rw [hdrain]
            have hoff2 : (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 2) = true := by
              obtain ⟨ha, -⟩ := hostLocate_ectl_off s.cq.pendingAddr.toNat l hl hblk hre
              have hqa : s.cq.pendingAddr = 0x2462 := by
                apply BitVec.eq_of_toNat_eq
                rw [ha]
                decide
              rw [hqa]
              decide
            rw [show Strobes.hoDbgEctl = 2 from rfl]
            rw [hoff2]
            rfl
          simp [hr]
        · simp
      simp only [Machine.Util.hwByte, Machine.Util.hwAt, hl, hres]
      rfl
    · rw [if_neg hC]
      rfl

/-- **`DbgWire.hectl`.**  The machine's host-then-drain `ECTL` byte is the cut's
single-byte port with host priority (§12.4/§13.1; `ECTL` is one byte, so no
byte collision exists and the equality holds unconditionally). -/
theorem dbgHectl (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    Bridge.Debug.pickByte (machHw m) (machCw m) "ECTL" =
      (Bridge.Debug.Port.mk (dbgCtrlIn s pin).dWrEctl (dbgCtrlIn s pin).hEctl
        (dbgCtrlIn s pin).hWd (dbgCtrlIn s pin).cwData).ok := by
  have hhost : Machine.Util.hwByte (machHw m) "DBG" 0 "ECTL" =
      (if hwIsSome s "DBG" 0 "ECTL" then some (hwData s).toNat else none) := by
    rw [machHw_eq_hwOf hrel hinv, hwByte_hwOf]
    rfl
  have hcore := machCw_hwByte_ectl hrel
  have heq := hwIsSome_ectl_eq s
  change Bridge.Debug.pickByte (machHw m) (machCw m) "ECTL" =
    (Bridge.Debug.Port.mk
      (Strobes.dbgByteWrite (hwDbg s) (dbgOff s.hostCmd.addr) (cwDrain s)
        s.cq.pendingAddr Strobes.hoDbgEctl)
      (hwIsSome s "DBG" 0 "ECTL") (hwData s) (s.cq.pendingData)).ok
  unfold Bridge.Debug.pickByte
  rw [hhost, hcore]
  unfold Bridge.Debug.Port.ok
  rw [heq]
  by_cases hb : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEctl = true
  · rw [hb]
    have hdbg : Strobes.dbgByteWrite (hwDbg s) (dbgOff s.hostCmd.addr) (cwDrain s)
        s.cq.pendingAddr Strobes.hoDbgEctl = true := by
      unfold Strobes.dbgByteWrite
      simp only [hb, Bool.true_or]
    rw [hdbg]
    simp
  · have hb' : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEctl =
        false := by simpa using hb
    rw [hb']
    by_cases hd : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
        BitVec.ofNat 32 Strobes.hoDbgEctl)) = true
    · have hdbg : Strobes.dbgByteWrite (hwDbg s) (dbgOff s.hostCmd.addr) (cwDrain s)
          s.cq.pendingAddr Strobes.hoDbgEctl = true := by
        unfold Strobes.dbgByteWrite
        simp only [hb', Bool.false_or]
        exact hd
      rw [hdbg, hd]
      simp
    · have hd' : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
          BitVec.ofNat 32 Strobes.hoDbgEctl)) = false := by
        cases hx : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
          BitVec.ofNat 32 Strobes.hoDbgEctl))
        · rfl
        · exact absurd hx hd
      have hdbg : Strobes.dbgByteWrite (hwDbg s) (dbgOff s.hostCmd.addr) (cwDrain s)
          s.cq.pendingAddr Strobes.hoDbgEctl = false := by
        unfold Strobes.dbgByteWrite
        simp only [hb', Bool.false_or]
        exact hd'
      rw [hdbg, hd']
      simp

/-! ## 9. The two remaining false leaves (cause 2 only)

After the `Wire.dbgCtrlIn` fix (byte-precise `hEm0`/`hRlv0`, matching
`project.v:662/664`) `dbgHEH`, `dbgHESH`, `dbgHRH`, `dbgHRSH` hold
(§10).  `dbgHEC` and `dbgHRC` still fail, now *only* because of cause 2: a
host write and a drained core write of the **same** register byte in one
cycle.  The machine holds two `Option HostWr`s, the cut one combined per-byte
strobe with a host-select bit; in that cycle `coreOpt2` reports no core byte
although the machine's drained write exists (§13.1: the core write applies
before the host write).  The witnesses use `ha = hq` (`EMASK` byte 0 / `RLV`
byte 0 for both sources). -/

/-- The host write of `EMASK` byte 0 on the same-byte witness. -/
theorem wit_hwAt_host_emask0 (cont : Contents) :
    Machine.Util.hwAt (hwOf (witState cont 0x2468 0x2468)) "DBG" 0 "EMASK" = some (0, 0x5A) := by
  obtain ⟨l, hl, hb, hi, hr, hby⟩ := hostLocate_fields hostLocate_emask0
  have hl' : Machine.hostLocate ((0x2468 : BitVec 16).toNat) = some l := by simpa using hl
  simp only [hwOf, witState, witHostCmd, if_pos, hl', Machine.Util.hwAt, hb, hi, hr, hby,
    Bool.and_self, if_true]
  decide

/-- The host write of `RLV` byte 0 on the same-byte witness. -/
theorem wit_hwAt_host_rlv0 (cont : Contents) :
    Machine.Util.hwAt (hwOf (witState cont 0x2472 0x2472)) "DBG" 0 "RLV" = some (0, 0x5A) := by
  obtain ⟨l, hl, hb, hi, hr, hby⟩ := hostLocate_fields hostLocate_rlv0
  have hl' : Machine.hostLocate ((0x2472 : BitVec 16).toNat) = some l := by simpa using hl
  simp only [hwOf, witState, witHostCmd, if_pos, hl', Machine.Util.hwAt, hb, hi, hr, hby,
    Bool.and_self, if_true]
  decide

/-- A `DBG` byte strobe is down when its host and drain terms are down. -/
theorem dbgByteWrite_false {s : State} {off : Nat}
    (hhost : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) off = false)
    (hdrain : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
      BitVec.ofNat 32 off)) = false) :
    Strobes.dbgByteWrite (hwDbg s) (dbgOff s.hostCmd.addr) (cwDrain s) s.cq.pendingAddr off =
      false := by
  unfold Strobes.dbgByteWrite
  rw [hhost, hdrain]
  rfl

/-- No host write of `EMASK` byte 1 on the same-byte witness. -/
theorem wit_hostDbg_emask9_false (cont : Contents) :
    Strobes.hostDbg (hwDbg (witState cont 0x2468 0x2468))
      (dbgOff (witState cont 0x2468 0x2468).hostCmd.addr) Strobes.hoDbgEmaskPlus1 = false := by
  have ha : (witState cont 0x2468 0x2468).hostCmd.addr = 0x2468 := rfl
  by_cases h : Strobes.hostDbg (hwDbg (witState cont 0x2468 0x2468))
      (dbgOff (witState cont 0x2468 0x2468).hostCmd.addr) Strobes.hoDbgEmaskPlus1 = true
  · have h' : Strobes.hostDbg (hwDbg (witState cont 0x2468 0x2468))
        (dbgOff (witState cont 0x2468 0x2468).hostCmd.addr) 9 = true := by
      simpa [Strobes.hoDbgEmaskPlus1] using h
    obtain ⟨-, hoff⟩ := (hostDbg_eq (D := 9) (by decide)).mp h'
    have haddr := dbgOff_eq_addr (D := 9) (by decide) hoff
    rw [ha] at haddr
    exact absurd haddr (by decide)
  · simpa using h

/-- No drained write of `EMASK` byte 1 on the same-byte witness. -/
theorem wit_cwOff9_false (cont : Contents) :
    (cwDrain (witState cont 0x2468 0x2468) &&
      (Strobes.cwDbgOff (witState cont 0x2468 0x2468).cq.pendingAddr ==
        BitVec.ofNat 32 9)) = false := by
  have hp : (witState cont 0x2468 0x2468).cq.pendingAddr = (0x2468 : BitVec 16) := rfl
  have hoff : (Strobes.cwDbgOff (0x2468 : BitVec 16) == BitVec.ofNat 32 9) = false := by decide
  rw [hp, hoff, Bool.and_false]

/-- No host write of `RLV` byte 1 on the same-byte witness. -/
theorem wit_hostDbg_rlv19_false (cont : Contents) :
    Strobes.hostDbg (hwDbg (witState cont 0x2472 0x2472))
      (dbgOff (witState cont 0x2472 0x2472).hostCmd.addr) Strobes.hoDbgRlvPlus1 = false := by
  have ha : (witState cont 0x2472 0x2472).hostCmd.addr = 0x2472 := rfl
  by_cases h : Strobes.hostDbg (hwDbg (witState cont 0x2472 0x2472))
      (dbgOff (witState cont 0x2472 0x2472).hostCmd.addr) Strobes.hoDbgRlvPlus1 = true
  · have h' : Strobes.hostDbg (hwDbg (witState cont 0x2472 0x2472))
        (dbgOff (witState cont 0x2472 0x2472).hostCmd.addr) 19 = true := by
      simpa [Strobes.hoDbgRlvPlus1] using h
    obtain ⟨-, hoff⟩ := (hostDbg_eq (D := 19) (by decide)).mp h'
    have haddr := dbgOff_eq_addr (D := 19) (by decide) hoff
    rw [ha] at haddr
    exact absurd haddr (by decide)
  · simpa using h

/-- No drained write of `RLV` byte 1 on the same-byte witness. -/
theorem wit_cwOff19_false (cont : Contents) :
    (cwDrain (witState cont 0x2472 0x2472) &&
      (Strobes.cwDbgOff (witState cont 0x2472 0x2472).cq.pendingAddr ==
        BitVec.ofNat 32 19)) = false := by
  have hp : (witState cont 0x2472 0x2472).cq.pendingAddr = (0x2472 : BitVec 16) := rfl
  have hoff : (Strobes.cwDbgOff (0x2472 : BitVec 16) == BitVec.ofNat 32 19) = false := by decide
  rw [hp, hoff, Bool.and_false]

/-- The cut's byte-1 `EMASK` strobe is down on the same-byte witness (no host
byte 1, no drain of byte 1). -/
theorem wit_dWrEm1_false (cont : Contents) :
    Strobes.dbgByteWrite (hwDbg (witState cont 0x2468 0x2468))
      (dbgOff (witState cont 0x2468 0x2468).hostCmd.addr)
      (cwDrain (witState cont 0x2468 0x2468))
      (witState cont 0x2468 0x2468).cq.pendingAddr Strobes.hoDbgEmaskPlus1 = false := by
  have h := dbgByteWrite_false (s := witState cont 0x2468 0x2468)
    (off := Strobes.hoDbgEmaskPlus1) (wit_hostDbg_emask9_false cont) (wit_cwOff9_false cont)
  exact h

/-- The cut's byte-1 `RLV` strobe is down on the same-byte witness. -/
theorem wit_dWrRlv1_false (cont : Contents) :
    Strobes.dbgByteWrite (hwDbg (witState cont 0x2472 0x2472))
      (dbgOff (witState cont 0x2472 0x2472).hostCmd.addr)
      (cwDrain (witState cont 0x2472 0x2472))
      (witState cont 0x2472 0x2472).cq.pendingAddr Strobes.hoDbgRlvPlus1 = false := by
  have h := dbgByteWrite_false (s := witState cont 0x2472 0x2472)
    (off := Strobes.hoDbgRlvPlus1) (wit_hostDbg_rlv19_false cont) (wit_cwOff19_false cont)
  exact h

/-- The byte-precise low `EMASK` host strobe is up on the same-byte witness. -/
theorem wit_strobe_emask0 (cont : Contents) :
    byteStrobe (Machine.Util.hwAt (hwOf (witState cont 0x2468 0x2468)) "DBG" 0 "EMASK") 0 =
      true := by
  unfold byteStrobe
  rw [wit_hwAt_host_emask0 cont]
  rfl

/-- The byte-precise low `RLV` host strobe is up on the same-byte witness. -/
theorem wit_strobe_rlv0 (cont : Contents) :
    byteStrobe (Machine.Util.hwAt (hwOf (witState cont 0x2472 0x2472)) "DBG" 0 "RLV") 0 =
      true := by
  unfold byteStrobe
  rw [wit_hwAt_host_rlv0 cont]
  rfl

/-- `coreOpt2` is `none` when the low byte is host-selected and the high byte is
neither host-selected nor strobed. -/
theorem coreOpt2_none_low (p0 p1 : Bridge.Debug.Port) (h0 : p0.host = true)
    (h1 : (p1.strobe && !p1.host) = false) :
    Bridge.Debug.coreOpt2 p0 p1 = none := by
  unfold Bridge.Debug.coreOpt2
  rw [port_not_core p0 h0, h1]
  rfl

/-- The `EMASK`/`RLV` byte ports as their literal records (projection forms). -/
theorem emaskPort0_eq (i : Debug.Ctrl.Input) :
    Bridge.Debug.emaskPort0 i = ⟨i.dWrEm0, i.hEm0, i.hWd, i.cwData⟩ := rfl

theorem emaskPort1_eq (i : Debug.Ctrl.Input) :
    Bridge.Debug.emaskPort1 i = ⟨i.dWrEm1, i.hEm1, i.hWd, i.cwData⟩ := rfl

theorem rlvPort0_eq (i : Debug.Ctrl.Input) :
    Bridge.Debug.rlvPort0 i = ⟨i.dWrRlv0, i.hRlv0, i.hWd, i.cwData⟩ := rfl

theorem rlvPort1_eq (i : Debug.Ctrl.Input) :
    Bridge.Debug.rlvPort1 i = ⟨i.dWrRlv1, i.hRlv1, i.hWd, i.cwData⟩ := rfl

/-- `coreOpt2` is `none` when the low `EMASK` byte is host-selected and the
high byte is not strobed (generic in the state). -/
theorem coreOpt2_emask_none_of_strobes (s : State) (pin : Machine.PinIn)
    (h0 : (dbgCtrlIn s pin).hEm0 = true) (hd1 : (dbgCtrlIn s pin).dWrEm1 = false) :
    Bridge.Debug.coreOpt2 (Bridge.Debug.emaskPort0 (dbgCtrlIn s pin))
      (Bridge.Debug.emaskPort1 (dbgCtrlIn s pin)) = none := by
  rw [emaskPort0_eq, emaskPort1_eq]
  unfold Bridge.Debug.coreOpt2
  dsimp only
  rw [h0, hd1]
  simp

/-- `coreOpt2` is `none` when the low `RLV` byte is host-selected and the high
byte is not strobed (generic in the state). -/
theorem coreOpt2_rlv_none_of_strobes (s : State) (pin : Machine.PinIn)
    (h0 : (dbgCtrlIn s pin).hRlv0 = true) (hd1 : (dbgCtrlIn s pin).dWrRlv1 = false) :
    Bridge.Debug.coreOpt2 (Bridge.Debug.rlvPort0 (dbgCtrlIn s pin))
      (Bridge.Debug.rlvPort1 (dbgCtrlIn s pin)) = none := by
  rw [rlvPort0_eq, rlvPort1_eq]
  unfold Bridge.Debug.coreOpt2
  dsimp only
  rw [h0, hd1]
  simp

/-- `coreOpt2` reports no core byte on the same-byte `EMASK` witness. -/
theorem wit_coreOpt2_emask_coll (cont : Contents) (pin : Machine.PinIn) :
    Bridge.Debug.coreOpt2 (Bridge.Debug.emaskPort0 (dbgCtrlIn (witState cont 0x2468 0x2468) pin))
      (Bridge.Debug.emaskPort1 (dbgCtrlIn (witState cont 0x2468 0x2468) pin)) = none := by
  refine coreOpt2_emask_none_of_strobes (witState cont 0x2468 0x2468) pin ?_ ?_
  · have h := wit_strobe_emask0 cont
    simpa only [dbgCtrlIn] using h
  · have h := wit_dWrEm1_false cont
    simpa only [dbgCtrlIn] using h

/-- `coreOpt2` reports no core byte on the same-byte `RLV` witness. -/
theorem wit_coreOpt2_rlv_coll (cont : Contents) (pin : Machine.PinIn) :
    Bridge.Debug.coreOpt2 (Bridge.Debug.rlvPort0 (dbgCtrlIn (witState cont 0x2472 0x2472) pin))
      (Bridge.Debug.rlvPort1 (dbgCtrlIn (witState cont 0x2472 0x2472) pin)) = none := by
  refine coreOpt2_rlv_none_of_strobes (witState cont 0x2472 0x2472) pin ?_ ?_
  · have h := wit_strobe_rlv0 cont
    simpa only [dbgCtrlIn] using h
  · have h := wit_dWrRlv1_false cont
    simpa only [dbgCtrlIn] using h

/-- `dbgHEC` is false: a host write and a drained core write of `EMASK` byte 0
in one cycle (cause 2 only; the byte-precise host strobes are in place). -/
theorem dbgHEC_false :
    ∃ (s : State) (m : Machine.State) (pin : Machine.PinIn),
      ChipRel s m ∧ Inv s ∧ runRst s pin = true ∧
      Machine.Util.hwAt (machCw m) "DBG" 0 "EMASK" ≠
        Bridge.Debug.coreOpt2 (Bridge.Debug.emaskPort0 (dbgCtrlIn s pin))
          (Bridge.Debug.emaskPort1 (dbgCtrlIn s pin)) := by
  refine ⟨witState Contents.init 0x2468 0x2468,
    absChip (witState Contents.init 0x2468 0x2468), ⟨0, 0, true⟩,
    wit_chipRel _ _ _ BankWire.maskedZero_zero, wit_inv _ _ _, wit_runRst _ _ _, ?_⟩
  rw [wit_hwAt_core_emask0 Contents.init 0x2468, wit_coreOpt2_emask_coll]
  decide

/-- `dbgHRC` is false on the same-byte `RLV` witness. -/
theorem dbgHRC_false :
    ∃ (s : State) (m : Machine.State) (pin : Machine.PinIn),
      ChipRel s m ∧ Inv s ∧ runRst s pin = true ∧
      Machine.Util.hwAt (machCw m) "DBG" 0 "RLV" ≠
        Bridge.Debug.coreOpt2 (Bridge.Debug.rlvPort0 (dbgCtrlIn s pin))
          (Bridge.Debug.rlvPort1 (dbgCtrlIn s pin)) := by
  refine ⟨witState Contents.init 0x2472 0x2472,
    absChip (witState Contents.init 0x2472 0x2472), ⟨0, 0, true⟩,
    wit_chipRel _ _ _ BankWire.maskedZero_zero, wit_inv _ _ _, wit_runRst _ _ _, ?_⟩
  rw [wit_hwAt_core_rlv0 Contents.init 0x2472, wit_coreOpt2_rlv_coll]
  decide

/-! ## 10. The four host/exclusivity leaves under the fixed wiring

With byte-precise `hEm0`/`hRlv0` (`Wire.lean` after the fix) a host write's
own byte strobe is exactly the located byte, so `hostOpt2` selects the host
byte the machine's `hwAt` reports, and one host write cannot set both bytes. -/

/-- The window offset of the window base plus a byte offset. -/
theorem dbgOff_ofNat_base (D : Nat) (hD : D < 0x20) :
    dbgOff (BitVec.ofNat 16 (0x2460 + D)) = BitVec.ofNat 16 D := by
  have hoff : (BitVec.ofNat 16 (0x2460 + D)).toNat = 0x2460 + D := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hD' : (BitVec.ofNat 16 D).toNat = D := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [dbgOff_toNat, hoff, hD']
  rw [show 0x2460 + D + 56224 = D + 65536 from by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- A host `DBG` byte strobe needs the host write. -/
theorem hwDbg_wr {s : State} (h : hwDbg s = true) : s.hostCmd.wr = true := by
  have h' := h
  unfold hwDbg at h'
  rw [Bool.and_eq_true] at h'
  exact h'.1

/-- A located host byte strobe needs the host write. -/
theorem hwAt_some_wr {s : State} {r : String} {j v : Nat}
    (h : Machine.Util.hwAt (hwOf s) "DBG" 0 r = some (j, v)) : s.hostCmd.wr = true := by
  rcases hw : s.hostCmd.wr with _ | _
  · simp [hwOf, hw, Machine.Util.hwAt] at h
  · rfl

/-- `inDbg` of the window base plus an in-window offset. -/
theorem inDbg_ofNat (off : Nat) (h : off < 0x20) :
    inDbg (BitVec.ofNat 16 (0x2460 + off)) = true := by
  unfold inDbg
  rw [dbgOff_ofNat_base off h]
  show decide ((BitVec.ofNat 16 off).toNat < 0x20) = true
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off < 2 ^ 16), decide_eq_true_eq]
  exact h

/-- Widening a 16-bit offset to 32 bits keeps it. -/
theorem setWidth_ofNat_self (off : Nat) (h : off < 65536) :
    (BitVec.setWidth 32 (BitVec.ofNat 16 off) == BitVec.ofNat 32 off) = true := by
  rw [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : off < 2 ^ 16), Nat.mod_eq_of_lt (by omega : off < 2 ^ 32)]

/-- **Byte strobe to host strobe.**  A located byte `b` of register `r` is a
host write of the byte's window offset. -/
theorem hostDbg_of_byteStrobe {s : State} {r : String} {off b : Nat} (hoff : off < 0x20)
    (hgeo : ∀ (l : Machine.HostLoc), Machine.hostLocate s.hostCmd.addr.toNat = some l →
      l.blk = "DBG" → l.reg = r → l.byte = b → s.hostCmd.addr.toNat = 0x2460 + off)
    (h : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 r) b = true) :
    Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) off = true := by
  unfold byteStrobe at h
  cases ho : Machine.Util.hwAt (hwOf s) "DBG" 0 r with
  | none => simp [ho] at h
  | some p =>
    obtain ⟨j, v⟩ := p
    have hj : j = b := by simpa [ho] using h
    obtain ⟨w, l, hw, hl, hbyte, hv, hblk, hinst, hreg⟩ := hwAt_some_facts ho
    have hwr : s.hostCmd.wr = true := hwAt_some_wr ho
    have hloc : Machine.hostLocate s.hostCmd.addr.toNat = some l := by
      unfold hwOf at hw
      rw [if_pos hwr] at hw
      injection hw with hwe
      rw [← hwe] at hl
      simpa using hl
    have hby : l.byte = b := by rw [hbyte, hj]
    have haddrn : s.hostCmd.addr.toNat = 0x2460 + off := hgeo l hloc hblk hreg hby
    have haddr : s.hostCmd.addr = BitVec.ofNat 16 (0x2460 + off) := by
      apply BitVec.eq_of_toNat_eq
      rw [haddrn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hdoff : dbgOff s.hostCmd.addr = BitVec.ofNat 16 off := by
      rw [haddr]
      exact dbgOff_ofNat_base off hoff
    have hin : inDbg s.hostCmd.addr = true := by
      rw [haddr]
      exact inDbg_ofNat off hoff
    have hwr' : hwDbg s = true := by
      unfold hwDbg
      rw [hwr, hin]
      rfl
    have hset : (BitVec.setWidth 32 (dbgOff s.hostCmd.addr) == BitVec.ofNat 32 off) = true := by
      rw [hdoff]
      exact setWidth_ofNat_self off (by omega)
    unfold Strobes.hostDbg
    rw [hwr', hset, Bool.true_and]

/-- **Host strobe to byte strobe.**  A host write of byte offset `off` of
register `r` is a located byte `b` of that register. -/
theorem byteStrobe_of_hostDbg {s : State} {r : String} {off b : Nat} (hofflt : off < 0x20)
    (hmap : (Machine.hostLocate (0x2460 + off)).map (fun l => (l.blk, l.inst, l.reg, l.byte))
      = some ("DBG", 0, r, b))
    (h : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) off = true) :
    byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 r) b = true := by
  obtain ⟨hwd, hoff⟩ := (hostDbg_eq (D := off) hofflt).mp h
  have hwr : s.hostCmd.wr = true := hwDbg_wr hwd
  obtain ⟨l, hl, hb, hi, hr, hby⟩ := hostLocate_fields hmap
  have haddr : s.hostCmd.addr = BitVec.ofNat 16 (0x2460 + off) := by
    have h' := dbgOff_eq_addr (D := off) hofflt hoff
    simpa using h'
  have haddrn : s.hostCmd.addr.toNat = 0x2460 + off := by
    rw [haddr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hloc : Machine.hostLocate s.hostCmd.addr.toNat = some l := by
    rw [haddrn]
    exact hl
  have ho : Machine.Util.hwAt (hwOf s) "DBG" 0 r = some (b, s.hostCmd.wdata.toNat) := by
    simp only [hwOf, hwr, if_pos, hloc, Machine.Util.hwAt, hb, hi, hr, hby, Bool.and_self,
      if_true]
    simp [beq_self_eq_true]
  unfold byteStrobe
  rw [ho]
  exact beq_self_eq_true b

/-- A host write of `EMASK` byte 0 is at `0x2468`. -/
theorem hostDbg_emask0_addr {s : State}
    (h : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmask = true) :
    s.hostCmd.addr = 0x2468 := by
  have h' : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) 8 = true := by
    simpa [Strobes.hoDbgEmask] using h
  obtain ⟨-, hoff⟩ := (hostDbg_eq (D := 8) (by decide)).mp h'
  simpa using dbgOff_eq_addr (D := 8) (by decide) hoff

/-- A host write of `EMASK` byte 1 is at `0x2469`. -/
theorem hostDbg_emask1_addr {s : State}
    (h : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmaskPlus1 = true) :
    s.hostCmd.addr = 0x2469 := by
  have h' : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) 9 = true := by
    simpa [Strobes.hoDbgEmaskPlus1] using h
  obtain ⟨-, hoff⟩ := (hostDbg_eq (D := 9) (by decide)).mp h'
  simpa using dbgOff_eq_addr (D := 9) (by decide) hoff

/-- A host write of `RLV` byte 0 is at `0x2472`. -/
theorem hostDbg_rlv0_addr {s : State}
    (h : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlv = true) :
    s.hostCmd.addr = 0x2472 := by
  have h' : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) 18 = true := by
    simpa [Strobes.hoDbgRlv] using h
  obtain ⟨-, hoff⟩ := (hostDbg_eq (D := 18) (by decide)).mp h'
  simpa using dbgOff_eq_addr (D := 18) (by decide) hoff

/-- A host write of `RLV` byte 1 is at `0x2473`. -/
theorem hostDbg_rlv1_addr {s : State}
    (h : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlvPlus1 = true) :
    s.hostCmd.addr = 0x2473 := by
  have h' : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) 19 = true := by
    simpa [Strobes.hoDbgRlvPlus1] using h
  obtain ⟨-, hoff⟩ := (hostDbg_eq (D := 19) (by decide)).mp h'
  simpa using dbgOff_eq_addr (D := 19) (by decide) hoff

/-- The byte-precise `EMASK` byte-0 host strobe is the offset-8 host write. -/
theorem hostByteStrobe_emask0 (s : State) :
    byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 0 =
      Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmask := by
  by_cases hb : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 0 = true
  · have himp := hostDbg_of_byteStrobe (s := s) (r := "EMASK") (off := 8) (b := 0) (by decide)
      (fun l hl hblk hreg hby => by
        obtain ⟨ha, -⟩ := hostLocate_emask_off s.hostCmd.addr.toNat l hl hblk hreg
        rw [hby] at ha
        omega)
      hb
    rw [hb, himp]
  · have hb' : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 0 = false := by
      simpa using hb
    rw [hb']
    by_cases hd : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmask = true
    · exact absurd (byteStrobe_of_hostDbg (s := s) (r := "EMASK") (off := 8) (b := 0)
        (by decide) hostLocate_emask0 hd) hb
    · simpa using hd

/-- The byte-precise `EMASK` byte-1 host strobe is the offset-9 host write. -/
theorem hostByteStrobe_emask1 (s : State) :
    byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 1 =
      Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmaskPlus1 := by
  by_cases hb : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 1 = true
  · have himp := hostDbg_of_byteStrobe (s := s) (r := "EMASK") (off := 9) (b := 1) (by decide)
      (fun l hl hblk hreg hby => by
        obtain ⟨ha, -⟩ := hostLocate_emask_off s.hostCmd.addr.toNat l hl hblk hreg
        rw [hby] at ha
        omega)
      hb
    rw [hb, himp]
  · have hb' : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 1 = false := by
      simpa using hb
    rw [hb']
    by_cases hd : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmaskPlus1 =
        true
    · exact absurd (byteStrobe_of_hostDbg (s := s) (r := "EMASK") (off := 9) (b := 1)
        (by decide) hostLocate_emask1 hd) hb
    · simpa using hd

/-- The byte-precise `RLV` byte-0 host strobe is the offset-18 host write. -/
theorem hostByteStrobe_rlv0 (s : State) :
    byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0 =
      Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlv := by
  by_cases hb : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0 = true
  · have himp := hostDbg_of_byteStrobe (s := s) (r := "RLV") (off := 18) (b := 0) (by decide)
      (fun l hl hblk hreg hby => by
        obtain ⟨ha, -⟩ := hostLocate_rlv_off s.hostCmd.addr.toNat l hl hblk hreg
        rw [hby] at ha
        omega)
      hb
    rw [hb, himp]
  · have hb' : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0 = false := by
      simpa using hb
    rw [hb']
    by_cases hd : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlv = true
    · exact absurd (byteStrobe_of_hostDbg (s := s) (r := "RLV") (off := 18) (b := 0)
        (by decide) hostLocate_rlv0 hd) hb
    · simpa using hd

/-- The byte-precise `RLV` byte-1 host strobe is the offset-19 host write. -/
theorem hostByteStrobe_rlv1 (s : State) :
    byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1 =
      Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlvPlus1 := by
  by_cases hb : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1 = true
  · have himp := hostDbg_of_byteStrobe (s := s) (r := "RLV") (off := 19) (b := 1) (by decide)
      (fun l hl hblk hreg hby => by
        obtain ⟨ha, -⟩ := hostLocate_rlv_off s.hostCmd.addr.toNat l hl hblk hreg
        rw [hby] at ha
        omega)
      hb
    rw [hb, himp]
  · have hb' : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1 = false := by
      simpa using hb
    rw [hb']
    by_cases hd : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlvPlus1 =
        true
    · exact absurd (byteStrobe_of_hostDbg (s := s) (r := "RLV") (off := 19) (b := 1)
        (by decide) hostLocate_rlv1 hd) hb
    · simpa using hd

/-- Decoding a host write to one of a two-byte register's byte lanes. -/
theorem hwAt_two_lane {o : Option Machine.HostWr} {r : String} {v : Nat}
    (h : ∀ j w, Machine.Util.hwAt o "DBG" 0 r = some (j, w) → j < 2 ∧ w = v) :
    Machine.Util.hwAt o "DBG" 0 r =
      (if byteStrobe (Machine.Util.hwAt o "DBG" 0 r) 0 then some (0, v)
       else if byteStrobe (Machine.Util.hwAt o "DBG" 0 r) 1 then some (1, v) else none) := by
  cases ho : Machine.Util.hwAt o "DBG" 0 r with
  | none => simp [byteStrobe, ho]
  | some p =>
    obtain ⟨j, w⟩ := p
    obtain ⟨hj, hw⟩ := h j w ho
    subst hw
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl <;> simp [byteStrobe, ho]

/-- `((a || b) && a) = a`. -/
theorem or_and_self_left (a b : Bool) : ((a || b) && a) = a := by
  cases a <;> simp

/-- **`DbgWire.hEH`** under the fixed wiring: the machine's host `EMASK` option
is the cut's `hostOpt2` of the two byte ports. -/
theorem dbgHEH (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    Machine.Util.hwAt (machHw m) "DBG" 0 "EMASK" =
      Bridge.Debug.hostOpt2 (Bridge.Debug.emaskPort0 (dbgCtrlIn s pin))
        (Bridge.Debug.emaskPort1 (dbgCtrlIn s pin)) := by
  rw [machHw_eq_hwOf hrel hinv]
  rw [hwAt_two_lane (o := hwOf s) (r := "EMASK") (v := (hwData s).toNat) ?_]
  · rw [hostByteStrobe_emask0 s, hostByteStrobe_emask1 s]
    rw [emaskPort0_eq, emaskPort1_eq]
    unfold Bridge.Debug.hostOpt2
    dsimp only
    have h0 : (dbgCtrlIn s pin).hEm0 =
        Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmask := by
      simpa only [dbgCtrlIn] using hostByteStrobe_emask0 s
    have h1 : (dbgCtrlIn s pin).hEm1 =
        Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmaskPlus1 := by
      simpa only [dbgCtrlIn] using hostByteStrobe_emask1 s
    rw [h0, h1]
    have hd0 : (dbgCtrlIn s pin).dWrEm0 =
        (Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmask ||
          (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 8))) := rfl
    have hd1 : (dbgCtrlIn s pin).dWrEm1 =
        (Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmaskPlus1 ||
          (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 9))) := rfl
    rw [show (dbgCtrlIn s pin).hWd = hwData s from rfl]
    rw [hd0, hd1, or_and_self_left, or_and_self_left]
  · intro j w hj
    obtain ⟨wt, l, hw, hl, hbyte, hv, hblk, hinst, hreg⟩ := hwAt_some_facts hj
    have hwr : s.hostCmd.wr = true := hwAt_some_wr hj
    have hwEq : wt = ⟨s.hostCmd.addr.toNat, s.hostCmd.wdata.toNat,
        Machine.hostLocate s.hostCmd.addr.toNat⟩ := by
      have h' := hw
      unfold hwOf at h'
      rw [if_pos hwr] at h'
      exact (Option.some.inj h').symm
    have hloc : Machine.hostLocate s.hostCmd.addr.toNat = some l := by
      rw [hwEq] at hl
      simpa using hl
    have hv' : s.hostCmd.wdata.toNat = w := by
      rw [hwEq] at hv
      exact hv
    obtain ⟨ha, hlt⟩ := hostLocate_emask_off s.hostCmd.addr.toNat l hloc hblk hreg
    refine ⟨by omega, ?_⟩
    rw [← hv']
    rfl

/-- **`DbgWire.hRH`**: the same for `RLV`. -/
theorem dbgHRH (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    Machine.Util.hwAt (machHw m) "DBG" 0 "RLV" =
      Bridge.Debug.hostOpt2 (Bridge.Debug.rlvPort0 (dbgCtrlIn s pin))
        (Bridge.Debug.rlvPort1 (dbgCtrlIn s pin)) := by
  rw [machHw_eq_hwOf hrel hinv]
  rw [hwAt_two_lane (o := hwOf s) (r := "RLV") (v := (hwData s).toNat) ?_]
  · rw [hostByteStrobe_rlv0 s, hostByteStrobe_rlv1 s]
    rw [rlvPort0_eq, rlvPort1_eq]
    unfold Bridge.Debug.hostOpt2
    dsimp only
    have h0 : (dbgCtrlIn s pin).hRlv0 =
        Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlv := by
      simpa only [dbgCtrlIn] using hostByteStrobe_rlv0 s
    have h1 : (dbgCtrlIn s pin).hRlv1 =
        Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlvPlus1 := by
      simpa only [dbgCtrlIn] using hostByteStrobe_rlv1 s
    rw [h0, h1]
    have hd0 : (dbgCtrlIn s pin).dWrRlv0 =
        (Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlv ||
          (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 18))) := rfl
    have hd1 : (dbgCtrlIn s pin).dWrRlv1 =
        (Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlvPlus1 ||
          (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 19))) := rfl
    rw [show (dbgCtrlIn s pin).hWd = hwData s from rfl]
    rw [hd0, hd1, or_and_self_left, or_and_self_left]
  · intro j w hj
    obtain ⟨wt, l, hw, hl, hbyte, hv, hblk, hinst, hreg⟩ := hwAt_some_facts hj
    have hwr : s.hostCmd.wr = true := hwAt_some_wr hj
    have hwEq : wt = ⟨s.hostCmd.addr.toNat, s.hostCmd.wdata.toNat,
        Machine.hostLocate s.hostCmd.addr.toNat⟩ := by
      have h' := hw
      unfold hwOf at h'
      rw [if_pos hwr] at h'
      exact (Option.some.inj h').symm
    have hloc : Machine.hostLocate s.hostCmd.addr.toNat = some l := by
      rw [hwEq] at hl
      simpa using hl
    have hv' : s.hostCmd.wdata.toNat = w := by
      rw [hwEq] at hv
      exact hv
    obtain ⟨ha, hlt⟩ := hostLocate_rlv_off s.hostCmd.addr.toNat l hloc hblk hreg
    refine ⟨by omega, ?_⟩
    rw [← hv']
    rfl

/-- **`DbgWire.hESH`** under the fixed wiring: one host write cannot be
host-selected on both `EMASK` bytes. -/
theorem dbgHESH (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ((dbgCtrlIn s pin).dWrEm0 && (dbgCtrlIn s pin).hEm0 &&
      (dbgCtrlIn s pin).dWrEm1 && (dbgCtrlIn s pin).hEm1) = false := by
  have h0 : (dbgCtrlIn s pin).hEm0 =
      Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmask := by
    simpa only [dbgCtrlIn] using hostByteStrobe_emask0 s
  have h1 : (dbgCtrlIn s pin).hEm1 =
      Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmaskPlus1 := by
    simpa only [dbgCtrlIn] using hostByteStrobe_emask1 s
  have hd0 : (dbgCtrlIn s pin).dWrEm0 =
      (Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmask ||
        (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 8))) := rfl
  rw [hd0, h0, h1, or_and_self_left]
  by_cases h8 : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmask = true
  · have h9 : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmaskPlus1 =
        false := by
      by_cases hh : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr)
          Strobes.hoDbgEmaskPlus1 = true
      · have a0 := hostDbg_emask0_addr h8
        have a1 := hostDbg_emask1_addr hh
        rw [a0] at a1
        exact absurd a1 (by decide)
      · simpa using hh
    rw [h8, h9]
    simp
  · have h8' : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgEmask =
        false := by simpa using h8
    simp [h8']

/-- **`DbgWire.hRSH`** under the fixed wiring: the same for `RLV`. -/
theorem dbgHRSH (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    ((dbgCtrlIn s pin).dWrRlv0 && (dbgCtrlIn s pin).hRlv0 &&
      (dbgCtrlIn s pin).dWrRlv1 && (dbgCtrlIn s pin).hRlv1) = false := by
  have h0 : (dbgCtrlIn s pin).hRlv0 =
      Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlv := by
    simpa only [dbgCtrlIn] using hostByteStrobe_rlv0 s
  have h1 : (dbgCtrlIn s pin).hRlv1 =
      Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlvPlus1 := by
    simpa only [dbgCtrlIn] using hostByteStrobe_rlv1 s
  have hd0 : (dbgCtrlIn s pin).dWrRlv0 =
      (Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlv ||
        (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 18))) := rfl
  rw [hd0, h0, h1, or_and_self_left]
  by_cases h8 : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlv = true
  · have h9 : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlvPlus1 =
        false := by
      by_cases hh : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlvPlus1 =
          true
      · have a0 := hostDbg_rlv0_addr h8
        have a1 := hostDbg_rlv1_addr hh
        rw [a0] at a1
        exact absurd a1 (by decide)
      · simpa using hh
    rw [h8, h9]
    simp
  · have h8' : Strobes.hostDbg (hwDbg s) (dbgOff s.hostCmd.addr) Strobes.hoDbgRlv =
        false := by simpa using h8
    simp [h8']

/-! ## 11. Register-value facts (the restatement proposal)

`StreamDbg.premise_dbg` consumes `DbgRel`, whose `EMASK`/`RLV` fields are
`(Machine.step m pin).dbg.emask = (activeStep s pin).dbgCtrl.emask` and the
same for `rlv`; `Bridge.Debug.emask_bridge`/`rlv_bridge` conclude exactly those
register values through `dbgNext`.  The two facts below are the value-level
statements the assembler can use *instead of* the four per-port leaves
`hEH/hEC/hESH` and `hRH/hRC/hRSH`: the machine applies the drained byte and
then the host byte (§13.1), which is the cut's per-byte host-or-drain value
even when both target the same byte. -/

/-- A machine `setByte` at a lane of a 16-bit word, truncated to 13 bits. -/
theorem bv13_setByte_nat (x k v : Nat) (hk : k < 2) (hx : x < 2 ^ 16) (hv : v < 256) :
    Machine.Util.bv 13 ((Machine.Util.setByte (Machine.Util.bv 16 x) k v).toNat) =
      Bridge.Debug.setByte13 (Machine.Util.bv 13 x) k (BitVec.ofNat 8 v) := by
  have h := Bridge.Debug.bv13_setByte x k (BitVec.ofNat 8 v) hk hx
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv] at h

/-- Two machine byte writes at lanes of a 16-bit word, truncated to 13 bits. -/
theorem bv13_setByte2_nat (x k1 k2 v1 v2 : Nat) (h1 : k1 < 2) (h2 : k2 < 2)
    (hx : x < 2 ^ 16) (hv1 : v1 < 256) (hv2 : v2 < 256) :
    Machine.Util.bv 13 ((Machine.Util.setByte (Machine.Util.bv 16
        ((Machine.Util.setByte (Machine.Util.bv 16 x) k1 v1).toNat)) k2 v2).toNat) =
      Bridge.Debug.setByte13 (Bridge.Debug.setByte13 (Machine.Util.bv 13 x) k1
        (BitVec.ofNat 8 v1)) k2 (BitVec.ofNat 8 v2) := by
  rw [bv13_setByte_nat (Machine.Util.setByte (Machine.Util.bv 16 x) k1 v1).toNat k2 v2 h2
    (Machine.Util.setByte (Machine.Util.bv 16 x) k1 v1).isLt hv2]
  rw [bv13_setByte_nat x k1 v1 h1 hx hv1]

/-- The lane-0 and lane-1 forms of `setByte13` and their slices. -/
theorem setByte13_0_eq (x : BitVec 13) (v : BitVec 8) :
    Bridge.Debug.setByte13 x 0 v = Metronome.Debug.slice x 8 5 ++ v := by
  simp [Bridge.Debug.setByte13]

theorem setByte13_1_eq (x : BitVec 13) (v : BitVec 8) :
    Bridge.Debug.setByte13 x 1 v = Metronome.Debug.slice v 0 5 ++ Metronome.Debug.slice x 0 8 := by
  simp [Bridge.Debug.setByte13]

theorem slice_setByte13_0 (x : BitVec 13) (v : BitVec 8) :
    Metronome.Debug.slice (Bridge.Debug.setByte13 x 0 v) 0 8 = v := by
  rw [setByte13_0_eq]
  unfold Metronome.Debug.slice
  bv_decide

theorem slice_setByte13_1_lo (x : BitVec 13) (v : BitVec 8) :
    Metronome.Debug.slice (Bridge.Debug.setByte13 x 1 v) 0 8 = Metronome.Debug.slice x 0 8 := by
  rw [setByte13_1_eq]
  unfold Metronome.Debug.slice
  bv_decide

theorem slice_setByte13_1_hi (x : BitVec 13) (v : BitVec 8) :
    Metronome.Debug.slice (Bridge.Debug.setByte13 x 1 v) 8 5 = Metronome.Debug.slice v 0 5 := by
  rw [setByte13_1_eq]
  unfold Metronome.Debug.slice
  bv_decide

/-- Slices of a `5 ++ 8` concatenation. -/
theorem slice5_append_low (a : BitVec 5) (b : BitVec 8) :
    Metronome.Debug.slice (a ++ b) 0 8 = b := by
  unfold Metronome.Debug.slice
  bv_decide

theorem slice5_append_hi (a : BitVec 5) (b : BitVec 8) :
    Metronome.Debug.slice (a ++ b) 8 5 = a := by
  unfold Metronome.Debug.slice
  bv_decide

/-- **The two-byte register value.**  With per-lane host/drain strobes
`h0,h1,d0,d1` (at most one of each) and the machine's two write options, the
machine's core-then-host byte application is the cut's two-port value. -/
theorem byteW2_value (x : Nat) (hx : x < 2 ^ 13) (hwd cwd : BitVec 8)
    (h0 h1 d0 d1 : Bool) (hw cw : Option Machine.HostWr) (r : String)
    (hH : Machine.Util.hwAt hw "DBG" 0 r =
      (if h0 then some (0, hwd.toNat) else if h1 then some (1, hwd.toNat) else none))
    (hC : Machine.Util.hwAt cw "DBG" 0 r =
      (if d0 then some (0, cwd.toNat) else if d1 then some (1, cwd.toNat) else none))
    (h01 : h0 = true → h1 = false) (d01 : d0 = true → d1 = false) :
    Machine.Util.bv 13 (Bridge.Debug.byteWOf hw cw x r) =
      Bridge.Debug.writeBytes (Machine.Util.bv 13 x) ⟨h0 || d0, h0, hwd, cwd⟩
        ⟨h1 || d1, h1, hwd, cwd⟩ := by
  unfold Bridge.Debug.byteWOf Bridge.Debug.writeBytes
  dsimp only
  rw [hH, hC]
  have hx16 : x < 2 ^ 16 := by omega
  have hwdlt : hwd.toNat < 256 := hwd.isLt
  have hcwdlt : cwd.toNat < 256 := cwd.isLt
  generalize hxb : Machine.Util.bv 13 x = xb
  cases h0 <;> cases h1 <;> cases d0 <;> cases d1 <;> simp_all
  all_goals
    first
    | exact (Metronome.Debug.slice13 xb).symm
    | (rw [bv13_setByte2_nat _ _ _ _ _ (by decide) (by decide) (by omega) (by omega) (by omega)]
       try rw [hxb]
       try rw [show BitVec.ofNat 8 cwd.toNat = cwd from Bridge.Debug.bv_self cwd]
       try rw [show BitVec.ofNat 8 hwd.toNat = hwd from Bridge.Debug.bv_self hwd]
       try simp only [setByte13_0_eq, setByte13_1_eq, slice_setByte13_0, slice_setByte13_1_lo,
         slice_setByte13_1_hi, slice5_append_low, slice5_append_hi]
       try rfl)
    | (rw [bv13_setByte_nat _ _ _ (by decide) (by omega) (by omega)]
       try rw [hxb]
       try rw [show BitVec.ofNat 8 cwd.toNat = cwd from Bridge.Debug.bv_self cwd]
       try rw [show BitVec.ofNat 8 hwd.toNat = hwd from Bridge.Debug.bv_self hwd]
       try simp only [setByte13_0_eq, setByte13_1_eq, slice_setByte13_0, slice_setByte13_1_lo,
         slice_setByte13_1_hi, slice5_append_low, slice5_append_hi]
       try rfl)

/-- **The `EMASK` register value.**  Given the host-byte decode (`hH`, proved
by `dbgHEH`) and the drained-byte decode (`hC`), the machine's next `EMASK`
(core byte applied first, then the host byte, �13.1) is the cut's next
`EMASK`, for every combination of the two byte strobes. -/
theorem emask_value_of {s : State} {m : Machine.State} {pin : Machine.PinIn}
    (hrel : ChipRel s m) (hact : runRst s pin = true)
    (hH : Machine.Util.hwAt (machHw m) "DBG" 0 "EMASK" =
      (if byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 0 then
          some (0, (hwData s).toNat)
       else if byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 1 then
          some (1, (hwData s).toNat) else none))
    (hC : Machine.Util.hwAt (machCw m) "DBG" 0 "EMASK" =
      (if (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 8)) then
          some (0, s.cq.pendingData.toNat)
       else if (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 9)) then
          some (1, s.cq.pendingData.toNat) else none))
    (h01 : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 0 = true →
      byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 1 = false)
    (d01 : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 8)) = true →
      (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 9)) = false) :
    (machDbgNext m).emask = (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).emask := by
  have hL : (machDbgNext m).emask = Machine.Util.bv 13
      (Bridge.Debug.byteWOf (machHw m) (machCw m) m.dbg.emask.toNat "EMASK") := rfl
  rw [hL, ctrl_step_emask s.dbgCtrl (dbgCtrlIn s pin) hact]
  rw [show Debug.Ctrl.emaskNext s.dbgCtrl.emask (dbgCtrlIn s pin) =
      Bridge.Debug.writeBytes s.dbgCtrl.emask (Bridge.Debug.emaskPort0 (dbgCtrlIn s pin))
        (Bridge.Debug.emaskPort1 (dbgCtrlIn s pin)) from by
    unfold Debug.Ctrl.emaskNext Bridge.Debug.writeBytes Bridge.Debug.emaskPort0
      Bridge.Debug.emaskPort1
    simp only [Bridge.Debug.slice_ite]]
  rw [show m.dbg.emask = s.dbgCtrl.emask from DbgRel.emask_eq hrel.dbg]
  rw [emaskPort0_eq, emaskPort1_eq]
  have e0 : (dbgCtrlIn s pin).hEm0 =
      byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 0 := rfl
  have e1 : (dbgCtrlIn s pin).hEm1 =
      byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 1 := rfl
  have ew : (dbgCtrlIn s pin).hWd = hwData s := rfl
  have ec : (dbgCtrlIn s pin).cwData = s.cq.pendingData := rfl
  have d0e : (dbgCtrlIn s pin).dWrEm0 =
      (byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 0 ||
        (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 8))) := by
    rw [show (dbgCtrlIn s pin).dWrEm0 = (Strobes.hostDbg (hwDbg s)
      (dbgOff s.hostCmd.addr) Strobes.hoDbgEmask ||
        (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
          BitVec.ofNat 32 8))) from rfl]
    rw [hostByteStrobe_emask0 s]
  have d1e : (dbgCtrlIn s pin).dWrEm1 =
      (byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 1 ||
        (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 9))) := by
    rw [show (dbgCtrlIn s pin).dWrEm1 = (Strobes.hostDbg (hwDbg s)
      (dbgOff s.hostCmd.addr) Strobes.hoDbgEmaskPlus1 ||
        (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
          BitVec.ofNat 32 9))) from rfl]
    rw [hostByteStrobe_emask1 s]
  rw [e0, e1, ew, ec, d0e, d1e]
  have hb := byteW2_value s.dbgCtrl.emask.toNat s.dbgCtrl.emask.isLt (hwData s)
    s.cq.pendingData _ _ _ _ (machHw m) (machCw m) "EMASK" hH hC h01 d01
  simpa only [show Machine.Util.bv 13 s.dbgCtrl.emask.toNat = s.dbgCtrl.emask from
    Bridge.Debug.bv_self s.dbgCtrl.emask] using hb

/-- **The `RLV` register value, apply-conditional `WB`.**  The machine reads its
first replay slot only in an apply cycle (`Debug.Ctrl.apply` conjoins
`replayValid`, whose bit 0 is the cut's `WV`), so the unguarded `WB` equality is
too strong (B1's `Bridge.StreamBuf.dbgHwb_unguarded_false` refutes it on a
reachable state).  This is the `EMASK` value fact for the replay-level register,
with the `WB` hypothesis needed only when `apply` fires: the machine's next
`RLV` (replay levels, then the drained byte, then the host byte) is the cut's
next `RLV`.  The replay value needs the two existing `DbgWire` fields
`hwb`/`happly`. -/
theorem rlv_value_of_apply {s : State} {m : Machine.State} {pin : Machine.PinIn}
    (hrel : ChipRel s m) (hact : runRst s pin = true)
    (hwb : (machApplyLate m).1 = true →
      (Machine.Util.vget m.streams 0).wb = (streamAt s 0).wb)
    (happly : (machApplyLate m).1 =
      Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
        (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
        (dbgCtrlIn s pin).replayWord)
    (hH : Machine.Util.hwAt (machHw m) "DBG" 0 "RLV" =
      (if byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0 then
          some (0, (hwData s).toNat)
       else if byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1 then
          some (1, (hwData s).toNat) else none))
    (hC : Machine.Util.hwAt (machCw m) "DBG" 0 "RLV" =
      (if (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 18)) then
          some (0, s.cq.pendingData.toNat)
       else if (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 19)) then
          some (1, s.cq.pendingData.toNat) else none))
    (h01 : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0 = true →
      byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1 = false)
    (d01 : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 18)) = true →
      (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 19)) = false) :
    (machDbgNext m).rlv = (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).rlv := by
  have hL : (machDbgNext m).rlv = Machine.Util.bv 13
      (Bridge.Debug.byteWOf (machHw m) (machCw m)
        (if (machApplyLate m).1 then
            (m.dbg.rlv.toNat &&& (2 ^ 13 - 1 - m.dbg.emask.toNat)) |||
              ((Machine.Util.vget m.streams 0).wb.toNat &&& m.dbg.emask.toNat)
         else m.dbg.rlv.toNat) "RLV") := rfl
  rw [hL, ctrl_step_rlv s.dbgCtrl (dbgCtrlIn s pin) hact]
  rw [show Debug.Ctrl.rlvNext s.dbgCtrl (dbgCtrlIn s pin) =
      Bridge.Debug.writeBytes
        (Debug.Ctrl.replayLevels s.dbgCtrl.rlv s.dbgCtrl.emask
          (Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
            (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
            (dbgCtrlIn s pin).replayWord)
          (dbgCtrlIn s pin).replayWord)
        (Bridge.Debug.rlvPort0 (dbgCtrlIn s pin))
        (Bridge.Debug.rlvPort1 (dbgCtrlIn s pin)) from by
    unfold Debug.Ctrl.rlvNext Bridge.Debug.writeBytes Bridge.Debug.rlvPort0
      Bridge.Debug.rlvPort1
    simp only [Bridge.Debug.slice_ite]]
  have hval : (if (machApplyLate m).1 then
        (m.dbg.rlv.toNat &&& (2 ^ 13 - 1 - m.dbg.emask.toNat)) |||
          ((Machine.Util.vget m.streams 0).wb.toNat &&& m.dbg.emask.toNat)
      else m.dbg.rlv.toNat) =
      (Debug.Ctrl.replayLevels s.dbgCtrl.rlv s.dbgCtrl.emask
        (Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
          (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
          (dbgCtrlIn s pin).replayWord)
        (dbgCtrlIn s pin).replayWord).toNat := by
    rw [Bridge.Debug.replayLevels_toNat, ← happly, DbgRel.rlv_eq hrel.dbg,
      DbgRel.emask_eq hrel.dbg]
    rw [show (dbgCtrlIn s pin).replayWord = (streamAt s 0).wb from rfl]
    by_cases h : (machApplyLate m).1
    · rw [if_pos h, if_pos h]
      rw [hwb h]
      rw [Bridge.Debug.and_nbits13 (streamAt s 0).wb.toNat s.dbgCtrl.emask]
    · rw [if_neg h, if_neg h]
  rw [hval]
  rw [rlvPort0_eq, rlvPort1_eq]
  have e0 : (dbgCtrlIn s pin).hRlv0 =
      byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0 := rfl
  have e1 : (dbgCtrlIn s pin).hRlv1 =
      byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1 := rfl
  have ew : (dbgCtrlIn s pin).hWd = hwData s := rfl
  have ec : (dbgCtrlIn s pin).cwData = s.cq.pendingData := rfl
  have d0e : (dbgCtrlIn s pin).dWrRlv0 =
      (byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0 ||
        (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 18))) := by
    rw [show (dbgCtrlIn s pin).dWrRlv0 = (Strobes.hostDbg (hwDbg s)
      (dbgOff s.hostCmd.addr) Strobes.hoDbgRlv ||
        (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
          BitVec.ofNat 32 18))) from rfl]
    rw [hostByteStrobe_rlv0 s]
  have d1e : (dbgCtrlIn s pin).dWrRlv1 =
      (byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1 ||
        (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 19))) := by
    rw [show (dbgCtrlIn s pin).dWrRlv1 = (Strobes.hostDbg (hwDbg s)
      (dbgOff s.hostCmd.addr) Strobes.hoDbgRlvPlus1 ||
        (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
          BitVec.ofNat 32 19))) from rfl]
    rw [hostByteStrobe_rlv1 s]
  rw [e0, e1, ew, ec, d0e, d1e]
  rw [show Debug.Ctrl.replayLevels s.dbgCtrl.rlv s.dbgCtrl.emask
      (Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
        (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
        (dbgCtrlIn s pin).replayWord)
      (dbgCtrlIn s pin).replayWord =
      Machine.Util.bv 13 (Debug.Ctrl.replayLevels s.dbgCtrl.rlv s.dbgCtrl.emask
        (Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
          (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
          (dbgCtrlIn s pin).replayWord)
        (dbgCtrlIn s pin).replayWord).toNat from
    (Bridge.Debug.bv_self _).symm]
  have hb := byteW2_value (Debug.Ctrl.replayLevels s.dbgCtrl.rlv s.dbgCtrl.emask
      (Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
        (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
        (dbgCtrlIn s pin).replayWord)
      (dbgCtrlIn s pin).replayWord).toNat
    (Debug.Ctrl.replayLevels s.dbgCtrl.rlv s.dbgCtrl.emask
      (Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
        (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
        (dbgCtrlIn s pin).replayWord)
      (dbgCtrlIn s pin).replayWord).isLt
    (hwData s) s.cq.pendingData _ _ _ _ (machHw m) (machCw m) "RLV" hH hC h01 d01
  simpa only [show Machine.Util.bv 13
      (Debug.Ctrl.replayLevels s.dbgCtrl.rlv s.dbgCtrl.emask
        (Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
          (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
          (dbgCtrlIn s pin).replayWord)
        (dbgCtrlIn s pin).replayWord).toNat
      = Debug.Ctrl.replayLevels s.dbgCtrl.rlv s.dbgCtrl.emask
        (Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
          (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
          (dbgCtrlIn s pin).replayWord)
        (dbgCtrlIn s pin).replayWord from
    Bridge.Debug.bv_self _] using hb

/-- **The `RLV` register value.**  The `EMASK` value fact for the replay-level
register: the machine's next `RLV` (replay levels, then the drained byte, then
the host byte) is the cut's next `RLV`.  The replay value needs the two
existing `DbgWire` fields `hwb`/`happly`.  (The unguarded `hwb` form is kept
for the consumers that already carry it; `dbgRlvValue_of_wv` below is the
WV-guarded, reachable version.) -/
theorem rlv_value_of {s : State} {m : Machine.State} {pin : Machine.PinIn}
    (hrel : ChipRel s m) (hact : runRst s pin = true)
    (hwb : (Machine.Util.vget m.streams 0).wb = (streamAt s 0).wb)
    (happly : (machApplyLate m).1 =
      Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
        (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
        (dbgCtrlIn s pin).replayWord)
    (hH : Machine.Util.hwAt (machHw m) "DBG" 0 "RLV" =
      (if byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0 then
          some (0, (hwData s).toNat)
       else if byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1 then
          some (1, (hwData s).toNat) else none))
    (hC : Machine.Util.hwAt (machCw m) "DBG" 0 "RLV" =
      (if (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 18)) then
          some (0, s.cq.pendingData.toNat)
       else if (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 19)) then
          some (1, s.cq.pendingData.toNat) else none))
    (h01 : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0 = true →
      byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1 = false)
    (d01 : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 18)) = true →
      (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 19)) = false) :
    (machDbgNext m).rlv = (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).rlv :=
  rlv_value_of_apply hrel hact (fun _ => hwb) happly hH hC h01 d01

/-- A single host write is one byte (lane 0 excludes lane 1), `EMASK`. -/
theorem emask_host_01 (s : State) :
    byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 0 = true →
      byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 1 = false := by
  intro h
  unfold byteStrobe at h ⊢
  cases ho : Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK" with
  | none => simp [ho] at h
  | some p =>
    obtain ⟨j, v⟩ := p
    have hj : j = 0 := by simpa [ho] using h
    subst hj
    simp [ho]

/-- A single host write is one byte, `RLV`. -/
theorem rlv_host_01 (s : State) :
    byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0 = true →
      byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1 = false := by
  intro h
  unfold byteStrobe at h ⊢
  cases ho : Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV" with
  | none => simp [ho] at h
  | some p =>
    obtain ⟨j, v⟩ := p
    have hj : j = 0 := by simpa [ho] using h
    subst hj
    simp [ho]

/-- A single drain is one byte (offset 8 excludes offset 9), `EMASK`. -/
theorem emask_drain_01 (s : State) :
    (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 8)) = true →
      (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 9)) = false := by
  intro h
  have h8 : (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 8) = true := by
    have h' := h
    rw [Bool.and_eq_true] at h'
    exact h'.2
  have he : Strobes.cwDbgOff s.cq.pendingAddr = BitVec.ofNat 32 8 := beq_iff_eq.mp h8
  rw [he, show (BitVec.ofNat 32 8 == BitVec.ofNat 32 9) = false from by decide, Bool.and_false]

/-- A single drain is one byte (offset 18 excludes offset 19), `RLV`. -/
theorem rlv_drain_01 (s : State) :
    (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 18)) = true →
      (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 19)) = false := by
  intro h
  have h8 : (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 18) = true := by
    have h' := h
    rw [Bool.and_eq_true] at h'
    exact h'.2
  have he : Strobes.cwDbgOff s.cq.pendingAddr = BitVec.ofNat 32 18 := beq_iff_eq.mp h8
  rw [he, show (BitVec.ofNat 32 18 == BitVec.ofNat 32 19) = false from by decide,
    Bool.and_false]

/-- The cut's drain strobe at an `EMASK` byte pins the queued address. -/
theorem cwDrain_emask_addr {s : State} {off : Nat} (hoff : off = 8 ∨ off = 9)
    (hd : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
      BitVec.ofNat 32 off)) = true) :
    s.cq.pendingAddr = (0x2468 + (off - 8) : Nat) := by
  have ho : (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 off) = true := by
    have h' := hd
    rw [Bool.and_eq_true] at h'
    exact h'.2
  rcases hoff with rfl | rfl
  · have hn := cwDbgOff_eq_addr (D := 8) (by decide) ho
    apply BitVec.eq_of_toNat_eq
    rw [hn]
    decide
  · have hn := cwDbgOff_eq_addr (D := 9) (by decide) ho
    apply BitVec.eq_of_toNat_eq
    rw [hn]
    decide

/-- The cut's drain strobe at an `RLV` byte pins the queued address. -/
theorem cwDrain_rlv_addr {s : State} {off : Nat} (hoff : off = 18 ∨ off = 19)
    (hd : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
      BitVec.ofNat 32 off)) = true) :
    s.cq.pendingAddr = (0x2472 + (off - 18) : Nat) := by
  have ho : (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 off) = true := by
    have h' := hd
    rw [Bool.and_eq_true] at h'
    exact h'.2
  rcases hoff with rfl | rfl
  · have hn := cwDbgOff_eq_addr (D := 18) (by decide) ho
    apply BitVec.eq_of_toNat_eq
    rw [hn]
    decide
  · have hn := cwDbgOff_eq_addr (D := 19) (by decide) ho
    apply BitVec.eq_of_toNat_eq
    rw [hn]
    decide

/-- The machine's drained address is a runtime target (a `DBG` register byte). -/
theorem machCw_runtime {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    machCw m = none ∨ ∃ (r : String) (b : Nat) (l : Machine.HostLoc),
      Machine.hostLocate s.cq.pendingAddr.toNat = some l ∧ l.blk = "DBG" ∧
        l.reg = r ∧ l.byte = b ∧ b < 2 := by
  rw [machCw_eq hrel]
  by_cases hC : (!s.freeze.frz && s.cq.pending &&
      !(s.cq.pending && Machine.Config.isCfgAddr s.cq.pendingAddr.toNat) &&
      Machine.cwRuntimeTarget s.cq.pendingAddr.toNat) = true
  · rw [if_pos hC]
    right
    obtain ⟨l, hl, hblk, hregs⟩ := cwRuntimeTarget_loc (by
      have h2 := hC
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h2
      exact h2.2)
    refine ⟨l.reg, l.byte, l, hl, hblk, rfl, rfl, ?_⟩
    rcases hregs with h | h | h
    · obtain ⟨-, hb⟩ := hostLocate_ectl_off s.cq.pendingAddr.toNat l hl hblk h
      omega
    · obtain ⟨-, hb⟩ := hostLocate_emask_off s.cq.pendingAddr.toNat l hl hblk h
      omega
    · obtain ⟨-, hb⟩ := hostLocate_rlv_off s.cq.pendingAddr.toNat l hl hblk h
      omega
  · rw [if_neg hC]
    left
    rfl

/-- A set `cwDrain` needs the pending queue. -/
theorem cwDrain_pending {s : State} (h : cwDrain s = true) : s.cq.pending = true := by
  unfold cwDrain at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.1

/-- A set `cwDrain` needs an unfrozen cycle. -/
theorem cwDrain_frz {s : State} (h : cwDrain s = true) : (!s.freeze.frz) = true := by
  unfold cwDrain at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.2

/-- A cut drain strobe at an `EMASK` byte implies the machine's drain
condition. -/
theorem emask_drain_imp_C {s : State} {off : Nat} (hoff : off = 8 ∨ off = 9)
    (hd : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
      BitVec.ofNat 32 off)) = true) :
    (!s.freeze.frz && s.cq.pending &&
      !(s.cq.pending && Machine.Config.isCfgAddr s.cq.pendingAddr.toNat) &&
      Machine.cwRuntimeTarget s.cq.pendingAddr.toNat) = true := by
  have hdrain : cwDrain s = true := by
    have h' := hd
    rw [Bool.and_eq_true] at h'
    exact h'.1
  have hp := cwDrain_pending hdrain
  have hf := cwDrain_frz hdrain
  have hq : s.cq.pendingAddr.toNat = 0x2468 + (off - 8) := by
    have h := congrArg BitVec.toNat (cwDrain_emask_addr hoff hd)
    have hlt : (9320 + (off - 8)) < 65536 := by omega
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] using h
  have hn : s.cq.pendingAddr.toNat = 9320 ∨ s.cq.pendingAddr.toNat = 9321 := by
    rcases hoff with rfl | rfl
    · exact Or.inl hq
    · exact Or.inr hq
  rcases hn with hn | hn
  · rw [hn] at ⊢
    rw [isCfgAddr_false_of _ (by decide)] at ⊢
    rw [hp, hf]
    rfl
  · rw [hn] at ⊢
    rw [isCfgAddr_false_of _ (by decide)] at ⊢
    rw [hp, hf]
    rfl

/-- A cut drain strobe at an `RLV` byte implies the machine's drain condition. -/
theorem rlv_drain_imp_C {s : State} {off : Nat} (hoff : off = 18 ∨ off = 19)
    (hd : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
      BitVec.ofNat 32 off)) = true) :
    (!s.freeze.frz && s.cq.pending &&
      !(s.cq.pending && Machine.Config.isCfgAddr s.cq.pendingAddr.toNat) &&
      Machine.cwRuntimeTarget s.cq.pendingAddr.toNat) = true := by
  have hdrain : cwDrain s = true := by
    have h' := hd
    rw [Bool.and_eq_true] at h'
    exact h'.1
  have hp := cwDrain_pending hdrain
  have hf := cwDrain_frz hdrain
  have hq : s.cq.pendingAddr.toNat = 0x2472 + (off - 18) := by
    have h := congrArg BitVec.toNat (cwDrain_rlv_addr hoff hd)
    have hlt : (9330 + (off - 18)) < 65536 := by omega
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] using h
  have hn : s.cq.pendingAddr.toNat = 9330 ∨ s.cq.pendingAddr.toNat = 9331 := by
    rcases hoff with rfl | rfl
    · exact Or.inl hq
    · exact Or.inr hq
  rcases hn with hn | hn
  · rw [hn] at ⊢
    rw [isCfgAddr_false_of _ (by decide)] at ⊢
    rw [hp, hf]
    rfl
  · rw [hn] at ⊢
    rw [isCfgAddr_false_of _ (by decide)] at ⊢
    rw [hp, hf]
    rfl

/-- **The drained core write on `EMASK`.**  The machine's drained byte is at the
lane the cut's `cw_drain` strobe marks (offsets 8 and 9). -/
theorem machCw_emask_lane {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    Machine.Util.hwAt (machCw m) "DBG" 0 "EMASK" =
      (if (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 8)) then
          some (0, s.cq.pendingData.toNat)
       else if (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 9)) then
          some (1, s.cq.pendingData.toNat) else none) := by
  rw [machCw_eq hrel]
  by_cases hC : (!s.freeze.frz && s.cq.pending &&
      !(s.cq.pending && Machine.Config.isCfgAddr s.cq.pendingAddr.toNat) &&
      Machine.cwRuntimeTarget s.cq.pendingAddr.toNat) = true
  · rw [if_pos hC]
    have hdrain : cwDrain s = true := by
      have h2 := hC
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h2
      obtain ⟨⟨⟨hf, hp⟩, hni⟩, -⟩ := h2
      rcases hc0 : Machine.Config.isCfgAddr s.cq.pendingAddr.toNat with _ | _
      · unfold cwDrain
        rw [hp, hf, hc0]
        simp
      · exfalso
        rw [hp, hc0] at hni
        exact absurd hni (by decide)
    have d8 : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 8)) =
        (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 8) := by
      rw [hdrain, Bool.true_and]
    have d9 : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 9)) =
        (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 9) := by
      rw [hdrain, Bool.true_and]
    rw [d8, d9]
    obtain ⟨l, hl, hblk, -⟩ := cwRuntimeTarget_loc (by
      have h2 := hC
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h2
      exact h2.2)
    have hloc : Machine.hostLocate s.cq.pendingAddr.toNat = some l := hl
    by_cases hreg : l.reg = "EMASK"
    · obtain ⟨ha, hlt⟩ := hostLocate_emask_off s.cq.pendingAddr.toNat l hl hblk hreg
      have hbyte : l.byte = 0 ∨ l.byte = 1 := by omega
      have hopt : Machine.Util.hwAt (some ⟨s.cq.pendingAddr.toNat, s.cq.pendingData.toNat,
          Machine.hostLocate s.cq.pendingAddr.toNat⟩) "DBG" 0 "EMASK" =
          some (l.byte, s.cq.pendingData.toNat) := by
        rcases hbyte with hb | hb
        · obtain ⟨l0, hl0, hb0, hi0, hr0, -⟩ := hostLocate_fields hostLocate_emask0
          have hn : s.cq.pendingAddr.toNat = 0x2468 := by omega
          rw [hn] at hloc ⊢
          have hll : l = l0 := Option.some.inj (hloc.symm.trans hl0)
          subst hll
          simp only [Machine.Util.hwAt, hloc, hb0, hi0, hr0, Bool.and_self, if_true]
          simp
        · obtain ⟨l0, hl0, hb0, hi0, hr0, -⟩ := hostLocate_fields hostLocate_emask1
          have hn : s.cq.pendingAddr.toNat = 0x2469 := by omega
          rw [hn] at hloc ⊢
          have hll : l = l0 := Option.some.inj (hloc.symm.trans hl0)
          subst hll
          simp only [Machine.Util.hwAt, hloc, hb0, hi0, hr0, Bool.and_self, if_true]
          simp
      rw [hopt]
      rcases hbyte with hb | hb
      · have hq : s.cq.pendingAddr = (0x2468 : BitVec 16) := by
          apply BitVec.eq_of_toNat_eq
          rw [show s.cq.pendingAddr.toNat = 0x2468 from by omega]
          decide
        rw [hb, hq,
          show (Strobes.cwDbgOff (0x2468 : BitVec 16) == BitVec.ofNat 32 8) = true from by decide,
          show (Strobes.cwDbgOff (0x2468 : BitVec 16) == BitVec.ofNat 32 9) = false from by decide]
        rfl
      · have hq : s.cq.pendingAddr = (0x2469 : BitVec 16) := by
          apply BitVec.eq_of_toNat_eq
          rw [show s.cq.pendingAddr.toNat = 0x2469 from by omega]
          decide
        rw [hb, hq,
          show (Strobes.cwDbgOff (0x2469 : BitVec 16) == BitVec.ofNat 32 8) = false from by decide,
          show (Strobes.cwDbgOff (0x2469 : BitVec 16) == BitVec.ofNat 32 9) = true from by decide]
        rfl
    · have hnone : Machine.Util.hwAt (some ⟨s.cq.pendingAddr.toNat, s.cq.pendingData.toNat,
          Machine.hostLocate s.cq.pendingAddr.toNat⟩) "DBG" 0 "EMASK" = none := by
        have hrf : (l.reg == "EMASK") = false := by
          by_cases hr : l.reg = "EMASK"
          · exact absurd hr hreg
          · simpa [beq_iff_eq] using hr
        simp only [Machine.Util.hwAt, hloc, hblk, hrf, Bool.and_false, Bool.false_and]
        rfl
      rw [hnone]
      have h8f : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
          BitVec.ofNat 32 8)) = false := by
        by_cases h : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
            BitVec.ofNat 32 8)) = true
        · exfalso
          have hq := cwDrain_emask_addr (Or.inl rfl) h
          have hqa : s.cq.pendingAddr = (0x2468 : BitVec 16) := by
            have := congrArg BitVec.toNat hq
            apply BitVec.eq_of_toNat_eq
            simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : (9320 : Nat) < 65536)]
              using this
          rw [hqa] at hloc
          obtain ⟨l0, hl0, -, -, hr0, -⟩ := hostLocate_fields hostLocate_emask0
          have hll : l = l0 := Option.some.inj (hloc.symm.trans hl0)
          rw [hll] at hreg
          exact hreg hr0
        · simpa using h
      have h9f : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
          BitVec.ofNat 32 9)) = false := by
        by_cases h : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
            BitVec.ofNat 32 9)) = true
        · exfalso
          have hq := cwDrain_emask_addr (Or.inr rfl) h
          have hqa : s.cq.pendingAddr = (0x2469 : BitVec 16) := by
            have := congrArg BitVec.toNat hq
            apply BitVec.eq_of_toNat_eq
            simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : (9321 : Nat) < 65536)]
              using this
          rw [hqa] at hloc
          obtain ⟨l0, hl0, -, -, hr0, -⟩ := hostLocate_fields hostLocate_emask1
          have hll : l = l0 := Option.some.inj (hloc.symm.trans hl0)
          rw [hll] at hreg
          exact hreg hr0
        · simpa using h
      have hx8 : (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 8) = false := by
        rw [← d8]
        exact h8f
      have hx9 : (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 9) = false := by
        rw [← d9]
        exact h9f
      rw [hx8, hx9]
      rfl
  · rw [if_neg hC]
    have h8f : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
        BitVec.ofNat 32 8)) = false := by
      by_cases h : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
          BitVec.ofNat 32 8)) = true
      · exfalso
        have hC' := emask_drain_imp_C (Or.inl rfl) h
        exact absurd hC' hC
      · simpa using h
    have h9f : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
        BitVec.ofNat 32 9)) = false := by
      by_cases h : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
          BitVec.ofNat 32 9)) = true
      · exfalso
        have hC' := emask_drain_imp_C (Or.inr rfl) h
        exact absurd hC' hC
      · simpa using h
    rw [h8f, h9f]
    rfl

/-- **The drained core write on `RLV`.**  The machine's drained byte is at the
lane the cut's `cw_drain` strobe marks (offsets 18 and 19). -/
theorem machCw_rlv_lane {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    Machine.Util.hwAt (machCw m) "DBG" 0 "RLV" =
      (if (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 18)) then
          some (0, s.cq.pendingData.toNat)
       else if (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 19)) then
          some (1, s.cq.pendingData.toNat) else none) := by
  rw [machCw_eq hrel]
  by_cases hC : (!s.freeze.frz && s.cq.pending &&
      !(s.cq.pending && Machine.Config.isCfgAddr s.cq.pendingAddr.toNat) &&
      Machine.cwRuntimeTarget s.cq.pendingAddr.toNat) = true
  · rw [if_pos hC]
    have hdrain : cwDrain s = true := by
      have h2 := hC
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h2
      obtain ⟨⟨⟨hf, hp⟩, hni⟩, -⟩ := h2
      rcases hc0 : Machine.Config.isCfgAddr s.cq.pendingAddr.toNat with _ | _
      · unfold cwDrain
        rw [hp, hf, hc0]
        simp
      · exfalso
        rw [hp, hc0] at hni
        exact absurd hni (by decide)
    have d8 : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 18)) =
        (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 18) := by
      rw [hdrain, Bool.true_and]
    have d9 : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 19)) =
        (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 19) := by
      rw [hdrain, Bool.true_and]
    rw [d8, d9]
    obtain ⟨l, hl, hblk, -⟩ := cwRuntimeTarget_loc (by
      have h2 := hC
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h2
      exact h2.2)
    have hloc : Machine.hostLocate s.cq.pendingAddr.toNat = some l := hl
    by_cases hreg : l.reg = "RLV"
    · obtain ⟨ha, hlt⟩ := hostLocate_rlv_off s.cq.pendingAddr.toNat l hl hblk hreg
      have hbyte : l.byte = 0 ∨ l.byte = 1 := by omega
      have hopt : Machine.Util.hwAt (some ⟨s.cq.pendingAddr.toNat, s.cq.pendingData.toNat,
          Machine.hostLocate s.cq.pendingAddr.toNat⟩) "DBG" 0 "RLV" =
          some (l.byte, s.cq.pendingData.toNat) := by
        rcases hbyte with hb | hb
        · obtain ⟨l0, hl0, hb0, hi0, hr0, -⟩ := hostLocate_fields hostLocate_rlv0
          have hn : s.cq.pendingAddr.toNat = 0x2472 := by omega
          rw [hn] at hloc ⊢
          have hll : l = l0 := Option.some.inj (hloc.symm.trans hl0)
          subst hll
          simp only [Machine.Util.hwAt, hloc, hb0, hi0, hr0, Bool.and_self, if_true]
          simp
        · obtain ⟨l0, hl0, hb0, hi0, hr0, -⟩ := hostLocate_fields hostLocate_rlv1
          have hn : s.cq.pendingAddr.toNat = 0x2473 := by omega
          rw [hn] at hloc ⊢
          have hll : l = l0 := Option.some.inj (hloc.symm.trans hl0)
          subst hll
          simp only [Machine.Util.hwAt, hloc, hb0, hi0, hr0, Bool.and_self, if_true]
          simp
      rw [hopt]
      rcases hbyte with hb | hb
      · have hq : s.cq.pendingAddr = (0x2472 : BitVec 16) := by
          apply BitVec.eq_of_toNat_eq
          rw [show s.cq.pendingAddr.toNat = 0x2472 from by omega]
          decide
        rw [hb, hq,
          show (Strobes.cwDbgOff (0x2472 : BitVec 16) == BitVec.ofNat 32 18) = true from by decide,
          show (Strobes.cwDbgOff (0x2472 : BitVec 16) == BitVec.ofNat 32 19) = false from by decide]
        rfl
      · have hq : s.cq.pendingAddr = (0x2473 : BitVec 16) := by
          apply BitVec.eq_of_toNat_eq
          rw [show s.cq.pendingAddr.toNat = 0x2473 from by omega]
          decide
        rw [hb, hq,
          show (Strobes.cwDbgOff (0x2473 : BitVec 16) == BitVec.ofNat 32 18) = false from by decide,
          show (Strobes.cwDbgOff (0x2473 : BitVec 16) == BitVec.ofNat 32 19) = true from by decide]
        rfl
    · have hnone : Machine.Util.hwAt (some ⟨s.cq.pendingAddr.toNat, s.cq.pendingData.toNat,
          Machine.hostLocate s.cq.pendingAddr.toNat⟩) "DBG" 0 "RLV" = none := by
        have hrf : (l.reg == "RLV") = false := by
          by_cases hr : l.reg = "RLV"
          · exact absurd hr hreg
          · simpa [beq_iff_eq] using hr
        simp only [Machine.Util.hwAt, hloc, hblk, hrf, Bool.and_false, Bool.false_and]
        rfl
      rw [hnone]
      have h8f : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
          BitVec.ofNat 32 18)) = false := by
        by_cases h : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
            BitVec.ofNat 32 18)) = true
        · exfalso
          have hq := cwDrain_rlv_addr (Or.inl rfl) h
          have hqa : s.cq.pendingAddr = (0x2472 : BitVec 16) := by
            have := congrArg BitVec.toNat hq
            apply BitVec.eq_of_toNat_eq
            simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : (9330 : Nat) < 65536)]
              using this
          rw [hqa] at hloc
          obtain ⟨l0, hl0, -, -, hr0, -⟩ := hostLocate_fields hostLocate_rlv0
          have hll : l = l0 := Option.some.inj (hloc.symm.trans hl0)
          rw [hll] at hreg
          exact hreg hr0
        · simpa using h
      have h9f : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
          BitVec.ofNat 32 19)) = false := by
        by_cases h : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
            BitVec.ofNat 32 19)) = true
        · exfalso
          have hq := cwDrain_rlv_addr (Or.inr rfl) h
          have hqa : s.cq.pendingAddr = (0x2473 : BitVec 16) := by
            have := congrArg BitVec.toNat hq
            apply BitVec.eq_of_toNat_eq
            simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : (9331 : Nat) < 65536)]
              using this
          rw [hqa] at hloc
          obtain ⟨l0, hl0, -, -, hr0, -⟩ := hostLocate_fields hostLocate_rlv1
          have hll : l = l0 := Option.some.inj (hloc.symm.trans hl0)
          rw [hll] at hreg
          exact hreg hr0
        · simpa using h
      have hx8 : (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 18) = false := by
        rw [← d8]
        exact h8f
      have hx9 : (Strobes.cwDbgOff s.cq.pendingAddr == BitVec.ofNat 32 19) = false := by
        rw [← d9]
        exact h9f
      rw [hx8, hx9]
      rfl
  · rw [if_neg hC]
    have h8f : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
        BitVec.ofNat 32 18)) = false := by
      by_cases h : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
          BitVec.ofNat 32 18)) = true
      · exfalso
        have hC' := rlv_drain_imp_C (Or.inl rfl) h
        exact absurd hC' hC
      · simpa using h
    have h9f : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
        BitVec.ofNat 32 19)) = false := by
      by_cases h : (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
          BitVec.ofNat 32 19)) = true
      · exfalso
        have hC' := rlv_drain_imp_C (Or.inr rfl) h
        exact absurd hC' hC
      · simpa using h
    rw [h8f, h9f]
    rfl

/-! ## 12. The value-level fields, unconditional -/

/-- The machine's two-byte `EMASK` host option, restated in the cut's
byte-strobe shape (the host decode `dbgHEH` speaks `hostOpt2`). -/
theorem emask_hostOpt_eq (s : State) (pin : Machine.PinIn) :
    Bridge.Debug.hostOpt2 (Bridge.Debug.emaskPort0 (dbgCtrlIn s pin))
        (Bridge.Debug.emaskPort1 (dbgCtrlIn s pin)) =
      (if byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 0 then
          some (0, (hwData s).toNat)
       else if byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 1 then
          some (1, (hwData s).toNat) else none) := by
  have e0 : (dbgCtrlIn s pin).hEm0 =
      byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 0 := rfl
  have e1 : (dbgCtrlIn s pin).hEm1 =
      byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 1 := rfl
  have ew : (dbgCtrlIn s pin).hWd = hwData s := rfl
  unfold Bridge.Debug.hostOpt2 Bridge.Debug.emaskPort0 Bridge.Debug.emaskPort1
  rw [e0, e1, ew]
  by_cases h0 : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 0 = true
  · have d0 : (dbgCtrlIn s pin).dWrEm0 = true := by
      rw [show (dbgCtrlIn s pin).dWrEm0 = (Strobes.hostDbg (hwDbg s)
        (dbgOff s.hostCmd.addr) Strobes.hoDbgEmask ||
          (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
            BitVec.ofNat 32 8))) from rfl, ← hostByteStrobe_emask0 s, h0]
      simp
    simp [h0, d0]
  · by_cases h1 : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "EMASK") 1 = true
    · have d1 : (dbgCtrlIn s pin).dWrEm1 = true := by
        rw [show (dbgCtrlIn s pin).dWrEm1 = (Strobes.hostDbg (hwDbg s)
          (dbgOff s.hostCmd.addr) Strobes.hoDbgEmaskPlus1 ||
            (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
              BitVec.ofNat 32 9))) from rfl, ← hostByteStrobe_emask1 s, h1]
        simp
      simp [h0, h1, d1]
    · simp [h0, h1]

/-- The machine's two-byte `RLV` host option, in the cut's byte-strobe shape. -/
theorem rlv_hostOpt_eq (s : State) (pin : Machine.PinIn) :
    Bridge.Debug.hostOpt2 (Bridge.Debug.rlvPort0 (dbgCtrlIn s pin))
        (Bridge.Debug.rlvPort1 (dbgCtrlIn s pin)) =
      (if byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0 then
          some (0, (hwData s).toNat)
       else if byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1 then
          some (1, (hwData s).toNat) else none) := by
  have e0 : (dbgCtrlIn s pin).hRlv0 =
      byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0 := rfl
  have e1 : (dbgCtrlIn s pin).hRlv1 =
      byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1 := rfl
  have ew : (dbgCtrlIn s pin).hWd = hwData s := rfl
  unfold Bridge.Debug.hostOpt2 Bridge.Debug.rlvPort0 Bridge.Debug.rlvPort1
  rw [e0, e1, ew]
  by_cases h0 : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 0 = true
  · have d0 : (dbgCtrlIn s pin).dWrRlv0 = true := by
      rw [show (dbgCtrlIn s pin).dWrRlv0 = (Strobes.hostDbg (hwDbg s)
        (dbgOff s.hostCmd.addr) Strobes.hoDbgRlv ||
          (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
            BitVec.ofNat 32 18))) from rfl, ← hostByteStrobe_rlv0 s, h0]
      simp
    simp [h0, d0]
  · by_cases h1 : byteStrobe (Machine.Util.hwAt (hwOf s) "DBG" 0 "RLV") 1 = true
    · have d1 : (dbgCtrlIn s pin).dWrRlv1 = true := by
        rw [show (dbgCtrlIn s pin).dWrRlv1 = (Strobes.hostDbg (hwDbg s)
          (dbgOff s.hostCmd.addr) Strobes.hoDbgRlvPlus1 ||
            (cwDrain s && (Strobes.cwDbgOff s.cq.pendingAddr ==
              BitVec.ofNat 32 19))) from rfl, ← hostByteStrobe_rlv1 s, h1]
        simp
      simp [h0, h1, d1]
    · simp [h0, h1]

/-- **The proposed `DbgWire` field `dbgEmaskValue`.**  The machine's next
`EMASK` (drained core byte, then host byte, §13.1) is the cut's next `EMASK`,
under `ChipRel`/`Inv`/`runRst` only.  Replaces `hEH`, `hEC`, `hESH`. -/
theorem dbgEmaskValue_of (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) :
    (machDbgNext m).emask = (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).emask :=
  emask_value_of hrel hact (by
    rw [dbgHEH s m pin hrel hinv hact]
    exact emask_hostOpt_eq s pin)
    (machCw_emask_lane hrel) (emask_host_01 s) (emask_drain_01 s)

/-- **The proposed `DbgWire` field `dbgRlvValue`.**  The machine's next `RLV`
(replay values, drained core byte, then host byte) is the cut's next `RLV`,
under `ChipRel`/`Inv`/`runRst` plus the two existing `DbgWire` fields `hwb`
(first replay slot) and `happly` (the replay apply comparison).  Replaces
`hRH`, `hRC`, `hRSH`.  `hwb` here is the *unguarded* form carried by the
current `DbgWire`; it is false on some reachable state
(`Bridge.StreamBuf.dbgHwb_unguarded_false`), and `dbgRlvValue_of_wv` below is
the WV-guarded replacement — this theorem is kept for the existing consumers. -/
theorem dbgRlvValue_of (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hwb : (Machine.Util.vget m.streams 0).wb = (streamAt s 0).wb)
    (happly : (machApplyLate m).1 =
      Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
        (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
        (dbgCtrlIn s pin).replayWord) :
    (machDbgNext m).rlv = (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).rlv :=
  rlv_value_of hrel hact hwb happly (by
    rw [dbgHRH s m pin hrel hinv hact]
    exact rlv_hostOpt_eq s pin)
    (machCw_rlv_lane hrel) (rlv_host_01 s) (rlv_drain_01 s)

/-! ## 13. The WV-guarded `RLV` value

The `RLV` path reads the first replay slot `WB` only when `apply` fires
(`Debug.Ctrl.apply` conjoins `replayValid`, `Metronome/Debug.lean:319`), and
`replayValid`'s bit 0 is the cut's `WV`
(`ChipCut.Assembly.bitAt_replayValid`, reproved locally here as
`dbg_bitAt_replayValid` because `Assembly` imports this file).  So the guarded
`WB` hypothesis is the valid one: B1's
`Bridge.StreamBuf.dbgHwb_unguarded_false` refutes the unguarded form on a
reachable state, and `Bridge.StreamBuf.dbgHwb_of_wv` proves the guarded form
from `AbsRelB`. -/

/-- `vget` of a two-element vector at index 0 is its first component. -/
theorem dbg_vget_streams_zero (m : Machine.State) :
    Machine.Util.vget m.streams 0 = m.streams[(0 : Fin 2)] := by
  simp [Machine.Util.vget]

/-- Bit 0 of the two-stream `replayValid` word is stream 0's `WV` (the local
form of `ChipCut.Assembly.bitAt_replayValid`, which cannot be imported here). -/
theorem dbg_bitAt_replayValid (s : State) (pin : Machine.PinIn) :
    Debug.bitAt (dbgCtrlIn s pin).replayValid 0 = (streamAt s 0).wv := by
  simp only [Debug.bitAt, dbgCtrlIn]
  by_cases h0 : (streamAt s 0).wv <;> by_cases h1 : (streamAt s 1).wv <;>
    simp [h0, h1]

/-- The cut's `WV` gives the machine's first replay slot from `ChipRel`
(B1's `Bridge.StreamBuf.dbgHwb_of_wv`, inlined to avoid importing
`Bridge.StreamBuf`). -/
theorem dbg_wb_of_wv {s : State} {m : Machine.State} (hrel : ChipRel s m)
    (hwv : (streamAt s 0).wv = true) :
    (Machine.Util.vget m.streams 0).wb = (streamAt s 0).wb := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbuf⟩ := hrel.streams (0 : Fin 2)
  rw [dbg_vget_streams_zero]
  exact (hbuf.wb_of_wv hwv).symm

/-- **The proposed `DbgWire` field `dbgRlvValue`, WV-guarded.**  Same conclusion
as `dbgRlvValue_of`, with the (reachable) guarded `WB` hypothesis
`(streamAt s 0).wv = true → machine WB = cut WB` in place of the unguarded one.
Uses `ChipRel`/`Inv`/`runRst` and the existing `DbgWire.happly`; the guarded
`WB` fact is derived here from `ChipRel.streams` (`dbg_wb_of_wv`).  Replaces
`hRH`, `hRC`, `hRSH` together with the WV-guarded `hwb`. -/
theorem dbgRlvValue_of_wv (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hwb : (streamAt s 0).wv = true →
      (Machine.Util.vget m.streams 0).wb = (streamAt s 0).wb)
    (happly : (machApplyLate m).1 =
      Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
        (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
        (dbgCtrlIn s pin).replayWord) :
    (machDbgNext m).rlv = (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).rlv := by
  refine rlv_value_of_apply hrel hact ?_ happly (by
    rw [dbgHRH s m pin hrel hinv hact]
    exact rlv_hostOpt_eq s pin)
    (machCw_rlv_lane hrel) (rlv_host_01 s) (rlv_drain_01 s)
  intro hA
  have hwv : (streamAt s 0).wv = true := by
    have hv : Debug.bitAt (dbgCtrlIn s pin).replayValid 0 = true := by
      rw [happly] at hA
      unfold Debug.Ctrl.apply at hA
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hA
      exact hA.1.2
    rw [← dbg_bitAt_replayValid s pin]
    exact hv
  exact hwb hwv

end Metronome.ChipCut.Discharge.DbgMapWire
