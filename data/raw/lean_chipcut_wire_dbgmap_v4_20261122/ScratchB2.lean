import Metronome.ChipCut.Discharge.StreamDbg

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Metronome.ChipCut.Discharge

open Metronome

/-! ## A witness family: host write of one DBG register byte and a drained core
write of another (or the same) byte in one cycle. -/

def witHostCmd (a : BitVec 16) : HostCmd.State :=
  { phase := HostCmd.ST_DATA, bitc := 0, rx := 0, isRd := false, addr := a, wr := true,
    wdata := 0x5A, rd := false, rack := false, cmd := 0x02 }

def witHostRead (a : BitVec 16) : HostRead.State :=
  { phase := HostCmd.ST_DATA, bitc := 0, rx := 0, isRd := false, addr := a, wr := true,
    wdata := 0x5A, rd := false, rack := false, tx := 0, rackv := 0 }

def witCq (q : BitVec 16) : CoreQueue.State :=
  { addr := 0, pending := true, pendingAddr := q, pendingData := 0x3C, overrun := false }

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

theorem wit_chipRel (cont : Contents) (ha hq : BitVec 16) :
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
    exact bankRel_reset _
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

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

end Metronome.ChipCut.Discharge
