import Metronome.ChipCut.Discharge.DbgMapWire

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Metronome.ChipCut.Discharge.DbgMapWire

open Metronome

theorem isCfgAddr_false_of (a : Nat) (h : 0x21E0 ≤ a) :
    Machine.Config.isCfgAddr a = false := by
  rcases hc : Machine.Config.isCfgAddr a with _ | _
  · rfl
  · have hw := Bridge.CfgWrite.isCfgAddr_window a hc
    omega

/-- The fields of a located host-map address. -/
theorem hostLocate_fields {a : Nat} {blk : String} {inst : Nat} {reg : String} {b : Nat}
    (hmap : (Machine.hostLocate a).map (fun l => (l.blk, l.inst, l.reg, l.byte))
      = some (blk, inst, reg, b)) :
    ∃ l : Machine.HostLoc, Machine.hostLocate a = some l ∧ l.blk = blk ∧ l.inst = inst ∧
      l.reg = reg ∧ l.byte = b := by
  obtain ⟨l, hl, hf⟩ := Option.map_eq_some_iff.mp hmap
  exact ⟨l, hl, by simpa using congrArg (·.1) hf, by simpa using congrArg (·.2.1) hf,
    by simpa using congrArg (·.2.2.1) hf, by simpa using congrArg (·.2.2.2) hf⟩

theorem hostLocate_emask0 :
    (Machine.hostLocate 0x2468).map (fun l => (l.blk, l.inst, l.reg, l.byte))
      = some ("DBG", 0, "EMASK", (0 : Nat)) := by decide

theorem hostLocate_emask1 :
    (Machine.hostLocate 0x2469).map (fun l => (l.blk, l.inst, l.reg, l.byte))
      = some ("DBG", 0, "EMASK", (1 : Nat)) := by decide

theorem hostLocate_rlv0 :
    (Machine.hostLocate 0x2472).map (fun l => (l.blk, l.inst, l.reg, l.byte))
      = some ("DBG", 0, "RLV", (0 : Nat)) := by decide

theorem hostLocate_rlv1 :
    (Machine.hostLocate 0x2473).map (fun l => (l.blk, l.inst, l.reg, l.byte))
      = some ("DBG", 0, "RLV", (1 : Nat)) := by decide

theorem machCw_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) :
    machCw m = (if !s.freeze.frz && s.cq.pending &&
        !(s.cq.pending && Machine.Config.isCfgAddr s.cq.pendingAddr.toNat) &&
        Machine.cwRuntimeTarget s.cq.pendingAddr.toNat then
      some ⟨s.cq.pendingAddr.toNat, s.cq.pendingData.toNat,
        Machine.hostLocate s.cq.pendingAddr.toNat⟩ else none) := by
  unfold machCw
  dsimp only
  unfold Machine.cwNext
  dsimp only
  rw [show m.cw.cwv = s.cq.pending from hrel.cw.cwv,
      show m.cw.cwqa = s.cq.pendingAddr from hrel.cw.cwqa,
      show m.cw.cwqd = s.cq.pendingData from hrel.cw.cwqd,
      show m.dbg.frz = s.freeze.frz from DbgRel.frz_eq hrel.dbg]

/-! ## EMASK, host byte 1 + drained core byte 0 -/

theorem wit_cwDrain (cont : Contents) : cwDrain (witState cont 0x2469 0x2468) = true := by
  have hic : Machine.Config.isCfgAddr ((0x2468 : BitVec 16).toNat) = false :=
    isCfgAddr_false_of _ (by decide)
  simp only [cwDrain, witState, witCq, resetState, CoreCtl.freezeReset, Bool.not_false,
    Bool.true_and, hic]

theorem wit_cw (cont : Contents) :
    machCw (absChip (witState cont 0x2469 0x2468)) =
      some ⟨0x2468, 0x3C, Machine.hostLocate 0x2468⟩ := by
  have hic : Machine.Config.isCfgAddr ((0x2468 : BitVec 16).toNat) = false :=
    isCfgAddr_false_of _ (by decide)
  have hrt : Machine.cwRuntimeTarget ((0x2468 : BitVec 16).toNat) = true := by decide
  have hcond : (!(witState cont 0x2469 0x2468).freeze.frz &&
      (witState cont 0x2469 0x2468).cq.pending &&
      !((witState cont 0x2469 0x2468).cq.pending &&
        Machine.Config.isCfgAddr (witState cont 0x2469 0x2468).cq.pendingAddr.toNat) &&
      Machine.cwRuntimeTarget (witState cont 0x2469 0x2468).cq.pendingAddr.toNat) = true := by
    simp only [witState, witCq, resetState, CoreCtl.freezeReset, Bool.not_false, Bool.true_and]
    rw [hic, hrt]
    rfl
  rw [machCw_eq (wit_chipRel _ _ _), if_pos hcond]
  rfl

theorem wit_hwAt_host_emask1 (cont : Contents) :
    Machine.Util.hwAt (hwOf (witState cont 0x2469 0x2468)) "DBG" 0 "EMASK" = some (1, 0x5A) := by
  obtain ⟨l, hl, hb, hi, hr, hby⟩ := hostLocate_fields hostLocate_emask1
  have hl' : Machine.hostLocate ((0x2469 : BitVec 16).toNat) = some l := by simpa using hl
  simp only [hwOf, witState, witHostCmd, if_pos, hl', Machine.Util.hwAt, hb, hi, hr, hby,
    Bool.and_self, if_true]

theorem wit_hwAt_core_emask0 (cont : Contents) :
    Machine.Util.hwAt (machCw (absChip (witState cont 0x2469 0x2468))) "DBG" 0 "EMASK" =
      some (0, 0x3C) := by
  obtain ⟨l, hl, hb, hi, hr, hby⟩ := hostLocate_fields hostLocate_emask0
  rw [wit_cw cont]
  simp only [Machine.Util.hwAt, hl, hb, hi, hr, hby, Bool.and_self, if_true]

theorem wit_hEm0 (cont : Contents) :
    hwIsSome (witState cont 0x2469 0x2468) "DBG" 0 "EMASK" = true := by
  simp [hwIsSome, wit_hwAt_host_emask1]

theorem wit_hEm1 (cont : Contents) :
    byteStrobe (Machine.Util.hwAt (hwOf (witState cont 0x2469 0x2468)) "DBG" 0 "EMASK") 1 = true := by
  simp [byteStrobe, wit_hwAt_host_emask1]

theorem wit_dWrEm0 (cont : Contents) :
    Strobes.dbgByteWrite (hwDbg (witState cont 0x2469 0x2468))
      (dbgOff (witState cont 0x2469 0x2468).hostCmd.addr)
      (cwDrain (witState cont 0x2469 0x2468))
      (witState cont 0x2469 0x2468).cq.pendingAddr Strobes.hoDbgEmask = true := by
  have hc := wit_cwDrain cont
  have hh : Strobes.hostDbg (hwDbg (witState cont 0x2469 0x2468))
      (dbgOff (witState cont 0x2469 0x2468).hostCmd.addr) Strobes.hoDbgEmask = false := by
    simp [Strobes.hostDbg, hwDbg, dbgOff, witState, witHostCmd]
  have hoff : (Strobes.cwDbgOff (witState cont 0x2469 0x2468).cq.pendingAddr ==
      BitVec.ofNat 32 Strobes.hoDbgEmask) = true := by
    simp [witState, witCq, Strobes.cwDbgOff, Strobes.haDbgBase, Strobes.hoDbgEmask]
  simp only [Strobes.dbgByteWrite, hc, hh, Bool.false_or, Bool.true_and, hoff]

theorem wit_dWrEm1 (cont : Contents) :
    Strobes.dbgByteWrite (hwDbg (witState cont 0x2469 0x2468))
      (dbgOff (witState cont 0x2469 0x2468).hostCmd.addr)
      (cwDrain (witState cont 0x2469 0x2468))
      (witState cont 0x2469 0x2468).cq.pendingAddr Strobes.hoDbgEmaskPlus1 = true := by
  have hh : Strobes.hostDbg (hwDbg (witState cont 0x2469 0x2468))
      (dbgOff (witState cont 0x2469 0x2468).hostCmd.addr) Strobes.hoDbgEmaskPlus1 = true := by
    simp [Strobes.hostDbg, hwDbg, dbgOff, inDbg, witState, witHostCmd]
  simp only [Strobes.dbgByteWrite, hh, Bool.true_or]

theorem wit_hostOpt2_emask (cont : Contents) (pin : Machine.PinIn) :
    Bridge.Debug.hostOpt2 (Bridge.Debug.emaskPort0 (dbgCtrlIn (witState cont 0x2469 0x2468) pin))
      (Bridge.Debug.emaskPort1 (dbgCtrlIn (witState cont 0x2469 0x2468) pin)) =
      some (0, 0x5A) := by
  have h0 := wit_dWrEm0 cont
  have h1 := wit_hEm0 cont
  simp only [Bridge.Debug.hostOpt2, Bridge.Debug.emaskPort0, Bridge.Debug.emaskPort1,
    Bridge.Debug.Port, dbgCtrlIn]
  rw [h0, h1]
  simp [hwData, witState, witHostCmd]

theorem wit_coreOpt2_emask (cont : Contents) (pin : Machine.PinIn) :
    Bridge.Debug.coreOpt2 (Bridge.Debug.emaskPort0 (dbgCtrlIn (witState cont 0x2469 0x2468) pin))
      (Bridge.Debug.emaskPort1 (dbgCtrlIn (witState cont 0x2469 0x2468) pin)) = none := by
  have h0 := wit_dWrEm0 cont
  have h1 := wit_hEm0 cont
  have h2 := wit_dWrEm1 cont
  have h3 := wit_hEm1 cont
  simp only [Bridge.Debug.coreOpt2, Bridge.Debug.emaskPort0, Bridge.Debug.emaskPort1,
    Bridge.Debug.Port, dbgCtrlIn]
  rw [h0, h1, h2, h3]
  rfl

end Metronome.ChipCut.Discharge.DbgMapWire
