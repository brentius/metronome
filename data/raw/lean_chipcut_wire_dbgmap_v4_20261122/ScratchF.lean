import Metronome.ChipCut.Discharge.DbgMapWire

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Metronome.ChipCut.Discharge.DbgMapWire

open Metronome

/-- No `DBG`-window address is a configuration address. -/
theorem isCfgAddr_false_of (a : Nat) (h : 0x21E0 ≤ a) :
    Machine.Config.isCfgAddr a = false := by
  rcases hc : Machine.Config.isCfgAddr a with _ | _
  · rfl
  · have hw := Bridge.CfgWrite.isCfgAddr_window a hc
    omega

/-- The machine's drained core write (`cwNext`'s runtime output) is the cut's
pending queue write (in the machine's own drain form). -/
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

/-- The witness state's drained core write: the queue's pending `0x3C` write to
`EMASK` byte 0. -/
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

end Metronome.ChipCut.Discharge.DbgMapWire
