import Metronome.ChipCut.Discharge.HostPinWire
import Metronome.ChipCut.Discharge.MoveFabricKeyed

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Metronome.ChipCut.Discharge.PremiseWire

open Metronome

/-! ## 1. The group-packing identity -/

theorem six_slice (x0 x1 x2 x3 x4 x5 : BitVec 5) (q : Nat) (hq : q < 6) :
    CoreCtl.slice (BitVec.setWidth 30 x0 ||| BitVec.shiftLeft (BitVec.setWidth 30 x1) 5 |||
      BitVec.shiftLeft (BitVec.setWidth 30 x2) 10 |||
      BitVec.shiftLeft (BitVec.setWidth 30 x3) 15 |||
      BitVec.shiftLeft (BitVec.setWidth 30 x4) 20 |||
      BitVec.shiftLeft (BitVec.setWidth 30 x5) 25) (5 * q) 5
    = (match q with | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | 4 => x4 | _ => x5) := by
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold CoreCtl.slice
    bv_decide

theorem mapOfWith_slice (tab : BitVec 320) (dst : BitVec 36) (q : Nat) (hq : q < 6) :
    CoreCtl.slice (Moves.mapOfWith tab dst) (5 * q) 5 =
      Moves.dgLookupAt tab (CoreCtl.slice dst (6 * q) 6) :=
  six_slice (Moves.dgLookupAt tab (CoreCtl.slice dst 0 6))
    (Moves.dgLookupAt tab (CoreCtl.slice dst 6 6))
    (Moves.dgLookupAt tab (CoreCtl.slice dst 12 6))
    (Moves.dgLookupAt tab (CoreCtl.slice dst 18 6))
    (Moves.dgLookupAt tab (CoreCtl.slice dst 24 6))
    (Moves.dgLookupAt tab (CoreCtl.slice dst 30 6)) q hq

theorem grpPacked_holds (s : State) (pin : Machine.PinIn) :
    MoveFabricKeyed.GrpPacked s pin := by
  intro q hq
  have hg : ((movBundle s pin).get q).group = CoreCtl.slice (mvGrp s pin) (5 * q) 5 :=
    MoveFabricKeyed.bundle_grp (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
      (mvXl s) (mvXt s) q hq
  have hd : ((movBundle s pin).get q).dst = CoreCtl.slice (mvDst s pin) (6 * q) 6 :=
    MoveFabric.bundle_dst (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
      (mvXl s) (mvXt s) q hq
  rw [hg, hd]
  exact mapOfWith_slice Moves.dgMapLiteral (mvDst s pin) q hq

/-! ## 2. AMBIG 19 -/

theorem hostCfgOf_isSome_wr (s : State) (h : (hostCfgOf s).isSome = true) :
    s.hostCmd.wr = true := by
  cases hw : s.hostCmd.wr <;> simp [hostCfgOf, hwOf, hw] at h

theorem wrNext_completing (s : HostCmd.State) (i : HostCmd.Input)
    (h : HostCmd.wrNext s i = true) : HostCmd.completing s i = true := by
  unfold HostCmd.wrNext at h
  exact (Bool.and_eq_true.mp (Bool.and_eq_true.mp (Bool.and_eq_true.mp h).2).2).1

theorem completing_bitc (s : HostCmd.State) (i : HostCmd.Input)
    (h : HostCmd.completing s i = true) : s.bitc = 7 := by
  unfold HostCmd.completing at h
  have hb : (s.bitc == 7) = true := (Bool.and_eq_true.mp h).2
  simpa using hb

theorem cwH19_step (s : State) (pin : Machine.PinIn) (hpinv : HostPinInv s) :
    ¬ ((step s pin).arb.heldValid = true ∧
      (hostCfgOf (step s pin)).isSome = true) := by
  rintro ⟨hheld, hcfg⟩
  by_cases hact : runRst s pin = true
  · rw [step, if_pos hact] at hheld hcfg
    have hheld' := hheld
    rw [show ((activeStep s pin).arb).heldValid =
      (Config.step s.arb (arbIn s)).next.heldValid from rfl,
      Config.heldValid_next] at hheld'
    have hhost : (arbIn s).hostValid = true :=
      (Bool.and_eq_true.mp (Bool.and_eq_true.mp hheld').2).2
    have hwr : s.hostCmd.wr = true :=
      hostCfgOf_isSome_wr s (by simpa [arbIn, Bridge.CfgWrite.cfgIn] using hhost)
    have h0 : s.hostCmd.bitc = 0 := hpinv.wrBitc hwr
    have hwr' : HostCmd.wrNext s.hostCmd (hostCmdIn s pin) = true :=
      hostCfgOf_isSome_wr (activeStep s pin) hcfg
    have h7 : s.hostCmd.bitc = 7 :=
      completing_bitc s.hostCmd (hostCmdIn s pin) (wrNext_completing _ _ hwr')
    rw [h0] at h7
    exact absurd h7 (by decide)
  · rw [step, if_neg hact] at hheld
    simp [resetChip, resetState] at hheld

theorem cwH19_reset (cont : Contents) :
    ¬ ((resetState cont).arb.heldValid = true ∧
      (hostCfgOf (resetState cont)).isSome = true) := by
  simp [resetState]

theorem hostPinInv_trace (pins : Nat → Machine.PinIn) (cont : Contents) :
    ∀ n, HostPinInv (cutStateAt pins (resetState cont) n)
  | 0 => hostPinInv_reset cont
  | n + 1 => by
    rw [cutStateAt_succ]
    exact hostPinInv_step _ _ (hostPinInv_trace pins cont n)

theorem cwH19_trace (pins : Nat → Machine.PinIn) (cont : Contents) :
    ∀ n, ¬ ((cutStateAt pins (resetState cont) n).arb.heldValid = true ∧
      (hostCfgOf (cutStateAt pins (resetState cont) n)).isSome = true)
  | 0 => cwH19_reset cont
  | n + 1 => by
    rw [cutStateAt_succ]
    exact cwH19_step _ _ (hostPinInv_trace pins cont n)

end Metronome.ChipCut.Discharge.PremiseWire
