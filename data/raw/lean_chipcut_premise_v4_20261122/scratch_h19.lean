import Metronome.ChipCut.Discharge.HostPinWire

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Metronome.ChipCut.Discharge.PremiseWire

open Metronome

theorem and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp_all

theorem hostCfgOf_isSome_wr (s : State) (h : (hostCfgOf s).isSome = true) :
    s.hostCmd.wr = true := by
  cases hw : s.hostCmd.wr with
  | true => rfl
  | false => simp [hostCfgOf, hwOf, hw] at h

theorem wrNext_false (s : HostCmd.State) (i : HostCmd.Input)
    (h : HostCmd.completing s i = false) : HostCmd.wrNext s i = false := by
  unfold HostCmd.wrNext
  rw [h]
  simp

theorem wrNext_completing (s : HostCmd.State) (i : HostCmd.Input)
    (h : HostCmd.wrNext s i = true) : HostCmd.completing s i = true := by
  cases hc : HostCmd.completing s i with
  | true => rfl
  | false =>
    rw [wrNext_false s i hc] at h
    exact absurd h (by decide)

theorem completing_bitc (s : HostCmd.State) (i : HostCmd.Input)
    (h : HostCmd.completing s i = true) : s.bitc = 7 := by
  unfold HostCmd.completing at h
  have hb : (s.bitc == 7) = true := and_right h
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
    have hhost : (arbIn s).hostValid = true := and_right (and_right hheld')
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
