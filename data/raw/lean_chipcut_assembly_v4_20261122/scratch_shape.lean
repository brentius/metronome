import Metronome.ChipCut.Discharge.CoreCombWire
import Metronome.Bridge.StreamBuf

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Metronome.ChipCut.Discharge

open Metronome

/-- `stateMode` is the bridge's `modeOf` of the cycle's input. -/
theorem stateMode_eq_modeOf (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    stateMode s k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val) :=
  (stateMode_eq s k).trans (absMode_eq s pin k)

/-- A `CAP = 0` stream's mode is 0 or 1. -/
theorem stateMode_cap_false (s : State) (pin : Machine.PinIn) (k : Fin 2)
    (hk : (k.val == 0) = false) : stateMode s k = 0 ∨ stateMode s k = 1 := by
  rw [stateMode_eq_modeOf, hk]
  unfold Bridge.StreamB.modeOf
  simp only [Bool.false_and, Bool.false_eq_true, ite_false]
  have hcfgmk : (streamIn s pin k).cfgMode = ((Machine.cfgView s.cont.cfg).streams[k]).rx := by
    show ((Machine.cfgView s.cont.cfg).streams[k.val]!).rx = _
    rw [vec_get!_eq_get _ _ k.isLt]
  rw [hcfgmk]
  split <;> simp

/-- The cut's next stream is `Stream.step` on its input record. -/
theorem streamAt_activeStep (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    streamAt (activeStep s pin) k.val =
      Stream.step (k.val == 0) (streamAt s k.val) (streamIn s pin k.val) := by
  rw [streamAt_fin]
  have hvec : (activeStep s pin).streams = Vector.ofFn fun i : Fin 2 =>
      Stream.step (i.val == 0) (streamAt s i.val) (streamIn s pin i.val) := rfl
  rw [hvec]
  simp only [vec_get_ofFn']

/-- A clear `LD` and `NV` give a clear next `NV`. -/
theorem nv_step_zero (s : Stream.State) (i : Stream.Input) (hld : s.ld = false)
    (hnv : s.nv = false) : (Stream.step true s i).nv = false := by
  show Stream.nvNext true s i = false
  unfold Stream.nvNext
  rw [hld, hnv]
  simp

/-- The per-stream mode/shape invariant: `ShapeOK` and "a valid second slot only
in replay", indexed by the cut's current mode. -/
def streamShapeInv (s : State) : Prop :=
  ∀ k : Fin 2, Bridge.StreamBuf.ShapeModeOK (stateMode s k) (streamAt s k.val)

theorem streamShapeInv_reset (cont : Contents) : streamShapeInv (resetState cont) := by
  intro k
  rw [show streamAt (resetState cont) k.val = Stream.resetState from by
    rw [streamAt_fin]; simp [resetState]]
  exact Bridge.StreamBuf.shapeModeOK_reset _

theorem streamShapeInv_step (s : State) (pin : Machine.PinIn) (h : streamShapeInv s)
    (hq : stream_mode_quiet s pin) : streamShapeInv (step s pin) := by
  intro k
  by_cases hact : runRst s pin = true
  · rw [show step s pin = activeStep s pin from by simp [step, hact]]
    rw [streamAt_activeStep s pin k]
    have hk := h k
    by_cases hch : stateMode (activeStep s pin) k = stateMode s k
    · -- the mode does not change
      rw [hch]
      by_cases hk0 : (k.val == 0) = true
      · rw [hk0]
        have hsm : stateMode s k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val) :=
          stateMode_eq_modeOf s pin k
        rw [hsm, hk0]
        exact Bridge.StreamBuf.shapeModeOK_step (streamAt s k.val) (streamIn s pin k.val)
          (stateMode s k) hk (Or.inl (by rw [hsm, hk0]))
      · have hkf : (k.val == 0) = false := by
          cases h' : (k.val == 0) <;> simp_all
        rw [hkf]
        obtain ⟨hshape, hnv3⟩ := hk
        have hnvf : (streamAt s k.val).nv = false := by
          cases hn : (streamAt s k.val).nv
          · rfl
          · have h3 := hnv3 hn
            rcases stateMode_cap_false s pin k hkf with h0 | h1 <;> omega
        refine ⟨Bridge.StreamBuf.shapeOK_step_cap_false _ _ hnvf, ?_⟩
        intro hbad
        rw [Bridge.StreamBuf.nv_step_cap_false] at hbad
        rw [hnvf] at hbad
        exact Bool.noConfusion hbad
    · -- the mode changes: the quietness clears all the live registers
      have hch' : stateMode (step s pin) k ≠ stateMode s k := by
        rw [show step s pin = activeStep s pin from by simp [step, hact]]
        exact hch
      obtain ⟨hld0, -, hwv0, hnv0, -, -⟩ := hq k hch'
      have hnv' : (Stream.step (k.val == 0) (streamAt s k.val)
          (streamIn s pin k.val)).nv = false := by
        by_cases hk0 : (k.val == 0) = true
        · rw [hk0]
          exact nv_step_zero _ _ hld0 hnv0
        · have hkf : (k.val == 0) = false := by cases h' : (k.val == 0) <;> simp_all
          rw [hkf, Bridge.StreamBuf.nv_step_cap_false, hnv0]
      by_cases hk0 : (k.val == 0) = true
      · rw [hk0]
        rw [hk0] at hnv'
        have hs := Bridge.StreamBuf.shapeModeOK_step (streamAt s k.val)
          (streamIn s pin k.val) (stateMode s k) hk (Or.inr ⟨hwv0, hnv0⟩)
        obtain ⟨hshape, -⟩ := hs
        refine ⟨hshape, ?_⟩
        intro hbad
        rw [hnv'] at hbad
        exact Bool.noConfusion hbad
      · have hkf : (k.val == 0) = false := by cases h' : (k.val == 0) <;> simp_all
        rw [hkf]
        rw [hkf] at hnv'
        refine ⟨Bridge.StreamBuf.shapeOK_step_cap_false _ _ hnv0, ?_⟩
        intro hbad
        rw [hnv'] at hbad
        exact Bool.noConfusion hbad
  · rw [show step s pin = resetChip s pin from by simp [step, hact]]
    rw [show streamAt (resetChip s pin) k.val = Stream.resetState from by
      rw [streamAt_fin]; simp [resetChip, resetState]]
    exact Bridge.StreamBuf.shapeModeOK_reset _

theorem streamShapeInv_trace (pins : Nat → Machine.PinIn) (cont : Contents)
    (hq : ∀ n, stream_mode_quiet (cutStateAt pins (resetState cont) n) (pins n)) :
    ∀ n, streamShapeInv (cutStateAt pins (resetState cont) n) := by
  intro n
  induction n with
  | zero => exact streamShapeInv_reset cont
  | succ n ih =>
    rw [cutStateAt_succ]
    exact streamShapeInv_step _ _ ih (hq n)

end Metronome.ChipCut.Discharge
