import Metronome.ChipCut.Discharge.CoreCombWire
import Metronome.Bridge.StreamBuf

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 2000000

namespace Metronome.ChipCut.Discharge

open Metronome

/-! ## Helpers -/

/-- The machine's mode at a related state is the cut's `stateMode`. -/
theorem machMode_eq_stateMode (s : State) (m : Machine.State) (hrel : ChipRel s m) (k : Fin 2) :
    machMode m k = stateMode s k := by
  obtain ⟨-, -, -, -, -, hcen, hrpl, -, -, -, -⟩ := hrel.dbg
  simp only [machMode, stateMode, Machine.streamMode, hrel.cfg, hcen, hrpl]

/-- `stateMode` is the bridge's `modeOf` of the cycle's input. -/
theorem stateMode_modeOf (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    stateMode s k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val) :=
  (stateMode_eq s k).trans (absMode_eq s pin k)

/-- The cut's next stream is `Stream.step` on its input record. -/
theorem streamAt_activeStep' (s : State) (pin : Machine.PinIn) (k : Fin 2) :
    streamAt (activeStep s pin) k.val =
      Stream.step (k.val == 0) (streamAt s k.val) (streamIn s pin k.val) := by
  rw [streamAt_fin, activeStep_streams]

/-- A clear `LD` and `RQ` give a clear next `LD`. -/
theorem ldNext_false (cap : Bool) (st : Stream.State) (i : Stream.Input)
    (hres : i.resetN = true) (hld : st.ld = false) (hrq : st.rq = false) :
    Stream.ldNext cap st i = false := by
  unfold Stream.ldNext
  simp only [hres, hld, hrq, Bool.not_true, Bool.false_eq_true, if_false, Bool.false_and,
    Bool.and_true, ite_self]

/-! ## The capture invariant -/

/-- The mode-indexed capture invariant at the chip level: at every stream, the
machine's replay/capture buffer record agrees with the cut's while a word is
pending in **capture** mode, and the capture stream has no read in flight.  The
index is the cut's current mode `stateMode s k`, i.e. the mode of the cycle that
produced `s` (a pure state function). -/
def CapInv (s : State) (m : Machine.State) : Prop :=
  ∀ k : Fin 2, Bridge.StreamBuf.CapModeOK (stateMode s k) (streamAt s k.val) m.streams[k]

/-- The reset pair of the chip trace theorem satisfies `CapInv`. -/
theorem capInv_reset (cont : Contents) :
    CapInv (resetState cont) (absChip (resetState cont)) := by
  intro k
  have hS : streamAt (resetState cont) k.val = Stream.resetState := by
    rw [streamAt_fin]
    simp [resetState]
  have hM : (absChip (resetState cont)).streams[k] = (default : Machine.StreamSt) := by
    rw [absChip_streams, hS]
    decide
  rw [hS, hM]
  exact Bridge.StreamBuf.capModeOK_reset _

/-- **`CapInv` is preserved by one product step** (active and reset branches),
from the per-stream input agreement that `premise_streams` also consumes. -/
theorem capInv_step_of_input (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hcap : CapInv s m)
    (hin : ∀ k : Fin 2, StreamInputAgree m (streamAt s k.val) (streamIn s pin k.val) k)
    (hq : stream_mode_quiet s pin) :
    CapInv (step s pin) (Machine.step m pin) := by
  intro k
  by_cases hact : runRst s pin = true
  · have hstep : step s pin = activeStep s pin := by simp [step, hact]
    rw [hstep]
    by_cases hch : stateMode (activeStep s pin) k = stateMode s k
    · -- the mode is unchanged: B1's `capModeOK_step` at the cycle's mode
      have hmode : machMode m k =
          Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val) := by
        rw [machMode_eq_stateMode s m hrel k, stateMode_modeOf s pin k]
      have hcf : (Machine.cfgView m.cfg).streams[k] =
          Bridge.StreamB.cfgOf (streamIn s pin k.val) := by
        rw [hrel.cfg]
        exact (cfgOf_streamIn s pin k).symm
      have hnext : (Machine.step m pin).streams[k] =
          Machine.streamNext (Bridge.StreamB.cfgOf (streamIn s pin k.val))
            (Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val)) m.streams[k]
            (Bridge.StreamB.absIn (k.val == 0) (streamAt s k.val) (streamIn s pin k.val))
            (streamIn s pin k.val).frz := by
        rw [streamsNext_eq s m pin hrel hact k hcf hmode (hin k)]
        exact congrArg (fun b => Machine.streamNext (Bridge.StreamB.cfgOf (streamIn s pin k.val))
          (Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val)) m.streams[k]
          (Bridge.StreamB.absIn (k.val == 0) (streamAt s k.val) (streamIn s pin k.val)) b)
          (DbgRel.frz_eq hrel.dbg)
      rw [hch, stateMode_modeOf s pin k, streamAt_activeStep', hnext]
      have hnew := Bridge.StreamBuf.capModeOK_step (k.val == 0) (streamAt s k.val)
        (streamIn s pin k.val) m.streams[k] (Bridge.StreamB.cfgOf (streamIn s pin k.val))
        (stateMode s k) (hrel.streams k) (hcap k) hact rfl
        (Or.inl (stateMode_modeOf s pin k).symm)
      exact hnew
    · -- the mode changes: the quietness leaves the stream idle on both sides
      obtain ⟨hld0, hrq0, -, -, -, hpv0'⟩ := hq k (by rw [hstep]; exact hch)
      have hres : (streamIn s pin k.val).resetN = true := hact
      have hpv0'' : (streamAt (activeStep s pin) k.val).pv = false := by
        rw [← hstep]
        exact hpv0'
      refine ⟨?_, ?_⟩
      · intro _
        rw [streamAt_activeStep']
        exact ldNext_false _ _ _ hres hld0 hrq0
      · intro _ hpv'
        rw [hpv0''] at hpv'
        exact Bool.noConfusion hpv'
  · -- the reset edge: the cut loads `Stream.resetState`, whose `PV` is clear
    have hstep : step s pin = resetChip s pin := by simp [step, hact]
    rw [hstep]
    have hS : streamAt (resetChip s pin) k.val = Stream.resetState := by
      rw [streamAt_fin]
      simp [resetChip, resetState]
    rw [hS]
    refine ⟨?_, ?_⟩ <;> simp [Stream.resetState]

/-- **`CapInv` is preserved by one product step** in the packaged form (the
`StreamWire` bundle supplies the input agreement; `Inv s` is kept for signature
compatibility with the other discharge invariants and is not consumed). -/
theorem capInv_step (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hcap : CapInv s m)
    (hw : StreamWire s m pin) (hq : stream_mode_quiet s pin) :
    CapInv (step s pin) (Machine.step m pin) :=
  capInv_step_of_input s m pin hrel hcap hw.input hq

/-- `CapInv` at every cycle of the product trace (given the per-cycle relation
and input agreement, e.g. from `trace_refines` and `premises_of`). -/
theorem capInv_trace (pins : Nat → Machine.PinIn) (cont : Contents)
    (hrel : ∀ n, ChipRel (cutStateAt pins (resetState cont) n)
      (machineStateAt pins (absChip (resetState cont)) n))
    (hin : ∀ n, ∀ k : Fin 2,
      StreamInputAgree (machineStateAt pins (absChip (resetState cont)) n)
        (streamAt (cutStateAt pins (resetState cont) n) k.val)
        (streamIn (cutStateAt pins (resetState cont) n) (pins n) k.val) k)
    (hq : ∀ n, stream_mode_quiet (cutStateAt pins (resetState cont) n) (pins n)) :
    ∀ n, CapInv (cutStateAt pins (resetState cont) n)
      (machineStateAt pins (absChip (resetState cont)) n) := by
  intro n
  induction n with
  | zero => exact capInv_reset cont
  | succ n ih =>
    rw [cutStateAt_succ, machineStateAt_succ]
    exact capInv_step_of_input _ _ _ (hrel n) ih (hin n) (hq n)

end Metronome.ChipCut.Discharge
