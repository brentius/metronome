/-
# W5: the chip-level capture invariant `CapInv`

This file closes the last `WB`-slot residual of the ChipCut discharge: the
capture-mode write-buffer agreement that `contents_open_req_wb` (`CoreCombWire`
§11) takes as its premise.  `Bridge.StreamBuf` proves the *stream-level* step
(`capModeOK_step`); the missing piece is the chip-level trace invariant, in the
`ShapeModeOK` pattern of `Assembly.lean`:

* `CapInv s m := ∀ k, CapModeOK (stateMode s k) (streamAt s k) m.streams[k]` —
  the mode index is the cut's current mode (a pure state function, the mode of
  the cycle that produced the state);
* `capInv_reset` at the trace's reset pair, `capInv_step` for one product step
  (reset branch + active branch) under `stream_mode_quiet`, `capInv_trace` along
  the product trace;
* the consumer: `contentsWb_of_capInv` (the mode-2 projection, with `.symm` to
  the machine-first direction the request congruence takes) plus a mode-aware
  replacement `contents_open_req_cap` of `contents_open_req_wb`, which needs
  `WB` only in mode 2 because `Machine.streamReq`'s only `WB` reader is the
  capture `wrWord` (`streamReq_congr_cap`).

Nothing outside this file is edited.  Every goal is closed (the axiom dump in
`data/raw/lean_chipcut_captrace_v4_20261122/axioms.txt` shows only
`propext`/`Classical.choice`/`Quot.sound`) and nothing is decided natively.  The
only extra hypothesis of the step over the requested signature is the per-stream
input agreement `StreamInputAgree` (equivalently `StreamWire.input`): the
machine's next `WB` is `Machine.streamNext`'s, so the capture word of the next
state is read from the machine's own input record.  `Inv s` is kept in the
packaged signature for uniformity with the other discharge invariants and is not
consumed.
-/
import Metronome.ChipCut.Discharge.CoreCombWire
import Metronome.Bridge.StreamBuf

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 2000000

namespace Metronome.ChipCut.Discharge

open Metronome

/-! ## 1. Mode bookkeeping -/

/-- At a related pair the machine's mode is the cut's `stateMode` (both read the
configuration's `RX` bit and the two debug mode registers). -/
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

/-- A clear `LD` and `RQ` give a clear next `LD` (every branch of `Stream.ldNext`
is then `false`). -/
theorem ldNext_false (cap : Bool) (st : Stream.State) (i : Stream.Input)
    (hres : i.resetN = true) (hld : st.ld = false) (hrq : st.rq = false) :
    Stream.ldNext cap st i = false := by
  unfold Stream.ldNext
  simp only [hres, hld, hrq, Bool.not_true, Bool.false_eq_true, if_false, Bool.false_and,
    ite_self]

/-! ## 2. The capture invariant and its preservation -/

/-- The mode-indexed capture invariant at the chip level: at every stream, the
machine's write-buffer word agrees with the cut's while a word is pending in
**capture** mode, and a capture-mode stream has no read in flight.  The index is
the cut's current mode `stateMode s k`, i.e. the mode of the cycle that produced
`s` (a pure state function, as `ShapeModeOK` in `Assembly.lean`). -/
def CapInv (s : State) (m : Machine.State) : Prop :=
  ∀ k : Fin 2, Bridge.StreamBuf.CapModeOK (stateMode s k) (streamAt s k.val) m.streams[k]

/-- The reset pair of the chip trace theorem (`resetState cont` against its
canonical abstraction) satisfies `CapInv`. -/
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

/-- **`CapInv` on an active cycle.**  In the active branch the mode is compared
at the two states:

* unchanged (`stateMode (activeStep s pin) k = stateMode s k`): the goal's index
  is the cycle's `modeOf` (`stateMode_modeOf`), and B1's `capModeOK_step` applies
  at `pmode = stateMode s k` with the unchanged-mode branch of `hchange`;
* changed: `stream_mode_quiet` gives `PV = 0` now and `LD = RQ = 0`, so the next
  `LD` is clear (`ldNext_false`) and the next `PV` is clear, which makes both
  capture clauses vacuous — no machine fact is needed in this branch. -/
theorem capInv_step_active (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hact : runRst s pin = true) (hcap : CapInv s m)
    (hin : ∀ k : Fin 2, StreamInputAgree m (streamAt s k.val) (streamIn s pin k.val) k)
    (hq : stream_mode_quiet s pin) :
    CapInv (step s pin) (Machine.step m pin) := by
  intro k
  have hstep : step s pin = activeStep s pin := by simp [step, hact]
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
    exact Bridge.StreamBuf.capModeOK_step (k.val == 0) (streamAt s k.val)
      (streamIn s pin k.val) m.streams[k] (Bridge.StreamB.cfgOf (streamIn s pin k.val))
      (stateMode s k) (hrel.streams k) (hcap k) hact rfl
      (Or.inl (stateMode_modeOf s pin k).symm)
  · -- the mode changes: the quietness leaves the stream idle on both sides
    obtain ⟨hld0, hrq0, -, -, hpv0'⟩ := hq k (by rw [hstep]; exact hch)
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

/-- **`CapInv` on a reset cycle**, with no premise: the cut loads
`Stream.resetState`, whose `LD` and `PV` are clear, so both capture clauses are
vacuous whatever the machine does. -/
theorem capInv_step_reset (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hact : runRst s pin = false) (hcap : CapInv s m) :
    CapInv (step s pin) (Machine.step m pin) := by
  intro k
  have hstep : step s pin = resetChip s pin := by simp [step, hact]
  rw [hstep]
  have hS : streamAt (resetChip s pin) k.val = Stream.resetState := by
    rw [streamAt_fin]
    simp [resetChip, resetState]
  rw [hS]
  refine ⟨?_, ?_⟩ <;> simp [Stream.resetState]

/-- **`CapInv` is preserved by one product step** (active and reset branches),
from the per-stream input agreement that `premise_streams` also consumes. -/
theorem capInv_step_of_input (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hcap : CapInv s m)
    (hin : ∀ k : Fin 2, StreamInputAgree m (streamAt s k.val) (streamIn s pin k.val) k)
    (hq : stream_mode_quiet s pin) :
    CapInv (step s pin) (Machine.step m pin) := by
  by_cases hact : runRst s pin = true
  · exact capInv_step_active s m pin hrel hact hcap hin hq
  · exact capInv_step_reset s m pin (by simpa using hact) hcap

/-- **`CapInv` is preserved by one product step** in the packaged form: the
`StreamWire` bundle supplies the input agreement.  `Inv s` is kept for signature
compatibility with the other discharge invariants and is not consumed. -/
theorem capInv_step (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hcap : CapInv s m)
    (hw : StreamWire s m pin) (hq : stream_mode_quiet s pin) :
    CapInv (step s pin) (Machine.step m pin) :=
  capInv_step_of_input s m pin hrel hcap hw.input hq

/-- **`CapInv` at every cycle of the product trace**, from the per-cycle
relation (`trace_refines`) and the per-cycle input agreement, guarded by the
active cycle exactly as `trace_refines`' `hprem` is (so it composes with
`premises_of`'s `hIn`). -/
theorem capInv_trace (pins : Nat → Machine.PinIn) (cont : Contents)
    (hrel : ∀ n, ChipRel (cutStateAt pins (resetState cont) n)
      (machineStateAt pins (absChip (resetState cont)) n))
    (hin : ∀ n, runRst (cutStateAt pins (resetState cont) n) (pins n) = true → ∀ k : Fin 2,
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
    by_cases hact : runRst (cutStateAt pins (resetState cont) n) (pins n) = true
    · exact capInv_step_active _ _ _ (hrel n) hact ih (hin n hact) (hq n)
    · exact capInv_step_reset _ _ _ (by simpa using hact) ih

/-! ## 3. The consumer: the capture-slot `WB` agreement

`contents_open_req_wb` (`CoreCombWire` §11) takes the *unguarded*
`hwb : PV → m.WB = cut.WB`.  That form is **false** at reachable states
(`Bridge.StreamBuf.capWb_reachable_witness`: a receive state with a pending byte
and a stale `WB`), so it cannot be a consequence of any state relation — which
is why B1's notes record `contentsWb` as a named premise.  What `CapInv` supplies
is the mode-2 case, and that is all the request congruence needs:
`Machine.streamReq`'s only `WB` reader is the capture `wrWord`
(`streamReq_congr`, mode 2, `pv`).  `contents_open_req_cap` below is therefore
`contents_open_req_wb` with the unguarded premise replaced by the mode-2 one,
which `CapInv` discharges. -/

/-- The capture `WB` projection of `CapInv`, in the machine-first direction the
request congruence consumes. -/
theorem contentsWb_of_capInv (s : State) (m : Machine.State) (k : Fin 2)
    (hcap : CapInv s m) (hm2 : stateMode s k = 2) (hpv : (streamAt s k.val).pv = true) :
    m.streams[k].wb = (streamAt s k.val).wb :=
  ((hcap k).2 hm2 hpv).symm

/-- The other projection of `CapInv`: a capture-mode stream has no read in
flight. -/
theorem capLd_of_capInv (s : State) (m : Machine.State) (k : Fin 2)
    (hcap : CapInv s m) (hm2 : stateMode s k = 2) : (streamAt s k.val).ld = false :=
  (hcap k).1 hm2

/-- `streamReq` depends only on the mode and four stream fields, and on `WB` only
in **mode 2 while `PV`** (the capture `wrWord`) — `streamReq_congr` of
`CoreCombWire` with its unguarded `hwb` weakened to the mode-2 case. -/
theorem streamReq_congr_cap (mode : Nat) (a b : Machine.StreamSt)
    (hba : a.ba = b.ba) (hrq : a.rq = b.rq) (hpv : a.pv = b.pv)
    (hpend : a.pend = b.pend) (hwb : mode = 2 → a.pv = true → a.wb = b.wb) :
    Machine.streamReq mode a = Machine.streamReq mode b := by
  rcases mode with _ | _ | _ | _ | n
  · simp [Machine.streamReq, hba, hrq]
  · simp [Machine.streamReq, hba, hpv, hpend]
  · simp only [Machine.streamReq, hpv]
    by_cases hp : b.pv = true
    · rw [if_pos hp, if_pos hp, hba, hwb rfl (by rw [hpv]; exact hp)]
    · rw [if_neg hp, if_neg hp]
  · simp [Machine.streamReq, hba, hrq]
  · simp [Machine.streamReq, hba, hrq]

/-- The capture-mode request congruence: `mhcModesReq_abs_wb` with the `WB`
premise at the cut's capture mode only. -/
theorem mhcModesReq_abs_cap (s : State) (m : Machine.State) (pin : Machine.PinIn) (k : Fin 2)
    (hrel : ChipRel s m)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hwb : ∀ k : Fin 2, stateMode s k = 2 → (streamAt s k.val).pv = true →
      m.streams[k].wb = (streamAt s k.val).wb) :
    (mhcModesReq m pin)[k] = (mhcModesReq (absChip s) pin)[k] := by
  obtain ⟨_, _, hba, _, _, hrq, _, hpend, hpv, _, _⟩ := hrel.streams k
  have hL : (mhcModesReq m pin)[k] = Machine.streamReq (machMode m k) m.streams[k] := by
    simp [mhcModesReq, mhcModes, machMode]
  have hR : (mhcModesReq (absChip s) pin)[k] =
      Machine.streamReq (machMode (absChip s) k) ((absChip s).streams[k]) := by
    simp [mhcModesReq, mhcModes, machMode]
  rw [hL, hR, absChip_streams, hmode k, absMode_eq s pin k]
  refine streamReq_congr_cap _ _ _ ?_ ?_ ?_ ?_ ?_
  · show m.streams[k].ba = (streamAt s k.val).ba
    exact hba.symm
  · show m.streams[k].rq = (streamAt s k.val).rq
    exact hrq.symm
  · show m.streams[k].pv = (streamAt s k.val).pv
    exact hpv.symm
  · show m.streams[k].pend = (streamAt s k.val).pend
    exact hpend.symm
  · intro hm2 hpvM
    have hs2 : stateMode s k = 2 := by
      rw [stateMode_modeOf s pin k]
      exact hm2
    exact hwb k hs2 (by rw [hpv]; exact hpvM)

/-- The capture-mode request congruence at stream `0`. -/
theorem mhcModesReq_abs_cap0 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hwb : ∀ k : Fin 2, stateMode s k = 2 → (streamAt s k.val).pv = true →
      m.streams[k].wb = (streamAt s k.val).wb) :
    (mhcModesReq m pin)[0] = (mhcModesReq (absChip s) pin)[0] :=
  mhcModesReq_abs_cap s m pin 0 hrel hmode hwb

/-- The capture-mode request congruence at stream `1`. -/
theorem mhcModesReq_abs_cap1 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hwb : ∀ k : Fin 2, stateMode s k = 2 → (streamAt s k.val).pv = true →
      m.streams[k].wb = (streamAt s k.val).wb) :
    (mhcModesReq m pin)[1] = (mhcModesReq (absChip s) pin)[1] :=
  mhcModesReq_abs_cap s m pin 1 hrel hmode hwb

/-- **`contents_open_req_cap`**: `contents_open_req_wb` (`CoreCombWire` §11) with
the unguarded `WB` premise replaced by the capture-mode one, which `CapInv`
supplies (`contentsWb_of_capInv`).  This is the form the discharge can use in
place of the named `OpenWiring.contentsWb` residual. -/
theorem contents_open_req_cap (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hmode : ∀ k : Fin 2,
      machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hcap : CapInv s m) :
    mhcReq m pin = mhcReq (absChip s) pin := by
  have hwb : ∀ k : Fin 2, stateMode s k = 2 → (streamAt s k.val).pv = true →
      m.streams[k].wb = (streamAt s k.val).wb :=
    fun k hm2 hpv => contentsWb_of_capInv s m k hcap hm2 hpv
  have hserved := contents_open_served s m pin hrel hinv hmode
  have h0 := mhcModesReq_abs_cap0 s m pin hrel hmode hwb
  have h1 := mhcModesReq_abs_cap1 s m pin hrel hmode hwb
  have h2 : Machine.p0Req m.p0 = Machine.p0Req (absChip s).p0 :=
    p0Req_congr _ _ hrel.p0.req hrel.p0.ptr
  have h3 : Machine.hostReq m.host = Machine.hostReq (absChip s).host := by
    refine hostReq_congr _ _ ?_
    rw [hrel.hostReq]; rfl
  have hlist : ∀ j : Nat, j < 4 →
      (mhcReqs m pin).getD j .none = (mhcReqs (absChip s) pin).getD j .none := by
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj' with rfl | rfl | rfl | rfl <;> simp [mhcReqs, h0, h1, h2, h3]
  have hsle : Bridge.Mem.servedIndex s.p0 (memIn s pin) ≤ 4 := servedIndex_le_four s pin
  have hserved' : mhcServed (absChip s) pin = Bridge.Mem.servedIndex s.p0 (memIn s pin) := by
    rw [mhcServed_eq_machServed]; exact machServed_abs s pin hinv
  simp only [mhcReq]
  rw [hserved, hserved']
  by_cases hz : (Bridge.Mem.servedIndex s.p0 (memIn s pin) == 0) = true
  · simp only [hz, if_true]
  · simp only [hz, Bool.false_eq_true, if_false]
    exact hlist _ (by omega)

end Metronome.ChipCut.Discharge
