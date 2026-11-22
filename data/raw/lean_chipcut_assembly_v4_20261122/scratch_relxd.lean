import Metronome.ChipCut.Assembly

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Metronome.ChipCut

open Metronome
open Metronome.ChipCut.Discharge

/-! ## (3b) `StreamRelX` in its disjunctive form (`HeldOK` transposed) -/

/-- The landing relation, in `HeldOK`'s own shape: `FRZD` clear, or the transmit
`WB` agreement, or the replay landing pair.  This is strictly weaker than the
conjunctive form and is exactly what the unfrozen bridge consumes. -/
def StreamRelXD (s : State) (m : Machine.State) : Prop :=
  ∀ k : Fin 2, (streamAt s k.val).ld = true →
    (s.freeze.frzd = false ∨
     (stateMode s k = 0 ∧ (streamAt s k.val).wb = m.streams[k].wb) ∨
     (stateMode s k = 3 ∧ Bridge.StreamBuf.HeldLanding (streamAt s k.val) m.streams[k]))

theorem streamRelXD_reset (cont : Contents) (m : Machine.State) :
    StreamRelXD (resetState cont) m := by
  intro k h
  rw [show streamAt (resetState cont) k.val = Stream.resetState from by
    rw [streamAt_fin]; simp [resetState]] at h ⊢
  simp [Stream.resetState] at h

/-- `stateMode = 0` is the transmit branch. -/
theorem stateMode_zero_txMode (s : State) (pin : Machine.PinIn) (k : Fin 2)
    (h : stateMode s k = 0) : Stream.txMode (k.val == 0) (streamIn s pin k.val) = true := by
  rw [stateMode_branch s pin k] at h
  by_cases hr : Stream.rpl (k.val == 0) (streamIn s pin k.val) = true
  · rw [ite_eq_left hr] at h
    exact absurd h (by decide)
  · rw [ite_eq_right hr] at h
    by_cases hc : Stream.cen (k.val == 0) (streamIn s pin k.val) = true
    · rw [ite_eq_left hc] at h
      exact absurd h (by decide)
    · rw [ite_eq_right hc] at h
      by_cases ht : Stream.txMode (k.val == 0) (streamIn s pin k.val) = true
      · exact ht
      · rw [ite_eq_right ht] at h
        exact absurd h (by decide)

/-- `stateMode = 3` is the replay branch. -/
theorem stateMode_three_rpl (s : State) (pin : Machine.PinIn) (k : Fin 2)
    (h : stateMode s k = 3) : Stream.rpl (k.val == 0) (streamIn s pin k.val) = true := by
  rw [stateMode_branch s pin k] at h
  by_cases hr : Stream.rpl (k.val == 0) (streamIn s pin k.val) = true
  · exact hr
  · rw [ite_eq_right hr] at h
    by_cases hc : Stream.cen (k.val == 0) (streamIn s pin k.val) = true
    · rw [ite_eq_left hc] at h
      exact absurd h (by decide)
    · rw [ite_eq_right hc] at h
      by_cases ht : Stream.txMode (k.val == 0) (streamIn s pin k.val) = true
      · rw [ite_eq_left ht] at h
        exact absurd h (by decide)
      · rw [ite_eq_right ht] at h
        exact absurd h (by decide)

/-- The disjunctive relation *is* `HeldOK` (no mode invariant needed). -/
theorem streamRelXD_hok (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (h : StreamRelXD s m) :
    ∀ k : Fin 2, (streamAt s k.val).ld = true →
      Bridge.StreamBuf.HeldOK (k.val == 0) (streamAt s k.val) (streamIn s pin k.val)
        m.streams[k] := by
  intro k hld
  rcases h k hld with hf | ⟨hm, hwb⟩ | ⟨hm, hl⟩
  · exact Or.inl hf
  · exact Or.inr (Or.inl ⟨stateMode_zero_txMode s pin k hm, hwb⟩)
  · exact Or.inr (Or.inr ⟨stateMode_three_rpl s pin k hm, hl⟩)

/-! ## The frozen no-landing holds -/

theorem frzd_activeStep (s : State) (pin : Machine.PinIn) (hac : runRst s pin = true) :
    (activeStep s pin).freeze.frzd = s.freeze.frz := by
  show (CoreCtl.freezeStep s.freeze (freezeIn s pin)).frzd = s.freeze.frz
  rw [CoreCtl.frzd_next]
  have h : (freezeIn s pin).resetN = true := hac
  simp [h]

/-- With `FRZD` set the cut's frozen step holds `WB`, `NB`, `WV` and `LD`. -/
theorem frozen_holds_unguarded (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (hfrz : i.frz = true) (hreset : i.resetN = true) (hrew : i.rewind = false)
    (hfzd : i.frzd = true) :
    (Stream.step cap s i).wb = s.wb ∧ (Stream.step cap s i).nb = s.nb ∧
      (Stream.step cap s i).wv = s.wv ∧ (Stream.step cap s i).ld = s.ld := by
  have hz0 : (s.ld && !i.frzd) = false := by simp [hfzd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Stream.step, Stream.wbNext, hreset, Bool.not_true, ite_true, hfrz]
    rw [show (Stream.txMode cap i && s.ld && !i.frzd) = false by simp [Bool.and_assoc, hz0]]
    simp
  · simp only [Stream.step, Stream.nbNext, hreset, Bool.not_true]
    rw [show (Stream.rpl cap i && s.ld && !i.frzd && i.frz) = false by
      simp [Bool.and_assoc, hz0]]
    rw [show (Stream.rpl cap i && s.ld && !i.frzd && Stream.occupied s i) = false by
      simp [Bool.and_assoc, hz0]]
    simp
  · exact (Stream.frozen_holds cap s i hfrz hreset hrew).2.2.2.2.2.2.2.1
  · exact Bridge.StreamBuf.ld_frozen_eq cap s i hreset hfrz hrew

/-- With `FRZD` set the machine's frozen step holds `WB` and `NB`. -/
theorem mach_frozen_holds_unguarded (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (c : Machine.StreamCfg)
    (hld : s.ld = m.ld) (hwv : s.wv = m.wv) (hrew : i.rewind = false)
    (hfzd : i.frzd = true) :
    (Machine.streamNext c (Bridge.StreamB.modeOf cap i) m (Bridge.StreamB.absIn cap s i) true).wb
        = m.wb ∧
      (Machine.streamNext c (Bridge.StreamB.modeOf cap i) m (Bridge.StreamB.absIn cap s i) true).nb
        = m.nb := by
  have h := Bridge.StreamBuf.mach_frozen_landing cap s i m c hld hwv hrew
  constructor <;> (rw [h]; simp [hfzd])

/-! ## The step -/

theorem streamRelXD_step_active (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hw : Discharge.StreamWire s m pin)
    (h : StreamRelXD s m) (hldm : ldModeInv s) (hq : stream_mode_quiet s pin)
    (hac : runRst s pin = true) :
    StreamRelXD (activeStep s pin) (Machine.step m pin) := by
  intro k hld'
  have hstep : step s pin = activeStep s pin := by simp [step, hac]
  have hldnext : Stream.ldNext (k.val == 0) (streamAt s k.val) (streamIn s pin k.val) = true := by
    rw [streamAt_activeStep s pin k] at hld'
    show Stream.ldNext (k.val == 0) (streamAt s k.val) (streamIn s pin k.val) = true
    exact hld'
  have hres : (streamIn s pin k.val).resetN = true := hac
  have hrew : (streamIn s pin k.val).rewind = false := by
    by_cases hr : (streamIn s pin k.val).rewind = true
    · simp [Stream.ldNext, hres, hr] at hldnext
    · simpa using hr
  by_cases hfrz : s.freeze.frz = false
  · exact Or.inl (by rw [frzd_activeStep s pin hac, hfrz])
  · have hfrzt : s.freeze.frz = true := by simpa using hfrz
    have hfrzi : (streamIn s pin k.val).frz = true := hfrzt
    have hld : (streamAt s k.val).ld = true := by
      rw [Stream.ldNext, hres, hrew, hfrzi] at hldnext
      simpa using hldnext
    obtain ⟨-, -, -, -, -, -, hldeq, -, -, -, hbuf⟩ := hrel.streams k
    have hcf : (Machine.cfgView m.cfg).streams[k] =
        Bridge.StreamB.cfgOf (streamIn s pin k.val) := by
      rw [hrel.cfg]
      exact (cfgOf_streamIn s pin k).symm
    have hmachstep : (Machine.step m pin).streams[k] =
        Machine.streamNext (Bridge.StreamB.cfgOf (streamIn s pin k.val))
          (Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
          m.streams[k] (Bridge.StreamB.absIn (k.val == 0) (streamAt s k.val)
            (streamIn s pin k.val)) true := by
      rw [streamsNext_eq s m pin hrel hac k hcf (hw.mode k) (hw.input k),
        DbgRel.frz_eq hrel.dbg, hfrzt]
    by_cases hsame : stateMode (activeStep s pin) k = stateMode s k
    · by_cases hfzd : s.freeze.frzd = false
      · rcases ldMode_branch s pin k hldm hld with htx | hrpl
        · exact Or.inr (Or.inl ⟨hsame.trans (stateMode_of_txMode s pin k htx),
            wb_after_frozen_tx s m pin hrel hac hw hfrzt k hrew htx hld hfzd⟩)
        · exact Or.inr (Or.inr ⟨hsame.trans (stateMode_of_rpl s pin k hrpl),
            heldLanding_after_frozen_replay s m pin hrel hac hw hfrzt k hrew hrpl hld hfzd⟩)
      · have hfzdt : s.freeze.frzd = true := by simpa using hfzd
        have hfzdi : (streamIn s pin k.val).frzd = true := hfzdt
        have hcut := frozen_holds_unguarded (k.val == 0) (streamAt s k.val)
          (streamIn s pin k.val) hfrzi hres hrew hfzdi
        obtain ⟨hwb', hnb', hwv', -⟩ := hcut
        have hm := mach_frozen_holds_unguarded (k.val == 0) (streamAt s k.val)
          (streamIn s pin k.val) m.streams[k] (Bridge.StreamB.cfgOf (streamIn s pin k.val))
          hldeq hbuf.wv_eq hrew hfzdi
        obtain ⟨mwb', mnb'⟩ := hm
        rcases h k hld with hf | ⟨hm0, hwb⟩ | ⟨hm3, hl⟩
        · rw [hfzdt] at hf
          exact absurd hf (by decide)
        · exact Or.inr (Or.inl ⟨hsame.trans hm0, by
            rw [streamAt_activeStep s pin k, hwb', hmachstep, mwb']
            exact hwb⟩)
        · exact Or.inr (Or.inr ⟨hsame.trans hm3, by
            unfold Bridge.StreamBuf.HeldLanding at hl ⊢
            rw [streamAt_activeStep s pin k, hwv', hnb', hmachstep, mwb', mnb']
            exact hl⟩)
    · have hch : stateMode (step s pin) k ≠ stateMode s k := by rw [hstep]; exact hsame
      rw [(hq k hch).1] at hld
      exact absurd hld (by decide)

/-- A `StreamWire` record from the assembled pieces (the three open fields plus
the two proved agreements). -/
theorem streamWire_of (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hls : Discharge.LandingStream s)
    (hexp : ExplicitPremises s m pin) (hac : runRst s pin = true)
    (hopen : OpenWiring s m pin) : Discharge.StreamWire s m pin :=
  { mode := fun k => streamWire_mode s m pin hrel k
    input := streamInputAgree_of s m pin hrel hinv hls hexp hac
    hostctl := hopen.streamHostctl
    landing := hopen.streamLanding
    bufrel := hopen.streamBufrel }

theorem streamRelXD_step_of_premises (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hls : Discharge.LandingStream s)
    (hexp : ExplicitPremises s m pin) (hopen : OpenWiring s m pin)
    (h : StreamRelXD s m) (hldm : ldModeInv s) (hq : stream_mode_quiet s pin) :
    StreamRelXD (step s pin) (Machine.step m pin) := by
  by_cases hac : runRst s pin = true
  · rw [show step s pin = activeStep s pin from by simp [step, hac]]
    exact streamRelXD_step_active s m pin hrel (streamWire_of s m pin hrel hinv hls hexp hac hopen)
      h hldm hq hac
  · rw [show step s pin = resetChip s pin from by simp [step, hac]]
    intro k h
    have hS : streamAt (resetChip s pin) k.val = Stream.resetState := by
      rw [streamAt_fin]; simp [resetChip, resetState]
    rw [hS] at h
    simp [Stream.resetState] at h

end Metronome.ChipCut
