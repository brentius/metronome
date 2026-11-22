import Metronome.ChipCut.Assembly

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Metronome.ChipCut

open Metronome
open Metronome.ChipCut.Discharge

/-- (4a) The replay buffer at the next state, **proved** rather than assumed:
the unfrozen cycle is B1's guarded step with `hok` from `StreamRelX`, the frozen
cycle is B1's frozen landing bridge (`LD ∧ !FRZD` included) with `ldModeInv` and
`streamShapeInv` supplying its two side conditions. -/
theorem streamBufrel_of (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hac : runRst s pin = true)
    (hw : Discharge.StreamWire s m pin) (hX : StreamRelX s m)
    (hshape : streamShapeInv s) (hldm : ldModeInv s) (k : Fin 2) :
    Bridge.StreamB.BufRel (k.val == 0) (streamAt (activeStep s pin) k.val)
      ((Machine.step m pin).streams[k]) := by
  have hcfg : (Machine.cfgView m.cfg).streams[k] =
      Bridge.StreamB.cfgOf (streamIn s pin k.val) := by
    rw [hrel.cfg]
    exact (cfgOf_streamIn s pin k).symm
  have hnext := streamsNext_eq s m pin hrel hac k hcfg (hw.mode k) (hw.input k)
  have hmf : m.dbg.frz = s.freeze.frz := DbgRel.frz_eq hrel.dbg
  rw [streamAt_fin (activeStep s pin) k, activeStep_streams]
  by_cases hf : s.freeze.frz = true
  · rw [hnext, hmf, hf]
    have hldmode : (streamAt s k.val).ld = true →
        Stream.txMode (k.val == 0) (streamIn s pin k.val) = true ∨
          Stream.rpl (k.val == 0) (streamIn s pin k.val) = true :=
      ldMode_branch s pin k hldm
    have hshapek : Bridge.StreamBuf.ShapeOK (streamAt s k.val) := (hshape k).1
    have hmv : mvEn s pin = 0 := frozenNoMove s pin hf
    have hadv : (streamIn s pin k.val).adv = false := by
      show strobe s pin (BitVec.ofNat 6 (47 + k.val)) = false
      simp only [strobe, hmv]
      exact opg_zero _ _ _ _
    have hrx : (streamIn s pin k.val).rxWe = false := by
      show strobe s pin (BitVec.ofNat 6 (49 + k.val)) = false
      simp only [strobe, hmv]
      exact opg_zero _ _ _ _
    have hpush : (streamIn s pin k.val).capPush = false := by
      show Debug.Ctrl.cev s.dbgCtrl.cen s.dbgCtrl.replay s.freeze.frz (riseVec s)
        (fallVec s) s.dbgCtrl.emask = false
      simp [Debug.Ctrl.cev, hf]
    have hlate : (streamIn s pin k.val).replayLate = false := by
      show Debug.Ctrl.late s.dbgCtrl.replay s.freeze.frz (streamAt s 0).wv s.dbgCtrl.dc
        (streamAt s 0).wb = false
      simp [Debug.Ctrl.late, hf]
    by_cases hrew : (streamIn s pin k.val).rewind = true
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, hbuf⟩ :=
        Bridge.StreamBuf.frozen_rel_landing_rewind_flush (k.val == 0) (streamAt s k.val)
          (streamIn s pin k.val) m.streams[k] (Bridge.StreamB.cfgOf (streamIn s pin k.val))
          (hrel.streams k) hac hf hrew (Bridge.StreamB.cfgStart_bv (streamIn s pin k.val)).symm
          hldmode hadv hrx hpush hlate
      exact hbuf
    · have hrewf : (streamIn s pin k.val).rewind = false := by simpa using hrew
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hbuf⟩ :=
        Bridge.StreamBuf.frozen_rel_landing_flush (k.val == 0) (streamAt s k.val)
          (streamIn s pin k.val) m.streams[k] (Bridge.StreamB.cfgOf (streamIn s pin k.val))
          (hrel.streams k) hac hf hrewf hldmode hshapek hadv hrx hpush hlate
      exact hbuf
  · have hff : s.freeze.frz = false := by simpa using hf
    rw [hnext, hmf, hff]
    exact Bridge.StreamBuf.bufRel_step_unfrozen_guarded (k.val == 0) (streamAt s k.val)
      (streamIn s pin k.val) m.streams[k] (hrel.streams k)
      (streamRelX_hok s m pin hX k) hac hff

end Metronome.ChipCut
