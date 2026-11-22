import Metronome.ChipCut.Assembly

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Metronome.ChipCut

open Metronome
open Metronome.ChipCut.Discharge

/-- (3) The **landing relation**: while a stream has a read outstanding, the word
it is about to land agrees with the machine's landing slot — `WB` in transmit
(`MODE = 0`) and the replay-buffer landing pair in replay (`MODE = 3`, B1's
`HeldLanding`).

`HeldOK` is a *disjunction* (`FRZD = 0` alone suffices), so this relation is only
consumed on the cycles where `FRZD` is set: the first unfrozen cycle after a
freeze, where the frozen landing's agreement has to be carried over. -/
def StreamRelX (s : State) (m : Machine.State) : Prop :=
  ∀ k : Fin 2, (streamAt s k.val).ld = true →
    ((stateMode s k = 0 → (streamAt s k.val).wb = m.streams[k].wb) ∧
     (stateMode s k = 3 → Bridge.StreamBuf.HeldLanding (streamAt s k.val) m.streams[k]))

/-- At reset no stream has a read outstanding, so the relation is vacuous. -/
theorem streamRelX_reset (cont : Contents) (m : Machine.State) :
    StreamRelX (resetState cont) m := by
  intro k h
  rw [show streamAt (resetState cont) k.val = Stream.resetState from by
    rw [streamAt_fin]; simp [resetState]] at h ⊢
  simp [Stream.resetState] at h

/-- `TX` mode is `MODE = 0`. -/
theorem stateMode_of_txMode (s : State) (pin : Machine.PinIn) (k : Fin 2)
    (h : Stream.txMode (k.val == 0) (streamIn s pin k.val) = true) :
    stateMode s k = 0 := by
  rw [stateMode_branch s pin k]
  have hp := h
  unfold Stream.txMode at hp
  simp_all

/-- `RPL` mode is `MODE = 3`. -/
theorem stateMode_of_rpl (s : State) (pin : Machine.PinIn) (k : Fin 2)
    (h : Stream.rpl (k.val == 0) (streamIn s pin k.val) = true) :
    stateMode s k = 3 := by
  rw [stateMode_branch s pin k]
  simp [h]

/-- `ldModeInv` puts a stream with a read outstanding in a mode whose branch is
`TX` or `RPL`, so the relation's two clauses apply. -/
theorem ldMode_branch (s : State) (pin : Machine.PinIn) (k : Fin 2) (hm : ldModeInv s)
    (hld : (streamAt s k.val).ld = true) :
    Stream.txMode (k.val == 0) (streamIn s pin k.val) = true ∨
      Stream.rpl (k.val == 0) (streamIn s pin k.val) = true := by
  have h := hm k hld
  rw [stateMode_branch s pin k] at h
  by_cases hrpl : Stream.rpl (k.val == 0) (streamIn s pin k.val) = true
  · exact Or.inr hrpl
  · by_cases htx : Stream.txMode (k.val == 0) (streamIn s pin k.val) = true
    · exact Or.inl htx
    · simp [hrpl, htx] at h

/-- The relation supplies B1's per-cycle `HeldOK` (given the mode invariant on
`LD`), which is the shape `bufRel_step_unfrozen_guarded` consumes. -/
theorem streamRelX_hok (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (h : StreamRelX s m) (hm : ldModeInv s) :
    ∀ k : Fin 2, (streamAt s k.val).ld = true →
      Bridge.StreamBuf.HeldOK (k.val == 0) (streamAt s k.val) (streamIn s pin k.val)
        m.streams[k] := by
  intro k hld
  obtain ⟨hwb, hland⟩ := h k hld
  unfold Bridge.StreamBuf.HeldOK
  rcases ldMode_branch s pin k hm hld with htx | hrpl
  · exact Or.inr (Or.inl ⟨htx, hwb (stateMode_of_txMode s pin k htx)⟩)
  · exact Or.inr (Or.inr ⟨hrpl, hland (stateMode_of_rpl s pin k hrpl)⟩)

/-! ## Where the relation comes from: the frozen landing

The only cycles that can produce `LD = true` with `FRZD` set are the frozen ones
(`Stream.ldNext` holds `LD` through a freeze), so `StreamRelX`'s content is
established by the frozen landing itself.  These are the two carry-over facts:
B1's `heldLanding_frozen_landing` (replay) and `wb_frozen_tx_landing`
(transmit). -/

/-- A frozen replay landing leaves the cut and machine landing pairs in
`HeldLanding` at the next state. -/
theorem heldLanding_after_frozen_replay (s : State) (m : Machine.State)
    (pin : Machine.PinIn) (hrel : ChipRel s m) (hact : runRst s pin = true)
    (hw : StreamWire s m pin) (hfrz : s.freeze.frz = true) (k : Fin 2)
    (hrew : (streamIn s pin k.val).rewind = false)
    (hrpl : Stream.rpl (k.val == 0) (streamIn s pin k.val) = true)
    (hld : (streamAt s k.val).ld = true) (hfzd : s.freeze.frzd = false) :
    Bridge.StreamBuf.HeldLanding (streamAt (activeStep s pin) k.val)
      ((Machine.step m pin).streams[k]) := by
  obtain ⟨-, -, -, -, -, -, hldeq, -, -, -, hbuf⟩ := hrel.streams k
  have hfrzM : m.dbg.frz = true := by rw [DbgRel.frz_eq hrel.dbg]; exact hfrz
  have hcf : (Machine.cfgView m.cfg).streams[k] =
      Bridge.StreamB.cfgOf (streamIn s pin k.val) := by
    rw [hrel.cfg]
    exact (cfgOf_streamIn s pin k).symm
  have hmach := streamsNext_eq s m pin hrel hact k hcf (hw.mode k) (hw.input k)
  have hfzd' : (streamIn s pin k.val).frzd = false := hfzd
  rw [streamAt_activeStep s pin k, hmach, hfrzM]
  exact Bridge.StreamBuf.heldLanding_frozen_landing (k.val == 0) (streamAt s k.val)
    (streamIn s pin k.val) m.streams[k] (Bridge.StreamB.cfgOf (streamIn s pin k.val))
    hact hfrz hrew hldeq hbuf.wv_eq hld hfzd' hrpl

/-- A frozen transmit landing writes the same `WB` in both readings. -/
theorem wb_after_frozen_tx (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hact : runRst s pin = true) (hw : StreamWire s m pin)
    (hfrz : s.freeze.frz = true) (k : Fin 2)
    (hrew : (streamIn s pin k.val).rewind = false)
    (htx : Stream.txMode (k.val == 0) (streamIn s pin k.val) = true)
    (hld : (streamAt s k.val).ld = true) (hfzd : s.freeze.frzd = false) :
    (streamAt (activeStep s pin) k.val).wb = ((Machine.step m pin).streams[k]).wb := by
  obtain ⟨-, -, -, -, -, -, hldeq, -, -, -, hbuf⟩ := hrel.streams k
  have hfrzM : m.dbg.frz = true := by rw [DbgRel.frz_eq hrel.dbg]; exact hfrz
  have hcf : (Machine.cfgView m.cfg).streams[k] =
      Bridge.StreamB.cfgOf (streamIn s pin k.val) := by
    rw [hrel.cfg]
    exact (cfgOf_streamIn s pin k).symm
  have hmach := streamsNext_eq s m pin hrel hact k hcf (hw.mode k) (hw.input k)
  have hfzd' : (streamIn s pin k.val).frzd = false := hfzd
  rw [streamAt_activeStep s pin k, hmach, hfrzM]
  exact Bridge.StreamBuf.wb_frozen_tx_landing (k.val == 0) (streamAt s k.val)
    (streamIn s pin k.val) m.streams[k] (Bridge.StreamB.cfgOf (streamIn s pin k.val))
    hact hfrz hrew hldeq hbuf.wv_eq htx hld hfzd'

end Metronome.ChipCut
