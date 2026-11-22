/-
# ChipCut: invariants, the reset edge, the active cycle and traces

`Inv` holds in every reachable state (`inv_reset`, `inv_step`, `inv_trace`);
`SideConds` holds in every cycle (`sideConds`) and is not a hypothesis of the
refinement.  The reset edge refines the machine's reset step with no premises
(`chip_reset_refines`, `chip_reset_refines_rel`); the active cycle keeps one
named premise per component group (`Premises`).  `trace_refines` starts from
`resetState` and uses only `chip_step_refines` — no bisimulation hypothesis.
-/

import Metronome.ChipCut.Rel

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Metronome.ChipCut

open Metronome
open Discharge.BankWire (cfgMaskFin MaskedZero maskedZero_zero)

/-! ## Reachable-state invariants and per-cycle side conditions -/

/-- Reachable-state invariants the bridges ask for. -/
structure Inv (s : State) : Prop where
  /-- `Mem.req` never takes code 3 (`Mem.reqNext_ne`). -/
  reqNeThree : s.p0.req ≠ (3 : BitVec 2)
  /-- The core round-robin cursor is a thread index (`Core.rr_next_lt_six`). -/
  rrLt : ∀ c : Fin 2, s.cores[c.val].rr.toNat < 6
  /-- The two host-link cuts agree on their shared registers. -/
  hostAgrees : HostPins.Agrees s.hostRead s.hostCmd
  /-- A pointer request served with `RDY` clear does not leave a stale landing. -/
  staleRdy : s.p0.land = true → s.p0.landRdy = false → s.p0.rdy = false

/-- Per-cycle conditions the bridges need (they depend on the pin input). -/
structure SideConds (s : State) (pin : Machine.PinIn) : Prop where
  /-- The accumulator write group is one-hot or zero (§6). -/
  accHit : Units.Acc.OneHotOrZero (accIn s pin).hit
  /-- A frozen cycle presents no move to any unit (§12.3). -/
  frozenNoMove : s.freeze.frz = true → mvEn s pin = 0

/-- `Acc`'s write-group contract is a theorem, not an assumption. -/
theorem accHit_oneHotOrZero (s : State) (pin : Machine.PinIn) :
    Units.Acc.OneHotOrZero (accIn s pin).hit :=
  Strobes.atMostOne_oneHotOrZero (Strobes.hitsMask_atMostOne _ _ _)

/-- A frozen cycle presents no move: both cores' move-enable outputs are zero
(`Core.mvEn_zero`; the `xa` term carries the `!FRZ` gate). -/
theorem frozenNoMove (s : State) (pin : Machine.PinIn) (hf : s.freeze.frz = true) :
    mvEn s pin = 0 := by
  have h0 : (coreIn s pin 0).frz = true := hf
  have h1 : (coreIn s pin 1).frz = true := hf
  show (Core.out true s.cores[1] (coreIn s pin 1)).mvEn ++
    (Core.out false s.cores[0] (coreIn s pin 0)).mvEn = (0 : BitVec 6)
  rw [Core.mvEn_zero true s.cores[1] (coreIn s pin 1) (Or.inr h1),
    Core.mvEn_zero false s.cores[0] (coreIn s pin 0) (Or.inr h0)]
  simp

/-- `SideConds` holds in every cycle; it is a theorem, not a hypothesis. -/
theorem sideConds (s : State) (pin : Machine.PinIn) : SideConds s pin :=
  ⟨accHit_oneHotOrZero s pin, frozenNoMove s pin⟩

/-- `inv_reset`: the reset product satisfies the invariants. -/
theorem inv_reset (cont : Contents) : Inv (resetState cont) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [resetState, Mem.resetState]
  · intro c
    simp [resetState]
  · simp [HostPins.Agrees, resetState, HostRead.resetState, HostCmd.resetState]
  · intro h1 h2
    simp [resetState, Mem.resetState] at h1

/-- A landing with `RDY` clear keeps `RDY` clear one step later: the unfrozen
case forces a pointer move (which clears `RDY`), the frozen case is the invariant
itself. -/
theorem staleRdy_step (s : State) (pin : Machine.PinIn)
    (h : s.p0.land = true → s.p0.landRdy = false → s.p0.rdy = false) :
    (Mem.step s.p0 (memIn s pin)).land = true →
      (Mem.step s.p0 (memIn s pin)).landRdy = false →
      (Mem.step s.p0 (memIn s pin)).rdy = false := by
  intro hl hlr
  simp only [Mem.step, Mem.landNext, Mem.landRdyNext, Mem.rdyNext] at hl hlr ⊢
  by_cases hr : (memIn s pin).resetN = true
  · simp only [hr, Bool.not_true, Bool.false_eq_true, if_false] at hl hlr ⊢
    by_cases hpw : (memIn s pin).pWe = true
    · simp [hpw]
    · have hpw' : (memIn s pin).pWe = false := by simpa using hpw
      simp only [hpw', Bool.false_eq_true, if_false] at hl hlr ⊢
      by_cases hf : (memIn s pin).frz = true
      · simp only [hf, Bool.not_true, Bool.false_eq_true, if_false] at hl hlr
        simpa [hl, hlr] using h hl hlr
      · have hf' : (memIn s pin).frz = false := by simpa using hf
        simp [hf'] at hlr
  · have hr' : (memIn s pin).resetN = false := by simpa using hr
    simp [hr'] at hl

/-- `inv_step`: the invariants are preserved by one product step (both the
active and the reset edge). -/
theorem inv_step (s : State) (pin : Machine.PinIn) (h : Inv s) : Inv (step s pin) := by
  unfold step
  split
  · rename_i hrun
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (Mem.step s.p0 (memIn s pin)).req ≠ 3
      exact Mem.reqNext_ne s.p0 (memIn s pin) h.reqNeThree
    · intro c
      simpa [activeStep, Core.rrOk] using
        (Core.rr_next_lt_six (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) (h.rrLt c))
    · show HostPins.Agrees (HostRead.step s.hostRead (hostReadIn s pin))
        (HostCmd.step s.hostCmd (hostCmdIn s pin))
      have hi : hostCmdIn s pin = (hostReadIn s pin).toHostCmd := rfl
      rw [hi]
      exact HostPins.agrees_step s.hostRead s.hostCmd (hostReadIn s pin) h.hostAgrees
    · exact staleRdy_step s pin h.staleRdy
  · rename_i hrun
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [resetChip, resetState, Mem.resetState]
    · intro c
      simp [resetChip, resetState]
    · simp [HostPins.Agrees, resetChip, resetState, HostRead.resetState, HostCmd.resetState]
    · intro h1 h2
      simp [resetChip, resetState, Mem.resetState] at h1

/-! ## The reset relation, field by field -/

/-- The cut's line reset state is the machine's zero line. -/
theorem line_abs_reset : Bridge.Line.absSt Line.resetState = (default : Machine.LineSt) := by
  decide

/-- The cut's stream reset state satisfies `AbsRelB` against the zero stream. -/
theorem stream_abs_reset (cap : Bool) :
    Bridge.StreamB.AbsRelB cap Stream.resetState (default : Machine.StreamSt) := by
  unfold Bridge.StreamB.AbsRelB Bridge.StreamB.BufRel
  cases cap <;> decide

/-- The zero machine pointer relates to the cut's reset pointer. -/
theorem p0Rel_reset : P0Rel ({ ptr := 0, d := 0 } : Machine.P0St) Mem.resetState := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, ?_⟩
  · decide
  · intro h
    exact absurd h (by decide)

/-- The cut's pointer abstraction relates to its own state. -/
theorem p0Rel_abs (b : Mem.State) : P0Rel (Bridge.Mem.absP0 b) b := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro _
  rfl

/-- The arbiter abstraction relates to its own cut state. -/
theorem cwRel_abs (q : CoreQueue.State) (c : Config.State) :
    CwRel (Bridge.CfgWrite.cwOf q c) q c := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> intro _ <;> rfl

/-- The zero machine bank port relates to the cut's reset queue and arbiter. -/
theorem cwRel_reset :
    CwRel ({ cwa := 0, cwqa := 0, cwqd := 0, hha := 0, hhd := 0, bpa := 0, bpd := 0 } :
        Machine.CwSt)
      (⟨0, false, 0, 0, false⟩ : CoreQueue.State)
      (⟨false, false, ⟨0, 0⟩, ⟨0, 0⟩⟩ : Config.State) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> intro h <;>
    exact absurd h (by decide)

/-- Reset clears every implemented configuration bit. -/
theorem bankRel_reset (c : Machine.Config) (hzero : MaskedZero c) :
    BankRel (⟨cfgMaskFin, fun _ => 0⟩ : Bank.State) c := by
  refine ⟨rfl, ?_⟩
  intro k
  simpa [Bank.read, Machine.Util.cfgByte, Nat.add_sub_cancel_left] using (hzero k).symm

/-- During reset release the abstract configuration must still agree with
the cleared latch bank. An asserted reset clears the machine image directly. -/
theorem maskedZero_resetStep (m : Machine.State) (pin : Machine.PinIn)
    (hrelease : pin.rstn = true → MaskedZero (Machine.cfgNext m.cfg m.cw)) :
    MaskedZero (Machine.resetStep m pin).cfg := by
  cases hr : pin.rstn
  · simpa only [Machine.resetStep, hr, Bool.false_eq_true, if_false] using maskedZero_zero
  · simpa only [Machine.resetStep, hr, if_true] using hrelease hr

/-- The selected line of the reset state is a resetted line. -/
theorem lineAt_resetChip (s : State) (pin : Machine.PinIn) (n : Nat) :
    lineAt (resetChip s pin) n = Line.resetState := by
  unfold lineAt resetChip
  split <;> simp [resetState]

/-- The selected thread of the reset state is a resetted thread. -/
theorem threadAt_resetChip (s : State) (pin : Machine.PinIn) (n : Nat) :
    threadAt (resetChip s pin) n = Thread.resetState := by
  unfold threadAt resetChip
  split <;> simp [resetState]

/-- The selected stream of the reset state is a resetted stream. -/
theorem streamAt_resetChip (s : State) (pin : Machine.PinIn) (n : Nat) :
    streamAt (resetChip s pin) n = Stream.resetState := by
  unfold streamAt resetChip
  split <;> simp [resetState]

/-- The selected shifter of the power-on state is a resetted shifter. -/
theorem shAt_resetState (cont : Contents) (n : Nat) :
    shAt (resetState cont) n = Units.Shifter.resetState := by
  unfold shAt resetState
  split <;> simp

/-- The selected counter of the power-on state is a resetted counter. -/
theorem cntAt_resetState (cont : Contents) (n : Nat) :
    cntAt (resetState cont) n = Units.Counter.resetState := by
  unfold cntAt resetState
  split <;> simp

/-- The selected LFSR of the power-on state is a resetted LFSR. -/
theorem lfAt_resetState (cont : Contents) (n : Nat) :
    lfAt (resetState cont) n = Units.Lfsr.resetState := by
  unfold lfAt resetState
  split <;> simp

/-- `cfgNext` under the configuration-write relation: the two bank-port
payloads differ only when no write is performed. -/
theorem cfgNext_cwRel {q : CoreQueue.State} {c : Config.State} {cfg cfg' : Machine.Config}
    {cw : Machine.CwSt} (hcw : CwRel cw q c) (hcfg : cfg = cfg') :
    Machine.cfgNext cfg cw = Machine.cfgNext cfg' (Bridge.CfgWrite.cwOf q c) := by
  subst hcfg
  have hb : cw.bwp = c.previousWrite := hcw.bwp
  by_cases h : cw.bwp
  · have h' : c.previousWrite = true := by rw [← hb]; exact h
    simp [Machine.cfgNext, Bridge.CfgWrite.cwOf, h, h', hcw.bpa h, hcw.bpd h]
  · have hbw : cw.bwp = false := by
      cases hv : cw.bwp <;> simp_all
    have h' : c.previousWrite = false := by rw [← hb, hbw]
    simp [Machine.cfgNext, Bridge.CfgWrite.cwOf, hbw, h']

/-- The reset product's contents are the contents record itself. -/
theorem resetChip_cont (s : State) (pin : Machine.PinIn) :
    (resetChip s pin).cont = contentsReset s pin := rfl

theorem contentsReset_pmem (s : State) (pin : Machine.PinIn) :
    (contentsReset s pin).pmem = (Machine.resetStep (absChip s) pin).pmem := rfl

theorem contentsReset_dmem (s : State) (pin : Machine.PinIn) :
    (contentsReset s pin).dmem = (Machine.resetStep (absChip s) pin).dmem := rfl

theorem contentsReset_ramOut (s : State) (pin : Machine.PinIn) :
    (contentsReset s pin).ramOut = (Machine.resetStep (absChip s) pin).ramOut := rfl

theorem contentsReset_cfg (s : State) (pin : Machine.PinIn) :
    (contentsReset s pin).cfg = (Machine.resetStep (absChip s) pin).cfg := rfl

theorem resetStep_cfg (m : Machine.State) (pin : Machine.PinIn) :
    (Machine.resetStep m pin).cfg =
      (if pin.rstn = true then Machine.cfgNext m.cfg m.cw else Machine.Config.zero) := rfl

/-- The selected shifter of the reset state is a resetted shifter. -/
theorem shAt_resetChip (s : State) (pin : Machine.PinIn) (n : Nat) :
    shAt (resetChip s pin) n = Units.Shifter.resetState := by
  unfold shAt resetChip
  split <;> simp [resetState]

/-- The selected counter of the reset state is a resetted counter. -/
theorem cntAt_resetChip (s : State) (pin : Machine.PinIn) (n : Nat) :
    cntAt (resetChip s pin) n = Units.Counter.resetState := by
  unfold cntAt resetChip
  split <;> simp [resetState]

/-- The selected LFSR of the reset state is a resetted LFSR. -/
theorem lfAt_resetChip (s : State) (pin : Machine.PinIn) (n : Nat) :
    lfAt (resetChip s pin) n = Units.Lfsr.resetState := by
  unfold lfAt resetChip
  split <;> simp [resetState]

/-- `ChipRel` is preserved by a *reset* edge, for any related machine state.
No premise is needed: the cut loads its reset states, the machine clears every
register, and the validity-guarded fields are exactly the ones whose reset
values differ. -/
theorem chip_reset_refines_rel (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hrun : runRst s pin = false)
    (hrelease : pin.rstn = true → MaskedZero (Machine.cfgNext m.cfg m.cw)) :
    ChipRel (step s pin) (Machine.step m pin) := by
  have hcut : step s pin = resetChip s pin := by simp [step, hrun]
  have hq : (s.rst.rstQ && pin.rstn) = false := by simpa [runRst] using hrun
  have hmq : (m.rq && pin.rstn) = false := by rw [← hrel.rstQ]; exact hq
  have hmach : Machine.step m pin = Machine.resetStep m pin := by
    simp [Machine.step, Machine.stepObs, hmq]
  rw [hcut, hmach]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hr : pin.rstn = true <;> by_cases hb : s.rst.rstQ = true <;>
      simp [resetChip, resetState, Debug.Reset.step, Debug.Reset.resetState,
        Machine.resetStep, Machine.State.init, hr, hb]
  · by_cases hr : pin.rstn = true
    · by_cases hb : s.rst.rstQ = true <;>
        simp [resetChip, resetState, Debug.Reset.step, Debug.Reset.resetState,
          Machine.resetStep, Machine.State.init, hr, hb, hrel.rstM]
    · by_cases hb : s.rst.rstQ = true <;>
        simp [resetChip, resetState, Debug.Reset.step, Debug.Reset.resetState,
          Machine.resetStep, Machine.State.init, hr, hb]
  · show rqhNext s pin = Machine.Util.bv 2 ((m.rqh.toNat % 2) * 2)
    rw [show rqhNext s pin = BitVec.ofNat 2 ((s.rqh.toNat % 2) * 2) from by
      simp [rqhNext, hrun]]
    rw [hrel.rqh]
    rfl
  · simp only [resetChip, resetState, Machine.resetStep, Machine.State.init, SpiPins.resetState]
    unfold SyncRel
    refine ⟨?_, ?_, ?_⟩ <;> decide
  · intro l
    rw [lineAt_resetChip]
    simp [resetChip, resetState, Machine.resetStep, Machine.State.init, Bridge.Line.absSt,
      Line.resetState]
  · intro t
    rw [threadAt_resetChip]
    simp [resetChip, resetState, Machine.resetStep, Machine.State.init, Bridge.Thread.absState,
      Thread.resetState]
  · intro c
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [resetChip, resetState, Machine.resetStep, Machine.State.init]
  · intro c
    simp [resetChip, resetState, contentsReset, Machine.resetStep, Machine.State.init]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [resetChip, resetState, Machine.resetStep, Machine.State.init, Glue.resetState]
    · simp [resetChip, resetState, Machine.resetStep, Machine.State.init, Glue.resetState]
    · simp [resetChip, resetState, Machine.resetStep, Machine.State.init,
        Units.Acc.resetState]
    · simp [resetChip, resetState, Machine.resetStep, Machine.State.init,
        Units.Acc.resetState]
    · simp [resetChip, resetState, Machine.resetStep, Machine.State.init,
        Units.Acc.resetState]
    · simp [resetChip, resetState, Machine.resetStep, Machine.State.init,
        Units.Acc.resetState]
    · intro k
      simp [resetChip, resetState, Machine.resetStep, Machine.State.init,
        Units.Acc.resetState]
    · intro k
      rw [shAt_resetChip]
      simp [resetChip, resetState, Machine.resetStep, Machine.State.init, Units.Shifter.resetState]
    · intro k
      rw [cntAt_resetChip]
      simp [resetChip, resetState, Machine.resetStep, Machine.State.init,
        Units.Counter.resetState]
    · intro k
      rw [lfAt_resetChip]
      simp [resetChip, resetState, Machine.resetStep, Machine.State.init, Units.Lfsr.resetState]
  · show P0Rel ({ ptr := 0, d := 0 } : Machine.P0St) Mem.resetState
    exact p0Rel_reset
  · intro k
    rw [streamAt_resetChip]
    unfold Bridge.StreamB.AbsRelB Bridge.StreamB.BufRel
    simp [resetChip, resetState, Machine.resetStep, Machine.State.init, Stream.resetState]
  · show Bridge.Host.LinkRelR HostRead.resetState (0 : BitVec 8) (Machine.resetStep m pin)
    have hh : (Machine.resetStep m pin).host = Machine.State.init.host := rfl
    exact linkRelR_host_congr hh Bridge.Host.linkRelR_reset
  · show (Machine.HReq.none) = Machine.HReq.none
    rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [resetChip, resetState, Machine.resetStep, Machine.State.init, Glue.resetState]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [resetChip, resetState, Machine.resetStep, Machine.State.init,
        CoreCtl.freezeReset, Debug.Ctrl.resetState, Debug.Digest.resetState]
  · show CwRel ({ cwa := 0, cwqa := 0, cwqd := 0, hha := 0, hhd := 0, bpa := 0, bpd := 0 } : Machine.CwSt)
      (⟨0, false, 0, 0, false⟩ : CoreQueue.State)
      (⟨false, false, ⟨0, 0⟩, ⟨0, 0⟩⟩ : Config.State)
    exact cwRel_reset
  · exact bankRel_reset _ (maskedZero_resetStep m pin hrelease)
  · simp [resetChip, resetState, Machine.resetStep, Machine.State.init]
  · simp [resetChip, resetState, Machine.resetStep, Machine.State.init]
  · rw [resetChip_cont, contentsReset_cfg, resetStep_cfg, resetStep_cfg]
    by_cases hr : pin.rstn = true
    · simp only [hr, if_true]
      exact cfgNext_cwRel hrel.cw hrel.cfg
    · simp [hr]
  · rw [resetChip_cont, contentsReset_pmem]
    simpa [absChip, Machine.resetStep, Machine.State.init] using hrel.pmem
  · rw [resetChip_cont, contentsReset_dmem]
    simpa [absChip, Machine.resetStep, Machine.State.init] using hrel.dmem
  · rw [resetChip_cont, contentsReset_ramOut]
    simpa [absChip, Machine.resetStep, Machine.State.init] using hrel.ramOut
  · rw [resetChip_cont]
    simp [resetChip, resetState, contentsReset, Machine.resetStep, Machine.State.init]
  · rw [resetChip_cont]
    simp [resetChip, resetState, contentsReset, Machine.resetStep, Machine.State.init]

/-- The reset edge refines the machine's reset step with a cleared latch image. -/
theorem chip_reset_refines (s : State) (pin : Machine.PinIn) (hrun : runRst s pin = false)
    (hrelease : pin.rstn = true → MaskedZero (Machine.cfgNext (absChip s).cfg (absChip s).cw)) :
    ChipRel (step s pin) (Machine.step (absChip s) pin) := by
  have hcut : step s pin = resetChip s pin := by simp [step, hrun]
  have hq : (s.rst.rstQ && pin.rstn) = false := by simpa [runRst] using hrun
  have hmq : ((absChip s).rq && pin.rstn) = false := by simp [absChip, hq]
  have hmach : Machine.step (absChip s) pin = Machine.resetStep (absChip s) pin := by
    simp [Machine.step, Machine.stepObs, hmq]
  rw [hcut, hmach]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hr : pin.rstn = true <;> by_cases hb : s.rst.rstQ = true <;>
      simp [resetChip, resetState, Debug.Reset.step, Debug.Reset.resetState, absChip,
        Machine.resetStep, Machine.State.init, hr, hb]
  · by_cases hr : pin.rstn = true <;> by_cases hb : s.rst.rstQ = true <;>
      simp [resetChip, resetState, Debug.Reset.step, Debug.Reset.resetState, absChip,
        Machine.resetStep, Machine.State.init, hr, hb]
  · show rqhNext s pin = Machine.Util.bv 2 ((s.rqh.toNat % 2) * 2)
    rw [show rqhNext s pin = BitVec.ofNat 2 ((s.rqh.toNat % 2) * 2) from by
      simp [rqhNext, hrun]]
    rfl
  · simp only [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
      SpiPins.resetState]
    unfold SyncRel
    refine ⟨?_, ?_, ?_⟩ <;> decide
  · intro l
    rw [lineAt_resetChip]
    simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
      Bridge.Line.absSt, Line.resetState]
  · intro t
    rw [threadAt_resetChip]
    simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
      Bridge.Thread.absState, Thread.resetState]
  · intro c
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init]
  · intro c
    simp [resetChip, resetState, contentsReset, absChip, Machine.resetStep, Machine.State.init]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
        Glue.resetState]
    · simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
        Glue.resetState]
    · simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
        Units.Acc.resetState]
    · simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
        Units.Acc.resetState]
    · simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
        Units.Acc.resetState]
    · simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
        Units.Acc.resetState]
    · intro k
      simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
        Units.Acc.resetState]
    · intro k
      rw [shAt_resetChip]
      simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
        Units.Shifter.resetState]
    · intro k
      rw [cntAt_resetChip]
      simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
        Units.Counter.resetState]
    · intro k
      rw [lfAt_resetChip]
      simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
        Units.Lfsr.resetState]
  · simpa [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init] using
      (p0Rel_reset : P0Rel (default : Machine.P0St) Mem.resetState)
  · intro k
    rw [streamAt_resetChip]
    unfold Bridge.StreamB.AbsRelB Bridge.StreamB.BufRel
    simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
      Stream.resetState]
  · show Bridge.Host.LinkRelR HostRead.resetState (0 : BitVec 8)
        (Machine.resetStep (absChip s) pin)
    have hh : (Machine.resetStep (absChip s) pin).host = Machine.State.init.host := rfl
    exact linkRelR_host_congr hh Bridge.Host.linkRelR_reset
  · show (Machine.HReq.none) = Machine.HReq.none
    rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
        Glue.resetState]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init,
        CoreCtl.freezeReset, Debug.Ctrl.resetState, Debug.Digest.resetState]
  · simpa [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init] using
      cwRel_reset
  · simpa [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init] using
      (bankRel_reset _ (maskedZero_resetStep (absChip s) pin hrelease))
  · simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init]
  · simp [resetChip, resetState, absChip, Machine.resetStep, Machine.State.init]
  · rw [resetChip_cont, contentsReset_cfg, resetStep_cfg]
  · rw [resetChip_cont, contentsReset_pmem, absChip]
  · rw [resetChip_cont, contentsReset_dmem, absChip]
  · rw [resetChip_cont, contentsReset_ramOut, absChip]
  · rw [resetChip_cont]
    simp [resetChip, resetState, contentsReset, absChip, Machine.resetStep, Machine.State.init]
  · rw [resetChip_cont]
    simp [resetChip, resetState, contentsReset, absChip, Machine.resetStep, Machine.State.init]

/-! ## The active cycle -/

/-- The memory/config contents after one active step.  The machine keeps its own
memory path, so this is machine determinism under `ChipRel` (not a
cut-vs-machine claim); see `CHIPCUT_NOTES.md` §3.2. -/
structure ContentsEq (s : State) (m : Machine.State) (pin : Machine.PinIn) : Prop where
  mout : ∀ c : Fin 2, (Machine.step m pin).cores[c].mout = (activeStep s pin).cont.mout[c.val]
  cfg : (Machine.step m pin).cfg = (activeStep s pin).cont.cfg
  pmem : (Machine.step m pin).pmem = (activeStep s pin).cont.pmem
  dmem : (Machine.step m pin).dmem = (activeStep s pin).cont.dmem
  ramOut : (Machine.step m pin).ramOut = (activeStep s pin).cont.ramOut
  ramOwner : (Machine.step m pin).ramOwner = (activeStep s pin).cont.ramOwner
  ramLane : (Machine.step m pin).ramLane = (activeStep s pin).cont.ramLane

/-- Every remaining field group of one active cycle, as a named hypothesis.
`CHIPCUT_NOTES.md` §3.2 records the bridge and the missing wiring equality for
each field. -/
structure Premises (s : State) (m : Machine.State) (pin : Machine.PinIn) : Prop where
  sync : SyncRel (activeStep s pin).sync (Machine.step m pin).sync
  lines : ∀ l : Fin 4,
    (Machine.step m pin).lines[l] = Bridge.Line.absSt (lineAt (activeStep s pin) l.val)
  threads : ∀ t : Fin 6,
    (Machine.step m pin).threads[t] =
      Bridge.Thread.absState (threadAt (activeStep s pin) t.val)
  cores : ∀ c : Fin 2,
    CoreRegsRel ((activeStep s pin).cores[c.val]) (Machine.step m pin).cores[c]
  units : UnitsRel (activeStep s pin) (Machine.step m pin).units
  p0 : P0Rel (Machine.step m pin).p0 (activeStep s pin).p0
  streams : ∀ k : Fin 2,
    Bridge.StreamB.AbsRelB (k.val == 0) (streamAt (activeStep s pin) k.val)
      (Machine.step m pin).streams[k]
  host : Bridge.Host.LinkRelR (activeStep s pin).hostRead (activeStep s pin).hostCmd.cmd
    (Machine.step m pin)
  hostReq : (Machine.step m pin).host.req = Bridge.Mem.absSlot (activeStep s pin).p0
  ctrl : CtrlRel (activeStep s pin) (Machine.step m pin).ctrl
  dbg : DbgRel (activeStep s pin) (Machine.step m pin).dbg
  cw : CwRel (Machine.step m pin).cw (activeStep s pin).cq (activeStep s pin).arb
  bank : BankRel (activeStep s pin).bank (Machine.step m pin).cfg
  contents : ContentsEq s m pin
  out : (Machine.step m pin).out = (activeStep s pin).outPins
  oen : (Machine.step m pin).oen = (activeStep s pin).oenPins

/-- **Chip step refinement.**  Under the reachable-state invariants and the
named active-cycle premises, one product step refines one machine step field by
field.  A reset cycle needs no premise (`chip_reset_refines_rel`). -/
theorem chip_step_refines (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hprem : runRst s pin = true → Premises s m pin)
    (hrelease : runRst s pin = false → pin.rstn = true →
      MaskedZero (Machine.cfgNext m.cfg m.cw)) :
    ChipRel (step s pin) (Machine.step m pin) := by
  by_cases h : runRst s pin = true
  · have hp := hprem h
    have hrstn : pin.rstn = true := by
      have hc : (s.rst.rstQ && pin.rstn) = true := by simpa [runRst] using h
      exact (Bool.and_eq_true_iff.mp hc).2
    have hstep : step s pin = activeStep s pin := by simp [step, h]
    have hmach : Machine.step m pin = (Machine.runStep m pin).1 := by
      have hq : (m.rq && pin.rstn) = true := by rw [← hrel.rstQ]; exact h
      simp [Machine.step, Machine.stepObs, hq]
    rw [hstep]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmach]
      simp [activeStep, Debug.Reset.step, Machine.runStep, hrstn]
    · rw [hmach]
      simp [activeStep, Debug.Reset.step, Machine.runStep, hrstn]
      exact hrel.rstM
    · rw [hmach]
      simp [activeStep, rqhNext, Machine.runStep, h, hrstn, Machine.Util.bv, hrel.rqh]
    · exact hp.sync
    · exact hp.lines
    · exact hp.threads
    · exact hp.cores
    · exact hp.contents.mout
    · exact hp.units
    · exact hp.p0
    · exact hp.streams
    · exact hp.host
    · exact hp.hostReq
    · exact hp.ctrl
    · exact hp.dbg
    · exact hp.cw
    · exact hp.bank
    · exact hp.out
    · exact hp.oen
    · exact hp.contents.cfg
    · exact hp.contents.pmem
    · exact hp.contents.dmem
    · exact hp.contents.ramOut
    · exact hp.contents.ramOwner
    · exact hp.contents.ramLane
  · have hfalse : runRst s pin = false := by simpa using h
    exact chip_reset_refines_rel s m pin hrel hfalse (hrelease hfalse)

/-! ## Traces -/

/-- The product trace. -/
def cutStateAt (pins : Nat → Machine.PinIn) (init : State) : Nat → State
  | 0 => init
  | n + 1 => step (cutStateAt pins init n) (pins n)

/-- The machine trace. -/
def machineStateAt (pins : Nat → Machine.PinIn) (init : Machine.State) : Nat → Machine.State
  | 0 => init
  | n + 1 => Machine.step (machineStateAt pins init n) (pins n)

theorem cutStateAt_succ (pins : Nat → Machine.PinIn) (init : State) (n : Nat) :
    cutStateAt pins init (n + 1) = step (cutStateAt pins init n) (pins n) := rfl

theorem machineStateAt_succ (pins : Nat → Machine.PinIn) (init : Machine.State) (n : Nat) :
    machineStateAt pins init (n + 1) = Machine.step (machineStateAt pins init n) (pins n) := rfl

/-- The selected line of the power-on state is a resetted line. -/
theorem lineAt_resetState (cont : Contents) (n : Nat) :
    lineAt (resetState cont) n = Line.resetState := by
  unfold lineAt resetState
  split <;> simp

/-- The selected thread of the power-on state is a resetted thread. -/
theorem threadAt_resetState (cont : Contents) (n : Nat) :
    threadAt (resetState cont) n = Thread.resetState := by
  unfold threadAt resetState
  split <;> simp

/-- The selected stream of the power-on state is a resetted stream. -/
theorem streamAt_resetState (cont : Contents) (n : Nat) :
    streamAt (resetState cont) n = Stream.resetState := by
  unfold streamAt resetState
  split <;> simp

/-- The invariant holds along the product trace. -/
theorem inv_trace (pins : Nat → Machine.PinIn) (cont : Contents) :
    ∀ n, Inv (cutStateAt pins (resetState cont) n) := by
  intro n
  induction n with
  | zero => exact inv_reset cont
  | succ n ih =>
    rw [cutStateAt_succ]
    exact inv_step _ _ ih

/-- The reset product relates to its canonical abstraction. -/
theorem rel_reset (cont : Contents) (hzero : MaskedZero cont.cfg) :
    ChipRel (resetState cont) (absChip (resetState cont)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · simp only [absChip, resetState, SpiPins.resetState]
    unfold SyncRel
    refine ⟨?_, ?_, ?_⟩ <;> decide
  · intro l
    rw [lineAt_resetState]
    simp [absChip, resetState, Bridge.Line.absSt, Line.resetState]
  · intro t
    rw [threadAt_resetState]
    simp [absChip, resetState, Bridge.Thread.absState, Thread.resetState]
  · intro c
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [absChip, resetState, Bridge.Core.absCore]
  · intro c
    simp [absChip, resetState, Bridge.Core.absCore]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [absChip, resetState, Glue.resetState]
    · simp [absChip, resetState, Glue.resetState]
    · simp [absChip, resetState, Units.Acc.resetState]
    · simp [absChip, resetState, Units.Acc.resetState]
    · simp [absChip, resetState, Units.Acc.resetState]
    · simp [absChip, resetState, Units.Acc.resetState]
    · intro k
      simp [absChip, resetState, Units.Acc.resetState]
    · intro k
      rw [shAt_resetState]
      simp [absChip, resetState, Units.Shifter.resetState]
    · intro k
      rw [cntAt_resetState]
      simp [absChip, resetState, Units.Counter.resetState]
    · intro k
      rw [lfAt_resetState]
      simp [absChip, resetState, Units.Lfsr.resetState]
  · show P0Rel (Bridge.Mem.absP0 (resetState cont).p0) (resetState cont).p0
    exact p0Rel_abs _
  · intro k
    rw [streamAt_resetState]
    unfold Bridge.StreamB.AbsRelB Bridge.StreamB.BufRel
    simp [absChip, resetState, Bridge.StreamB.abs, Stream.resetState]
  · have hh : (absChip (resetState cont)).host = Machine.State.init.host := by
      simp [absChip, resetState, Machine.State.init, HostCmd.resetState, HostRead.resetState,
        nbyteOf, cmdOf, Bridge.Mem.absSlot, Mem.resetState]
    exact linkRelR_host_congr hh Bridge.Host.linkRelR_reset
  · simp [absChip, resetState, Mem.resetState, Bridge.Mem.absSlot]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [absChip, resetState, Glue.resetState]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [absChip, resetState, CoreCtl.freezeReset, Debug.Ctrl.resetState,
        Debug.Digest.resetState]
  · show CwRel (Bridge.CfgWrite.cwOf (resetState cont).cq (resetState cont).arb)
      (resetState cont).cq (resetState cont).arb
    exact cwRel_abs _ _
  · exact bankRel_reset _ hzero
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- During reset release, the bank is still clear and its write stage is idle. -/
theorem bank_reset_trace (pins : Nat → Machine.PinIn) (cont : Contents) (n : Nat) :
    let s := cutStateAt pins (resetState cont) n
    (s.rst.rstQ = true → s.rst.rstM = true) ∧
    (s.rst.rstQ = false → (∀ k, Bank.read s.bank k = 0) ∧ s.arb.previousWrite = false) := by
  induction n with
  | zero =>
    simp [cutStateAt, resetState, Debug.Reset.resetState, Bank.read]
  | succ n ih =>
    rw [cutStateAt_succ]
    let s := cutStateAt pins (resetState cont) n
    let pin := pins n
    change (s.rst.rstQ = true → s.rst.rstM = true) ∧ _ at ih
    change ((step s pin).rst.rstQ = true → (step s pin).rst.rstM = true) ∧
      ((step s pin).rst.rstQ = false →
        (∀ k, Bank.read (step s pin).bank k = 0) ∧ (step s pin).arb.previousWrite = false)
    by_cases hact : runRst s pin = true
    · have hrun : (s.rst.rstQ && pin.rstn) = true := hact
      obtain ⟨hq, hn⟩ := Bool.and_eq_true_iff.mp hrun
      have hm := ih.1 hq
      rw [show step s pin = activeStep s pin from if_pos hact]
      simp [activeStep, Debug.Reset.step, hn, hm]
    · rw [show step s pin = resetChip s pin from if_neg hact]
      cases hn : pin.rstn <;>
        simp [resetChip, resetState, Debug.Reset.step, Debug.Reset.resetState, hn, Bank.read]

/-- On a reset-release edge of a related trace, the staged configuration is clear. -/
theorem maskedZero_release_trace (pins : Nat → Machine.PinIn) (cont : Contents) (n : Nat)
    (m : Machine.State) (hrel : ChipRel (cutStateAt pins (resetState cont) n) m)
    (hrun : runRst (cutStateAt pins (resetState cont) n) (pins n) = false)
    (hn : (pins n).rstn = true) :
    MaskedZero (Machine.cfgNext m.cfg m.cw) := by
  let s := cutStateAt pins (resetState cont) n
  have hq : s.rst.rstQ = false := by
    change (s.rst.rstQ && (pins n).rstn) = false at hrun
    simpa only [hn, Bool.and_true] using hrun
  obtain ⟨hbank, hw⟩ := (bank_reset_trace pins cont n).2 hq
  obtain ⟨-, -, -, -, hbwp, -, -, -, -, -⟩ := hrel.cw
  rw [show Machine.cfgNext m.cfg m.cw = m.cfg by simp [Machine.cfgNext, hbwp, hw]]
  intro k
  simpa only [hrel.bank.1, Machine.Util.cfgByte, Nat.add_sub_cancel_left, hbank k]
    using (hrel.bank.2 k).symm

/-- Trace refinement from a cleared implemented latch image, with bridge
premises on active cycles. -/
theorem trace_refines (pins : Nat → Machine.PinIn) (cont : Contents) (hzero : MaskedZero cont.cfg)
    (hprem : ∀ n, runRst (cutStateAt pins (resetState cont) n) (pins n) = true →
      Premises (cutStateAt pins (resetState cont) n)
        (machineStateAt pins (absChip (resetState cont)) n) (pins n)) :
    ∀ n, ChipRel (cutStateAt pins (resetState cont) n)
      (machineStateAt pins (absChip (resetState cont)) n) := by
  intro n
  induction n with
  | zero => exact rel_reset cont hzero
  | succ n ih =>
    rw [cutStateAt_succ, machineStateAt_succ]
    exact chip_step_refines _ _ _ ih (inv_trace pins cont n) (hprem n)
      (maskedZero_release_trace pins cont n _ ih)

end Metronome.ChipCut
