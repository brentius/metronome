/-
Scratch acceptance checks for `Metronome/ChipCut/Discharge/PremiseWire.lean`.

Not part of the library; run with

  cd code/tests/lean
  lake env lean ..\..\..\data\raw\lean_chipcut_premise_v4_20261122\check_fields.lean

1. the two theorems have exactly the `ExplicitPremises` field types;
2. an `ExplicitPremises` record can be rebuilt with only those two fields
   replaced, at the trace states `trace_refines'` consumes;
3. axiom footprint (no `sorryAx`, no extra axioms beyond the `bv_decide`
   certificates);
4. a negative control: the `cwH19` statement is *not* true of arbitrary
   (unreachable) states, so the trace/invariant framing is essential.
-/

import Metronome.ChipCut.Assembly
import Metronome.ChipCut.Discharge.PremiseWire

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Metronome

/-! ### 1. Field types -/

example (s : ChipCut.State) (pin : Machine.PinIn) :
    ChipCut.Discharge.MoveFabricKeyed.GrpPacked s pin :=
  ChipCut.Discharge.PremiseWire.grpPacked_holds s pin

example (pins : Nat → Machine.PinIn) (cont : ChipCut.Contents) (n : Nat) :
    ¬ ((ChipCut.cutStateAt pins (ChipCut.resetState cont) n).arb.heldValid = true ∧
      (ChipCut.hostCfgOf (ChipCut.cutStateAt pins (ChipCut.resetState cont) n)).isSome = true) :=
  ChipCut.Discharge.PremiseWire.cwH19_trace pins cont n

/-! ### 2. Rebuilding `ExplicitPremises` at a trace state -/

example (pins : Nat → Machine.PinIn) (cont : ChipCut.Contents) (n : Nat)
    (hexp : ChipCut.ExplicitPremises (ChipCut.cutStateAt pins (ChipCut.resetState cont) n)
      (ChipCut.machineStateAt pins (ChipCut.absChip (ChipCut.resetState cont)) n) (pins n)) :
    ChipCut.ExplicitPremises (ChipCut.cutStateAt pins (ChipCut.resetState cont) n)
      (ChipCut.machineStateAt pins (ChipCut.absChip (ChipCut.resetState cont)) n) (pins n) :=
  { hexp with
    grpPacked := ChipCut.Discharge.PremiseWire.grpPacked_holds _ (pins n)
    cwH19 := ChipCut.Discharge.PremiseWire.cwH19_trace pins cont n }

/-! ### 3. Axiom footprint -/

#print axioms ChipCut.Discharge.PremiseWire.grpPacked_holds
#print axioms ChipCut.Discharge.PremiseWire.cwH19_trace
#print axioms ChipCut.Discharge.PremiseWire.mapOfWith_slice

/-! ### 4. Negative control: the overlap exists at an unreachable state

`heldValid` and a host configuration write *can* coincide in an arbitrary state
(nothing in `HostPinInv` forbids `heldValid = true` with `wr = true` and
`bitc = 0`); it just cannot be reached from reset.  Hence `cwH19` is stated
along the trace, not for every state. -/

example (a : BitVec 16) (ha : Machine.Config.isCfgAddr a.toNat = true) :
    ∃ s : ChipCut.State, s.arb.heldValid = true ∧ (ChipCut.hostCfgOf s).isSome = true := by
  refine ⟨{ ChipCut.resetState ChipCut.Contents.init with
      arb := { (ChipCut.resetState ChipCut.Contents.init).arb with heldValid := true },
      hostCmd := { (ChipCut.resetState ChipCut.Contents.init).hostCmd with
        wr := true, addr := a } }, rfl, ?_⟩
  simp [ChipCut.hostCfgOf, ChipCut.hwOf, ha]
