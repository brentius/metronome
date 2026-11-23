/-
# ChipCut: two `ExplicitPremises` fields are theorems

`Metronome/ChipCut/Assembly.lean` states the headline refinement
`Metronome.ChipCut.trace_refines'` under `ExplicitPremises` (Assembly.lean ~78).
Two of those fields are not assumptions about the design's configuration or its
environment at all; they are consequences of the cut's own wiring and of the
host link's reachable state:

* `grpPacked : Discharge.MoveFabricKeyed.GrpPacked s pin` — the cut defines the
  packed group bus as `mvGrp = Moves.mapOf (mvDst)` (`Wire.lean` ~347), and
  `Moves.mapOf` is `Moves.mapOfWith DG_MAP` (`Moves.lean` ~100), whose body is
  the six-slot OR of `DG_MAP[dst_q]` (`Moves.lean` ~90).  `grpPacked_holds`
  proves the per-slot identity `grp_q = dgTable dst_q` for every state and
  every pin input, by the six-slot slicing lemma `pack6_slice`.

* `cwH19 : ¬ (s.arb.heldValid = true ∧ (hostCfgOf s).isSome = true)` — AMBIG 19
  ("a new host configuration write arriving while a held one is pending").  This
  is a reachable invariant of the host link plus the arbiter, **not** an extra
  timing assumption: `Config.heldValid_next` makes `heldValid` mean "the
  previous cycle wrote the bank *and* a host configuration write is offered this
  cycle", while `(hostCfgOf s).isSome` means the registered `wr` strobe is up.
  `HostPinInv.wrBitc` (a one-cycle-pulse fact: `wr` is only ever up in the cycle
  after a completing byte, when `bitc` has just been cleared) then forces
  `bitc = 0` on the same state whose `hostCfgOf` is `some`, whereas
  `HostCmd.wrNext`'s `completing` conjunct forces `bitc = 7`.  So the overlap is
  excluded with no SCK-spacing hypothesis: `Discharge.host_sck_spacing` is not
  needed, and neither is a "≥ 8 SCK edges apart" timing fact.

`cwH19_step` is the preservation step (from `HostPinInv s` to the property of
`step s pin`, reset branch included) and `cwH19_trace` is the from-reset trace
statement, in the shape `trace_refines'` consumes at each cycle.

No `sorry`, no `native_decide`.  Nothing outside this file was edited.
-/

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
open Metronome.ChipCut.Discharge.MoveFabric

/-! ## 1. The group-packing identity (`GrpPacked`)

The RTL builds `grp_v = {grp[5], …, grp[0]}` from six independent 5-bit table
lookups (`Moves.mapOfWith`, the shift-and-OR form of `Moves.lean` ~90).  The
only missing step is that a 5-bit slice at `5 * q` of that OR is slot `q`'s
lookup, which `pack6_slice` proves by `bv_decide` on each of the six slots. -/

/-- Six `5`-bit group words packed the way `Moves.mapOfWith` packs them. -/
def pack6 (x0 x1 x2 x3 x4 x5 : BitVec 5) : BitVec 30 :=
  BitVec.setWidth 30 x0 ||| BitVec.shiftLeft (BitVec.setWidth 30 x1) 5 |||
    BitVec.shiftLeft (BitVec.setWidth 30 x2) 10 |||
    BitVec.shiftLeft (BitVec.setWidth 30 x3) 15 |||
    BitVec.shiftLeft (BitVec.setWidth 30 x4) 20 |||
    BitVec.shiftLeft (BitVec.setWidth 30 x5) 25

/-- Slot `q`'s word of a six-word packing. -/
def grpAt (q : Nat) (x0 x1 x2 x3 x4 x5 : BitVec 5) : BitVec 5 :=
  match q with
  | 0 => x0
  | 1 => x1
  | 2 => x2
  | 3 => x3
  | 4 => x4
  | _ => x5

/-- **The six-slot slicing lemma.**  Slot `q`'s 5-bit field of the packed word
is exactly the `q`-th input word. -/
theorem pack6_slice (x0 x1 x2 x3 x4 x5 : BitVec 5) (q : Nat) (hq : q < 6) :
    CoreCtl.slice (pack6 x0 x1 x2 x3 x4 x5) (5 * q) 5 =
      grpAt q x0 x1 x2 x3 x4 x5 := by
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold CoreCtl.slice grpAt pack6
    bv_decide

/-- **`mapOfWith` sliced.**  Slot `q` of `Moves.mapOfWith tab dst` is the
`tab` lookup of slot `q`'s destination word. -/
theorem mapOfWith_slice (tab : BitVec 320) (dst : BitVec 36) (q : Nat) (hq : q < 6) :
    CoreCtl.slice (Moves.mapOfWith tab dst) (5 * q) 5 =
      Moves.dgLookupAt tab (CoreCtl.slice dst (6 * q) 6) := by
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold Moves.mapOfWith
    exact pack6_slice _ _ _ _ _ _ _ (by omega)

/-- **`GrpPacked` is not a premise: it is the cut's own wiring.**  For every
state and pin input, slot `q`'s group word is `DG_MAP` of slot `q`'s
destination word (`mvGrp = Moves.mapOf (mvDst)` and `dgTable = DG_MAP[_]`). -/
theorem grpPacked_holds (s : State) (pin : Machine.PinIn) :
    MoveFabricKeyed.GrpPacked s pin := by
  intro q hq
  have hg : ((movBundle s pin).get q).group =
      CoreCtl.slice (mvGrp s pin) (5 * q) 5 :=
    MoveFabricKeyed.bundle_grp (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
      (mvXl s) (mvXt s) q hq
  have hd : ((movBundle s pin).get q).dst =
      CoreCtl.slice (mvDst s pin) (6 * q) 6 :=
    bundle_dst (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
      (mvXl s) (mvXt s) q hq
  rw [hg, hd]
  unfold mvGrp Moves.mapOf Moves.dgTable
  exact mapOfWith_slice Moves.dgMapLiteral (mvDst s pin) q hq

/-! ## 2. AMBIG 19 (`cwH19`): no host configuration write while `HH` waits

The arbiter holds a host write only for one cycle, and only in the cycle after a
bank write (`Config.heldValid_next`: `heldValid' = previousWrite && hostValid`).
`hostValid` is `(hostCfgOf s).isSome`, i.e. the registered host `wr` strobe is
up.  `wr` is a one-cycle pulse raised by `HostCmd.wrNext` on the *completing*
edge of a data byte, and `HostCmd.bitcNext` clears the bit counter on that same
edge, so `HostPinInv.wrBitc` gives `bitc = 0` whenever `wr` is up.  A host
configuration write and a *completing* host byte therefore cannot share a cycle:
the latter needs `bitc = 7`.  The overlap AMBIG 19 describes is thus empty on
every reachable state, with no SCK-pacing hypothesis. -/

/-- `hostCfgOf` is `some` only when the registered write strobe is up. -/
theorem hostCfgOf_isSome_wr (s : State) (h : (hostCfgOf s).isSome = true) :
    s.hostCmd.wr = true := by
  cases hw : s.hostCmd.wr with
  | true => rfl
  | false => simp [hostCfgOf, hwOf, hw] at h

/-- A completing host byte has a full bit counter. -/
theorem completing_bitc (s : HostCmd.State) (i : HostCmd.Input)
    (h : HostCmd.completing s i = true) : s.bitc = 7 := by
  unfold HostCmd.completing at h
  have hb : (s.bitc == 7) = true := and_right h
  simpa using hb

/-- **AMBIG 19 is excluded at every reachable state.**  If `HostPinInv` holds at
`s`, then the next state has no host configuration write overlapping a held
`HH`.  (The reset branch is immediate: the arbiter state is cleared.) -/
theorem cwH19_step (s : State) (pin : Machine.PinIn) (hpinv : HostPinInv s) :
    ¬ ((step s pin).arb.heldValid = true ∧
      (hostCfgOf (step s pin)).isSome = true) := by
  rintro ⟨hheld, hcfg⟩
  by_cases hact : runRst s pin = true
  · rw [step, if_pos hact] at hheld hcfg
    -- `heldValid` at the next state means a host write is offered now …
    have hheld' := hheld
    rw [show ((activeStep s pin).arb).heldValid =
      (Config.step s.arb (arbIn s)).next.heldValid from rfl] at hheld'
    rw [Config.heldValid_next] at hheld'
    have hhost : (arbIn s).hostValid = true := and_right (and_right hheld')
    have hwr : s.hostCmd.wr = true :=
      hostCfgOf_isSome_wr s (by simpa [arbIn, Bridge.CfgWrite.cfgIn] using hhost)
    -- … so `bitc = 0` now (`wr` is a one-cycle pulse), …
    have h0 : s.hostCmd.bitc = 0 := hpinv.wrBitc hwr
    -- … while a `hostCfgOf` at the next state is a completing byte now.
    have hwr' : HostCmd.wrNext s.hostCmd (hostCmdIn s pin) = true := by
      have hw := hostCfgOf_isSome_wr (activeStep s pin) hcfg
      simpa [activeStep, HostCmd.step] using hw
    have h7 : s.hostCmd.bitc = 7 :=
      completing_bitc s.hostCmd (hostCmdIn s pin) (wrNext_completing _ _ hwr')
    rw [h0] at h7
    exact absurd h7 (by decide)
  · rw [step, if_neg hact] at hheld
    simp [resetChip, resetState] at hheld

/-- The property holds at reset. -/
theorem cwH19_reset (cont : Contents) :
    ¬ ((resetState cont).arb.heldValid = true ∧
      (hostCfgOf (resetState cont)).isSome = true) := by
  simp [resetState]

/-- `HostPinInv` along the product trace. -/
theorem hostPinInv_trace (pins : Nat → Machine.PinIn) (cont : Contents) :
    ∀ n, HostPinInv (cutStateAt pins (resetState cont) n)
  | 0 => hostPinInv_reset cont
  | n + 1 => by
    rw [cutStateAt_succ]
    exact hostPinInv_step _ _ (hostPinInv_trace pins cont n)

/-- **AMBIG 19 along every trace from reset**: no cycle has a held `HH` and a
host configuration write at once.  This is the shape
`ExplicitPremises.cwH19` needs at each cycle of `trace_refines'`. -/
theorem cwH19_trace (pins : Nat → Machine.PinIn) (cont : Contents) :
    ∀ n, ¬ ((cutStateAt pins (resetState cont) n).arb.heldValid = true ∧
      (hostCfgOf (cutStateAt pins (resetState cont) n)).isSome = true)
  | 0 => cwH19_reset cont
  | n + 1 => by
    rw [cutStateAt_succ]
    exact cwH19_step _ _ (hostPinInv_trace pins cont n)

end Metronome.ChipCut.Discharge.PremiseWire
