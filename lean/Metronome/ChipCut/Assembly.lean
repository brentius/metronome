/-
# ChipCut assembly: the named wiring lemmas in one refinement theorem

`Metronome/ChipCut/Proof.lean` states the whole-chip refinement from sixteen
named per-cycle premises (`Premises`).  The five `Discharge/*.lean` files prove
each of those fields from *explicitly named wiring hypotheses*, and the
`WIRE_*`/`MoveFabric*`/`LineMoveWire`/`StreamMoveWire` files discharge those
hypotheses.  This file is the capstone: it

* exposes global decode tables, initial contents conditions, and cycle contracts;
* proves all sixteen `Premises` fields using the discharge lemmas;
* derives `chip_step_refines'` and the from-reset trace corollary
  `trace_refines'`, whose invariants all come from their `_trace` theorems.
-/

import Metronome.ChipCut.Discharge.Glue
import Metronome.ChipCut.Discharge.LineThread
import Metronome.ChipCut.Discharge.CoreUnits
import Metronome.ChipCut.Discharge.MemHostCfg
import Metronome.ChipCut.Discharge.StreamDbg
import Metronome.ChipCut.Discharge.GuardSrc
import Metronome.ChipCut.Discharge.HostPinWire
import Metronome.ChipCut.Discharge.CoreCombWire
import Metronome.ChipCut.Discharge.CoreCombCbs
import Metronome.ChipCut.Discharge.MoveFabric
import Metronome.ChipCut.Discharge.MoveFabricUnits
import Metronome.ChipCut.Discharge.MoveFabricKeyed
import Metronome.ChipCut.Discharge.MovePayloadWire
import Metronome.ChipCut.Discharge.DbgMapWire
import Metronome.ChipCut.Discharge.CapTrace
import Metronome.Bridge.StreamBuf
import Metronome.ChipCut.Discharge.StreamMoveWire
import Metronome.ChipCut.Discharge.LineMoveWire
import Metronome.ChipCut.Discharge.WindowWire
import Metronome.ChipCut.Discharge.PremiseWire

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

namespace Metronome.ChipCut

open Metronome

/-! ## The genuine premises -/

/-- Constant decode-table facts checked by compiled evaluation. -/
structure Tables : Prop where
  /-- `Machine.srcOp` is the computable source-name decode. -/
  srcTable : Bridge.Glue.SrcTable
  /-- `Machine.guardOp` is the computable guard-name decode. -/
  guardTable : Bridge.Glue.GuardTable
  /-- The jump-guard name table is the cut's `JG_TABLE`. -/
  jgTable : Discharge.MoveFabricKeyed.JGTable
  /-- The destination-kind table (`NULL`/`L.SYM`/`T.STOP`/other). -/
  dstKind : Bridge.Moves.DstKindTable
  /-- The destination-payload table (`payload`/`nonkeyed`/`codeOf`/`accRange`). -/
  dstPayload : Discharge.MoveFabric.DstPayloadTable
  /-- The checked `FLAGS`/`P0`/`CW` code table (W5's `MovePayloadWire`; 64 codes
  × 11 rows, compiled evaluation 0 failures) — it supplies the payload rows of
  `FLAGS.SET`/`CLR` (5/6), `P0.AL/AH/W/R` (43..46) and `CW.AL/AH/D` (58..60). -/
  dstFlagP0Cw : Discharge.MovePayloadWire.DstFlagP0CwTable
  /-- The multi-code port table of the shifter/counter/LFSR groups. -/
  dstPort : Discharge.MoveFabric.DstPortTable
  /-- The stream/line-control code table and the `L.SYM` code identity. -/
  dstStreamLine : Discharge.MoveFabricKeyed.DstStreamLineTable
/-- Power-on RAM ownership and configuration image conditions. -/
structure InitialConditions (cont : Contents) : Prop where
  ramOwner : cont.ramOwner = 0
  maskedZero : Discharge.BankWire.MaskedZero cont.cfg
  cfgSize : cont.cfg.img.size = Machine.Util.cfgSize

/-- The host spacing and stream mode contracts for one pin sample on the cut trace. -/
structure PinPremises (s : State) (pin : Machine.PinIn) : Prop where
  hostSckSpacing : Discharge.host_sck_spacing s pin
  streamModeQuiet : Discharge.stream_mode_quiet s pin

/-! ## A cut-side invariant helper -/

/-- `HostPinInv` along the product trace (`Discharge.hostPinInv_reset` +
`hostPinInv_step`). -/
theorem hostPinInv_trace (pins : Nat → Machine.PinIn) (cont : Contents) :
    ∀ n, Discharge.HostPinInv (cutStateAt pins (resetState cont) n) := by
  intro n
  induction n with
  | zero => exact Discharge.hostPinInv_reset cont
  | succ n ih =>
    rw [cutStateAt_succ]
    exact Discharge.hostPinInv_step _ _ ih

/-! ## Small adapters that remove `Premises` mismatches

Two mismatches are bridged here rather than carried: the stream-mode
congruence (so `StreamWire.mode` is a theorem) and the `LandingP0` form of
`premise_p0`'s landing hypothesis (so the false `LandingRel` is not needed). -/

/-- `machMode` is fixed by `ChipRel` (it reads `cfg` and the two debug bits). -/
theorem machMode_congr (s : State) (m : Machine.State) (hrel : ChipRel s m) (k : Fin 2) :
    Discharge.machMode m k = Discharge.machMode (absChip s) k := by
  obtain ⟨-, -, -, -, -, hcen, hrpl, -, -, -, -⟩ := hrel.dbg
  have hc : m.cfg = (absChip s).cfg := by rw [hrel.cfg]; rfl
  unfold Discharge.machMode Machine.streamMode
  rw [hc, hcen, hrpl]
  rfl

/-- **`StreamWire.mode`**, not a premise: the machine's mode of the cycle
is the bridge's `modeOf` (`Discharge.absMode_eq` is the abstraction's half). -/
theorem streamWire_mode (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (k : Fin 2) :
    Discharge.machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val) :=
  (machMode_congr s m hrel k).trans (Discharge.absMode_eq s pin k)

/-- **`premise_p0`'s landing hypothesis**, not a premise: the `LandingP0`
invariant plus `ChipRel.ramOwner` is exactly the `p0_open_land` hypothesis
(only the P0 clause of the false `LandingRel` is used). -/
theorem p0_open_land_of_landingP0 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (h : Discharge.LandingP0 s) :
    (m.ramOwner == 3) = (s.p0.land && !(memIn s pin).frzd) := by
  rw [hrel.ramOwner, h]
  rfl

/-- `DbgWire`'s `hword` is definitional. -/
theorem dbgWire_hword (s : State) (pin : Machine.PinIn) :
    (dbgCtrlIn s pin).replayWord = (streamAt s 0).wb := rfl

/-- Bit 0 of the two-stream `replayValid` word is stream 0's `WV`, the RTL's
`s_replay_valid[0]` (`project.v:442/465`).  This is what makes `DbgWire.happly`
true after the `Wire.lean` operand fix. -/
theorem bitAt_replayValid (s : State) (pin : Machine.PinIn) :
    Debug.bitAt (dbgCtrlIn s pin).replayValid 0 = (streamAt s 0).wv := by
  simp only [Debug.bitAt, dbgCtrlIn]
  by_cases h0 : (streamAt s 0).wv <;> by_cases h1 : (streamAt s 1).wv <;>
    simp [h0, h1]

/-- **`Premises.contents` from the projection.**  `premise_contents` consumes
`contents_open_cbs`, the whole-bundle equality that is *false*
(`CoreCombCbs.contents_open_cbs_counterexample`).  The five fields `coreNext`
reads are congruent by `contents_open_proj_abs`; `contents_mout_of_fetch` turns
their `fetch` component into the `mout` field; the other six fields are the body
of `premise_contents`.  The capture-buffer `PV` slot comes from A2's `CapInv`
(`contents_open_req_cap`), not a named `PV → WB` fact. -/
theorem premise_contents_proj (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hfetch : ∀ c : Fin 2,
      (Discharge.mhcCbs m pin)[c].fetch = (Discharge.mhcCbs (absChip s) pin)[c].fetch)
    (contents_open_req : Discharge.mhcReq m pin = Discharge.mhcReq (absChip s) pin)
    (contents_open_served : Discharge.mhcServed m pin = Discharge.mhcServed (absChip s) pin) :
    ContentsEq s m pin := by
  have hq : (m.rq && pin.rstn) = true := by rw [← hrel.rstQ]; exact hact
  have hq2 : ((absChip s).rq && pin.rstn) = true := by simpa [absChip, runRst] using hact
  have hmach : Machine.step (absChip s) pin = (Machine.runStep (absChip s) pin).1 := by
    simp [Machine.step, Machine.stepObs, hq2]
  have hhw : Discharge.mhcHw m pin = Discharge.mhcHw (absChip s) pin :=
    Discharge.mhcHw_bridge s m pin hinv hrel
  have hpw : Discharge.mhcPw m pin = Discharge.mhcPw (absChip s) pin := by
    simp only [Discharge.mhcPw, hhw]
  have hfrz : m.dbg.frz = (absChip s).dbg.frz := by
    rw [Discharge.dbgRel_frz hrel.dbg]; rfl
  have hdmemA : (absChip s).dmem = s.cont.dmem := rfl
  have hramOutA : (absChip s).ramOut = s.cont.ramOut := rfl
  have hram : Discharge.mhcRam m pin = Discharge.mhcRam (absChip s) pin := by
    simp only [Discharge.mhcRam, hrel.dmem, hrel.ramOut, hdmemA, hramOutA, contents_open_req]
  have howner : Discharge.mhcOwner m pin = Discharge.mhcOwner (absChip s) pin := by
    simp only [Discharge.mhcOwner, contents_open_req, contents_open_served]
  have hlaneN : Discharge.mhcLaneN m pin = Discharge.mhcLaneN (absChip s) pin := by
    simp only [Discharge.mhcLaneN, contents_open_req, contents_open_served]
  have hramM := Discharge.step_ram m pin hq
  have hramA := Discharge.step_ram (absChip s) pin hq2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    exact Discharge.contents_mout_of_fetch s m pin hrel hact hfetch c
  · rw [Discharge.step_cfg m pin hq]
    show Machine.cfgNext m.cfg m.cw = ((Machine.runStep (absChip s) pin).1).cfg
    rw [← hmach, Discharge.step_cfg (absChip s) pin hq2]
    rw [show (absChip s).cfg = m.cfg from hrel.cfg.symm]
    rw [show (absChip s).cw = Bridge.CfgWrite.cwOf s.cq s.arb from rfl]
    exact cfgNext_cwRel hrel.cw rfl
  · rw [Discharge.step_pmem m pin hq]
    show (match Discharge.mhcPw m pin with
        | some (c, a, v) =>
          Machine.Util.vset m.pmem c (Machine.Util.bset (Machine.Util.vget m.pmem c) a v)
        | none => m.pmem) = ((Machine.runStep (absChip s) pin).1).pmem
    rw [← hmach, Discharge.step_pmem (absChip s) pin hq2]
    rw [show (absChip s).pmem = m.pmem from hrel.pmem.symm, hpw]
    rfl
  · rw [hramM.1]
    show (Discharge.mhcRam m pin).1 = ((Machine.runStep (absChip s) pin).1).dmem
    rw [← hmach, hramA.1, hram]
  · rw [hramM.2.1]
    show Machine.Util.bv 32 (Discharge.mhcRam m pin).2.1 =
      ((Machine.runStep (absChip s) pin).1).ramOut
    rw [← hmach, hramA.2.1, hram]
  · rw [hramM.2.2.1]
    show Discharge.mhcOwner m pin = ((Machine.runStep (absChip s) pin).1).ramOwner
    rw [← hmach, hramA.2.2.1, howner]
  · rw [hramM.2.2.2]
    show Machine.Util.bv 2 (Discharge.mhcLaneN m pin) = ((Machine.runStep (absChip s) pin).1).ramLane
    rw [← hmach, hramA.2.2.2, hlaneN]

/-! ## The projected stream input (`StreamInputAgree`) -/

/-- `isSome` of a mapped option. -/
theorem option_isSome_map {α β : Type} (f : α → β) (o : Option α) :
    (o.map f).isSome = o.isSome := by cases o <;> rfl

/-- `getD 0` of an option mapped by `% 2` is the low bit of the value. -/
theorem option_getD_map_mod2 (o : Option Nat) :
    (o.map (fun v => v % 2)).getD 0 = o.getD 0 % 2 := by cases o <;> rfl

/-- `nbit` at index 0 only reads the low bit. -/
theorem nbit_mod2_zero (x : Nat) :
    Machine.Util.nbit (x % 2) 0 = Machine.Util.nbit x 0 := by
  unfold Machine.Util.nbit
  simp

/-- An option whose values are all `< 2` is unchanged by `% 2`. -/
theorem option_map_mod2_self {o : Option Nat} (h : ∀ v, o = some v → v < 2) :
    o.map (fun v => v % 2) = o := by
  cases o with
  | none => rfl
  | some v => simp [Nat.mod_eq_of_lt (h v rfl)]

/-- The bridge's `Sk.RX` value is a bit. -/
theorem absInOf_rx_lt (k : Fin 2) (st : Stream.State) (i : Stream.Input) :
    ∀ v, (Discharge.absInOf k st i).rx = some v → v < 2 := by
  intro v hv
  cases hrw : i.rxWe with
  | false => simp [Discharge.absInOf, Bridge.StreamB.absIn, Discharge.gatedIn, hrw] at hv
  | true =>
    simp only [Discharge.absInOf, Bridge.StreamB.absIn, Discharge.gatedIn, hrw, if_true,
      Option.some.injEq] at hv
    subst hv
    split <;> decide

/-- `Sk.RX`'s presence and low bit from the projected `% 2` equality. -/
theorem rx_agree_of_mod2 {o1 o2 : Option Nat}
    (h : o1.map (fun v => v % 2) = o2) (h2 : o2.map (fun v => v % 2) = o2) :
    o1.isSome = o2.isSome ∧
      Machine.Util.nbit (o1.getD 0) 0 = Machine.Util.nbit (o2.getD 0) 0 := by
  have hh : o1.map (fun v => v % 2) = o2.map (fun v => v % 2) := h.trans h2.symm
  refine ⟨?_, ?_⟩
  · rw [← option_isSome_map (fun v => v % 2) o1, hh, option_isSome_map]
  · have h3 := congrArg (fun o => Machine.Util.nbit (o.getD 0) 0) hh
    simpa [option_getD_map_mod2, nbit_mod2_zero] using h3

/-- The streams' `LD` registers agree (`AbsRelB`'s `LD` clause). -/
theorem stream_ld_eq {s : State} {m : Machine.State} (hrel : ChipRel s m) (k : Fin 2) :
    (streamAt s k.val).ld = m.streams[k].ld := by
  obtain ⟨-, -, -, -, -, -, hld, -, -, -, -⟩ := hrel.streams k
  exact hld

/-! ## (2) The mode-indexed replay-buffer shape invariant

`Bridge.StreamBuf.ShapeModeOK mode s` is `ShapeOK s` (an empty first slot implies
an empty second) plus "a valid second slot only in a replay cycle".  The
strengthened `stream_mode_quiet` (a stream's mode may only change while it is
completely idle) is exactly what preserves it; `shapeModeOK_step` is B1's
stream-level preservation lemma. -/

open Metronome.ChipCut.Discharge

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
  have hcfgmk : (streamIn s pin k).cfgMode =
      ((Machine.cfgView s.cont.cfg).streams[k]).rx := by
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

/-- A clear `LD` and `NV` give a clear next `NV` (`nvNext`'s only `true` branch
needs `s.ld`). -/
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

/-- The mode/shape invariant is preserved: a mode change only happens with
`LD = RQ = NV = PV = 0` and `PV' = 0` (the relaxed `stream_mode_quiet`, which no
longer needs `WV = 0`), so the stream is idle in the sense B1's
`shapeModeOK_step_nv` needs (`LD = NV = 0`); when the mode does *not* change the
goal's mode is the step's `modeOf` argument. -/
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
    · -- the mode changes: the quietness clears `LD`, `RQ`, `NV` and `PV`
      have hch' : stateMode (step s pin) k ≠ stateMode s k := by
        rw [show step s pin = activeStep s pin from by simp [step, hact]]
        exact hch
      obtain ⟨hld0, -, hnv0, -, -⟩ := hq k hch'
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
        have hs := Bridge.StreamBuf.shapeModeOK_step_nv (streamAt s k.val)
          (streamIn s pin k.val) (stateMode s k) hk (Or.inr ⟨hld0, hnv0⟩)
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

/-- The mode/shape invariant along the cut trace. -/
theorem streamShapeInv_trace (pins : Nat → Machine.PinIn) (cont : Contents)
    (hq : ∀ n, stream_mode_quiet (cutStateAt pins (resetState cont) n) (pins n)) :
    ∀ n, streamShapeInv (cutStateAt pins (resetState cont) n) := by
  intro n
  induction n with
  | zero => exact streamShapeInv_reset cont
  | succ n ih =>
    rw [cutStateAt_succ]
    exact streamShapeInv_step _ _ ih (hq n)

/-! ## (3) The conditional landing relation

`Bridge.StreamBuf.HeldOK` is a **disjunction**: `FRZD = 0` alone discharges it, so
B1's `bufRel_step_unfrozen_guarded` only needs real content on the cycles whose
`FRZD` is set — exactly the first unfrozen cycle after a freeze.  `StreamRelX`
carries that content (the mode-0 `WB` agreement and the mode-3 `HeldLanding`
pair) along the trace, and `ldModeInv` puts every `LD` cycle in the transmit or
replay branch, so the relation supplies `HeldOK` outright
(`streamRelX_hok`).

The two producers of the relation's content are the frozen landings
(`heldLanding_after_frozen_replay`, `wb_after_frozen_tx`), because
`Stream.ldNext` holds `LD` through a freeze. -/

/-- The **landing relation**: while a stream has a read outstanding, either `FRZD`
is clear (so no cut-side landing can diverge), or the transmit `WB` slot agrees,
or the replay landing pair does.  This is `HeldOK`'s three-way shape transposed to
the state pair, which is what the unfrozen bridge consumes directly. -/
def StreamRelX (s : State) (m : Machine.State) : Prop :=
  ∀ k : Fin 2, (streamAt s k.val).ld = true →
    (s.freeze.frzd = false ∨
     (stateMode s k = 0 ∧ (streamAt s k.val).wb = m.streams[k].wb) ∨
     (stateMode s k = 3 ∧ Bridge.StreamBuf.HeldLanding (streamAt s k.val) m.streams[k]))

/-- At reset no stream has a read outstanding, so the relation is vacuous. -/
theorem streamRelX_reset (cont : Contents) (m : Machine.State) :
    StreamRelX (resetState cont) m := by
  intro k h
  rw [show streamAt (resetState cont) k.val = Stream.resetState from by
    rw [streamAt_fin]; simp [resetState]] at h ⊢
  simp [Stream.resetState] at h

/-- `TX` mode is `stateMode = 0`. -/
theorem stateMode_of_txMode (s : State) (pin : Machine.PinIn) (k : Fin 2)
    (h : Stream.txMode (k.val == 0) (streamIn s pin k.val) = true) :
    stateMode s k = 0 := by
  rw [stateMode_branch s pin k]
  have hp := h
  unfold Stream.txMode at hp
  simp_all

/-- `RPL` mode is `stateMode = 3`. -/
theorem stateMode_of_rpl (s : State) (pin : Machine.PinIn) (k : Fin 2)
    (h : Stream.rpl (k.val == 0) (streamIn s pin k.val) = true) :
    stateMode s k = 3 := by
  rw [stateMode_branch s pin k]
  simp [h]

/-- The relation supplies B1's per-cycle `HeldOK` — the `hok` shape
`bufRel_step_unfrozen_guarded` consumes — with no extra invariant. -/
theorem streamRelX_hok (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (h : StreamRelX s m) :
    ∀ k : Fin 2, (streamAt s k.val).ld = true →
      Bridge.StreamBuf.HeldOK (k.val == 0) (streamAt s k.val) (streamIn s pin k.val)
        m.streams[k] := by
  intro k hld
  rcases h k hld with hf | ⟨hm, hwb⟩ | ⟨hm, hl⟩
  · exact Or.inl hf
  · exact Or.inr (Or.inl ⟨stateMode_zero_txMode s pin k hm, hwb⟩)
  · exact Or.inr (Or.inr ⟨stateMode_three_rpl s pin k hm, hl⟩)

/-- A frozen replay landing leaves the cut and machine landing pairs in
`HeldLanding` at the next state (the relation's mode-3 producer). -/
theorem heldLanding_after_frozen_replay (s : State) (m : Machine.State)
    (pin : Machine.PinIn) (hrel : ChipRel s m) (hact : runRst s pin = true)
    (hmode : ∀ k : Fin 2, machMode m k =
      Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hin : ∀ k : Fin 2,
      Discharge.StreamInputAgree m (streamAt s k.val) (streamIn s pin k.val) k)
    (hfrz : s.freeze.frz = true) (k : Fin 2)
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
  have hmach := streamsNext_eq s m pin hrel hact k hcf (hmode k) (hin k)
  have hfzd' : (streamIn s pin k.val).frzd = false := hfzd
  rw [streamAt_activeStep s pin k, hmach, hfrzM]
  exact Bridge.StreamBuf.heldLanding_frozen_landing (k.val == 0) (streamAt s k.val)
    (streamIn s pin k.val) m.streams[k] (Bridge.StreamB.cfgOf (streamIn s pin k.val))
    hact hfrz hrew hldeq hbuf.wv_eq hld hfzd' hrpl

/-- A frozen transmit landing writes the same `WB` in both readings (the
relation's mode-0 producer). -/
theorem wb_after_frozen_tx (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hact : runRst s pin = true)
    (hmode : ∀ k : Fin 2, machMode m k =
      Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hin : ∀ k : Fin 2,
      Discharge.StreamInputAgree m (streamAt s k.val) (streamIn s pin k.val) k)
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
  have hmach := streamsNext_eq s m pin hrel hact k hcf (hmode k) (hin k)
  have hfzd' : (streamIn s pin k.val).frzd = false := hfzd
  rw [streamAt_activeStep s pin k, hmach, hfrzM]
  exact Bridge.StreamBuf.wb_frozen_tx_landing (k.val == 0) (streamAt s k.val)
    (streamIn s pin k.val) m.streams[k] (Bridge.StreamB.cfgOf (streamIn s pin k.val))
    hact hfrz hrew hldeq hbuf.wv_eq htx hld hfzd'

/-- The next cycle's `FRZD` is this cycle's `FRZ`. -/
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

/-- **Preservation of the landing relation on an active cycle.**  An unfrozen
cycle makes the next `FRZD` false; a frozen landing is carried by the two
frozen-landing producers; a frozen non-landing cycle holds every slot; and a
frozen mode change leaves `LD` clear (`stream_mode_quiet`). -/
theorem streamRelX_step_active (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m)
    (hmode : ∀ k : Fin 2, machMode m k =
      Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hin : ∀ k : Fin 2,
      Discharge.StreamInputAgree m (streamAt s k.val) (streamIn s pin k.val) k)
    (h : StreamRelX s m) (hldm : ldModeInv s) (hq : stream_mode_quiet s pin)
    (hac : runRst s pin = true) :
    StreamRelX (activeStep s pin) (Machine.step m pin) := by
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
      rw [streamsNext_eq s m pin hrel hac k hcf (hmode k) (hin k),
        DbgRel.frz_eq hrel.dbg, hfrzt]
    by_cases hsame : stateMode (activeStep s pin) k = stateMode s k
    · by_cases hfzd : s.freeze.frzd = false
      · rcases ldMode_branch s pin k hldm hld with htx | hrpl
        · exact Or.inr (Or.inl ⟨hsame.trans (stateMode_of_txMode s pin k htx),
            wb_after_frozen_tx s m pin hrel hac hmode hin hfrzt k hrew htx hld hfzd⟩)
        · exact Or.inr (Or.inr ⟨hsame.trans (stateMode_of_rpl s pin k hrpl),
            heldLanding_after_frozen_replay s m pin hrel hac hmode hin hfrzt k hrew hrpl hld hfzd⟩)
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
    · -- the mode changes: the strengthened quietness leaves `LD` clear
      have hch : stateMode (step s pin) k ≠ stateMode s k := by rw [hstep]; exact hsame
      rw [(hq k hch).1] at hld
      exact absurd hld (by decide)

/-! ## The assembly -/

/-- (4a) The replay buffer at the next state, **proved** rather than assumed: the
unfrozen cycle is B1's guarded step with `hok` from `StreamRelX`, the frozen cycle
is B1's frozen landing bridge (`LD ∧ !FRZD` included), with `ldModeInv` and
`streamShapeInv` supplying its two side conditions. -/
theorem streamBufrel_of (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hac : runRst s pin = true)
    (hmode : ∀ k : Fin 2, machMode m k =
      Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hin : ∀ k : Fin 2,
      Discharge.StreamInputAgree m (streamAt s k.val) (streamIn s pin k.val) k)
    (hX : StreamRelX s m)
    (hshape : streamShapeInv s) (hldm : ldModeInv s) (k : Fin 2) :
    Bridge.StreamB.BufRel (k.val == 0) (streamAt (activeStep s pin) k.val)
      ((Machine.step m pin).streams[k]) := by
  have hcfg : (Machine.cfgView m.cfg).streams[k] =
      Bridge.StreamB.cfgOf (streamIn s pin k.val) := by
    rw [hrel.cfg]
    exact (cfgOf_streamIn s pin k).symm
  have hnext := streamsNext_eq s m pin hrel hac k hcfg (hmode k) (hin k)
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

/-- The per-cycle `StreamInputAgree` for both streams, from the explicit
premises (W5's `Sk.ADV`/`Sk.RX`/`Sk.CTL` agreements).  Factored out of
`premises_of` so the `CapInv` trace induction consumes the same proof. -/
theorem streamInputAgree_of (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hls : Discharge.LandingStream s)
    (tables : Tables) (hact : runRst s pin = true) :
    ∀ k : Fin 2,
      Discharge.StreamInputAgree m (streamAt s k.val) (streamIn s pin k.val) k := by
  have hgrp := Discharge.PremiseWire.grpPacked_holds s pin
  have hbus : ∀ c : Fin 2, Discharge.CoreInputBus s m pin c (Discharge.sIr s m c) :=
    fun c => Discharge.coreInputBus tables.guardTable tables.srcTable s m pin c hrel hinv hact
  intro k
  obtain ⟨hrxSome, hrxBit⟩ := rx_agree_of_mod2
    (Discharge.StreamMoveWire.streams_rx_low1 s m pin hrel hinv tables.jgTable hbus
      hgrp tables.dstKind tables.dstPayload tables.dstStreamLine k)
    (option_map_mod2_self (absInOf_rx_lt k (streamAt s k.val) (streamIn s pin k.val)))
  have hctl := Discharge.StreamMoveWire.streams_ctl_combined' s m pin hrel hinv tables.jgTable
    hbus hgrp tables.dstKind tables.dstPayload tables.dstStreamLine k
  refine ⟨Discharge.MoveFabricKeyed.streams_adv s m pin hrel hinv tables.jgTable hbus hgrp
    tables.dstKind tables.dstPayload tables.dstStreamLine k, hrxSome, hrxBit, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rewind
    rw [hctl.1]
    simp [Discharge.absInOf, Discharge.gatedIn, Bridge.StreamB.absIn, Bridge.StreamB.nbit_ctl0,
      Bridge.StreamB.nbit_clr0]
  · -- flush (only read unfrozen)
    intro hf
    have hfrz : (streamIn s pin k.val).frz = false := by
      show s.freeze.frz = false
      rw [← Discharge.dbgRel_frz hrel.dbg]
      exact hf
    have hB := hctl.2.1
    rw [hf, hfrz] at hB
    simp only [Bool.not_false, Bool.true_and, Bool.and_true] at hB
    rw [hB]
    simp [Discharge.absInOf, Discharge.gatedIn, Bridge.StreamB.absIn, Bridge.StreamB.nbit_ctl1,
      Bridge.StreamB.nbit_clr1]
  · -- clr
    rw [hctl.2.2]
    simp [Discharge.absInOf, Discharge.gatedIn, Bridge.StreamB.absIn, Bridge.StreamB.nbit_clr7]
  · -- served
    rw [Discharge.stream_served s m pin hrel hinv (fun j => streamWire_mode s m pin hrel j) k]
    rfl
  · -- landNow, guarded by the stream's LD
    intro hld
    have hcut : (streamAt s k.val).ld = true := by
      rw [stream_ld_eq hrel k]; exact hld
    have hln := Discharge.stream_landNow_ld s m pin hrel hls k hcut
    show (m.ramOwner == k.val + 1) = ((streamAt s k.val).ld && !(streamIn s pin k.val).frzd)
    rw [hln, hcut]
    rfl
  · -- ramOut
    show m.ramOut.toNat = (streamIn s pin k.val).rdata.toNat
    rw [hrel.ramOut]
    rfl
  · exact Discharge.stream_cev_eq s m pin hrel k
  · exact Discharge.stream_record_eq s m pin hrel k
  · exact Discharge.stream_apply_eq s m pin hrel k
  · exact Discharge.stream_late_eq s m pin hrel k

/-- Preservation of the landing relation on any product step (reset or active). -/
theorem streamRelX_step (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hls : Discharge.LandingStream s)
    (tables : Tables)
    (h : StreamRelX s m) (hldm : ldModeInv s) (hq : stream_mode_quiet s pin) :
    StreamRelX (step s pin) (Machine.step m pin) := by
  by_cases hac : runRst s pin = true
  · rw [show step s pin = activeStep s pin from by simp [step, hac]]
    exact streamRelX_step_active s m pin hrel
      (fun k => streamWire_mode s m pin hrel k)
      (streamInputAgree_of s m pin hrel hinv hls tables hac) h hldm hq hac
  · rw [show step s pin = resetChip s pin from by simp [step, hac]]
    intro k hk
    have hS : streamAt (resetChip s pin) k.val = Stream.resetState := by
      rw [streamAt_fin]; simp [resetChip, resetState]
    rw [hS] at hk
    simp [Stream.resetState] at hk

/-- **Every discharged premise, plugged in.**  Under the reachable-state
invariants and the host spacing and decode-table premises, one active cycle
satisfies all sixteen `Premises` fields. -/
theorem premises_of (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (habs : Discharge.AbsInv s)
    (hexec : Discharge.ExecInv s) (hpinv : Discharge.HostPinInv s)
    (hldm : Discharge.ldModeInv s) (hlp0 : Discharge.LandingP0 s)
    (hls : Discharge.LandingStream s) (hlane : Discharge.laneInv s)
    (hcap : Discharge.CapInv s m) (hshape : streamShapeInv s)
    (hX : StreamRelX s m)
    (tables : Tables) (hspacing : Discharge.host_sck_spacing s pin)
    (h19 : ¬ (s.arb.heldValid = true ∧ (hostCfgOf s).isSome = true))
    (hwindow : Discharge.WindowWire.WindowQuiet s)
    (hsize : m.cfg.img.size = Machine.Util.cfgSize)
    (hact : runRst s pin = true) :
    Premises s m pin := by
  have hgrp := Discharge.PremiseWire.grpPacked_holds s pin
  have hmode : ∀ k : Fin 2, Discharge.machMode m k =
      Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val) :=
    fun k => streamWire_mode s m pin hrel k
  have hbus : ∀ c : Fin 2, Discharge.CoreInputBus s m pin c (Discharge.sIr s m c) :=
    fun c => Discharge.coreInputBus tables.guardTable tables.srcTable s m pin c hrel hinv hact
  have hwire : Discharge.WireAgree s m pin :=
    { pinAgree := Discharge.wire_pinAgree s m pin hrel hinv hact
      pinLvl := Discharge.wire_pinLvl s m pin hrel hinv hact
      pinPrev := Discharge.wire_pinPrev s m pin hrel hinv hact
      sym := fun l => Discharge.LineMoveWire.wireAgree_sym_low4 s m pin hrel hinv tables.jgTable
        hbus hgrp tables.dstKind tables.dstStreamLine l
      ctl := fun l => Discharge.LineMoveWire.wireAgree_ctl_low3 s m pin hrel hinv tables.jgTable
        hbus hgrp tables.dstKind tables.dstPayload l
      hPhase := Discharge.wire_hPhase s m pin hrel hinv hact
      hCtl := Discharge.wire_hCtl s m pin hrel hinv hact
      hTapmissClr := Discharge.wire_hTapmissClr s m pin hrel hinv hact
      beat := Discharge.wire_beat s m pin hrel hinv hact
      late := fun t => Discharge.MoveFabricKeyed.wireAgree_late s m pin hrel hinv tables.jgTable
        hbus hgrp tables.dstKind t
      stop := fun t => Discharge.MoveFabricKeyed.wireAgree_stop s m pin hrel hinv tables.jgTable
        hbus hgrp tables.dstKind t
      dispatch := fun t => Discharge.ccw_dispatch s m pin hrel hinv hbus tables.jgTable t
      pause := fun t => Discharge.ccw_pause s m pin hrel hinv hbus tables.jgTable t
      hPC := Discharge.wire_hPC s m pin hrel hinv hact
      hStat := Discharge.wire_hStat s m pin hrel hinv hact
      pauseDisp := Discharge.ccw_pauseDisp_cut s pin hexec }
  have hIn : ∀ k : Fin 2,
      Discharge.StreamInputAgree m (streamAt s k.val) (streamIn s pin k.val) k :=
    streamInputAgree_of s m pin hrel hinv hls tables hact
  have happly : (Discharge.machApplyLate m).1 =
      Debug.Ctrl.apply s.dbgCtrl.replay (dbgCtrlIn s pin).frz
        (Debug.bitAt (dbgCtrlIn s pin).replayValid 0) s.dbgCtrl.dc
        (dbgCtrlIn s pin).replayWord := by
    have h := Discharge.stream_apply_eq s m pin hrel 0
    rw [show Debug.bitAt (dbgCtrlIn s pin).replayValid 0 = (streamAt s 0).wv from
      bitAt_replayValid s pin]
    simpa [Discharge.machStreamIn, Discharge.machApplyLate, Discharge.absInOf,
      Discharge.gatedIn, Bridge.StreamB.absIn, streamIn, dbgCtrlIn] using h
  have hcev : (Discharge.machCevRec m).1 =
      Debug.Ctrl.cev s.dbgCtrl.cen s.dbgCtrl.replay (dbgCtrlIn s pin).frz
        (dbgCtrlIn s pin).rise (dbgCtrlIn s pin).fall s.dbgCtrl.emask := by
    have h := Discharge.stream_cev_eq s m pin hrel 0
    simpa [Discharge.machStreamIn, Discharge.machCevRec, Discharge.absInOf,
      Discharge.gatedIn, Bridge.StreamB.absIn, streamIn, dbgCtrlIn] using h
  refine
    { sync := Discharge.premise_sync s m pin hrel hinv hact
      lines := Discharge.premise_lines s m pin hrel hinv hact
        (Discharge.hcfg s m pin hrel hinv hact) hwire
      threads := Discharge.premise_threads s m pin hrel hinv hact hwire
      cores := Discharge.premise_cores_of tables.guardTable tables.srcTable s m pin
        hrel hinv hact tables.jgTable
      units := Discharge.premise_units s m pin hrel hinv hact
        { flag := Discharge.MoveFabric.unitInputs_flag_low4 s m pin hrel hinv tables.jgTable
            hbus hgrp tables.dstKind
            (Discharge.MovePayloadWire.unitFlagPQ tables.dstPayload tables.dstFlagP0Cw)
          acc := Discharge.MoveFabric.unitInputs_acc s m pin hrel hinv tables.jgTable hbus
            hgrp tables.dstKind tables.dstPayload
          reg := Discharge.MoveFabric.unitInputs_reg s m pin hrel hinv tables.jgTable hbus
            hgrp tables.dstKind tables.dstPayload
          sh := Discharge.MoveFabric.unitInputs_sh s m pin hrel hinv tables.jgTable hbus
            hgrp tables.dstKind tables.dstPayload tables.dstPort
          shCfg := Discharge.MoveFabric.unitInputs_shCfg_low5 s m pin hrel hinv tables.jgTable
            hbus hgrp tables.dstKind tables.dstPayload
          cnt := Discharge.MoveFabric.unitInputs_cnt s m pin hrel hinv tables.jgTable hbus
            hgrp tables.dstKind tables.dstPayload tables.dstPort
          lf := Discharge.MoveFabric.unitInputs_lf s m pin hrel hinv tables.jgTable hbus
            hgrp tables.dstKind tables.dstPayload tables.dstPort }
      p0 := Discharge.premise_p0 s m pin hrel hinv hact
        (Discharge.MovePayloadWire.p0Move s m pin hrel hinv tables.jgTable hbus hgrp
          tables.dstKind tables.dstPayload tables.dstFlagP0Cw)
        (Discharge.p0_open_served s m pin hrel hinv hmode)
        (p0_open_land_of_landingP0 s m pin hrel hlp0) hlane
      streams := Discharge.premise_streams s m pin hrel hinv hact
        { mode := hmode
          input := hIn
          bufrel := streamBufrel_of s m pin hrel hact hmode hIn hX hshape hldm }
        (fun k => ldMode_branch s pin k hldm) (fun k => (hshape k).1)
      host := Discharge.premise_host s m pin hrel hinv hact
        (Discharge.host_open_regVal s m pin hrel hinv hact)
        (Discharge.host_open_quiet s m pin hrel hinv hact hpinv hspacing)
      hostReq := Discharge.premise_hostReq s m pin hrel hinv hact
        (Discharge.hostReq_open_served s m pin hrel hinv hmode)
        (Discharge.hostReq_open_strobe s m pin hrel hinv hact hpinv)
      ctrl := Discharge.premise_ctrl s m pin hrel hinv hact
        { hostOut := Discharge.MoveFabric.ctrlMoveFabric_hostOut_of_table s m pin hrel hinv
            tables.jgTable hbus hgrp tables.dstKind tables.dstPayload
          hostInRead := Discharge.MoveFabricKeyed.ctrlMoveFabric_hostInRead s m pin hrel hinv
            tables.jgTable hbus hgrp tables.dstKind tables.srcTable
          conflict := Discharge.MoveFabric.ctrlMoveFabric_conflict_of_chipRel s m pin hrel
            hinv tables.jgTable hbus hgrp tables.dstKind
          memhaz := Discharge.MovePayloadWire.ctrlMemhaz s m pin hrel hinv tables.jgTable hbus
            hgrp tables.dstKind tables.srcTable tables.dstPayload tables.dstFlagP0Cw
            (Discharge.p0_open_served s m pin hrel hinv hmode)
          cwovr := Discharge.MovePayloadWire.ctrlCwovr s m pin hrel hinv tables.jgTable hbus
            hgrp tables.dstKind tables.dstFlagP0Cw }
      dbg := Discharge.premise_dbg s m pin hrel hinv hact
        { hdbg := Discharge.dbgWire_hdbg s m pin hrel hinv hact
          hmctl := Discharge.DbgMapWire.dbgHmctl s m pin hrel hinv hact
          hectl := Discharge.DbgMapWire.dbgHectl s m pin hrel hinv hact
          dbgEmaskValue := Discharge.DbgMapWire.dbgEmaskValue_of s m pin hrel hinv hact
          dbgRlvValue := Discharge.DbgMapWire.dbgRlvValue_of_wv s m pin hrel hinv hact
            (Discharge.DbgMapWire.dbg_wb_of_wv hrel) happly
          hword := dbgWire_hword s pin
          happly := happly
          hcev := hcev }
      cw := Discharge.WindowWire.cw_window_ok s m pin hrel hinv hact
        h19
        (Discharge.MovePayloadWire.cwMove s m pin hrel hinv tables.jgTable hbus hgrp
          tables.dstKind tables.dstFlagP0Cw)
        hwindow
      bank := Discharge.premise_bank s m pin hrel hinv hact
        hsize
      contents := premise_contents_proj s m pin hrel hinv hact
        (fun c => (Discharge.contents_open_proj_abs s m pin hrel hinv hact habs
          tables.guardTable tables.srcTable tables.jgTable c).2.2.2.2)
        (Discharge.contents_open_req_cap s m pin hrel hinv hmode hcap)
        (Discharge.contents_open_served s m pin hrel hinv hmode)
      out := Discharge.premise_out s m pin hrel hinv hact
      oen := Discharge.premise_oen s m pin hrel hinv hact }

/-- **Chip step refinement from the assembled premises.**  One product step
refines one machine step with no remaining `Premises` hypothesis. -/
theorem chip_step_refines' (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (habs : Discharge.AbsInv s)
    (hexec : Discharge.ExecInv s) (hpinv : Discharge.HostPinInv s)
    (hldm : Discharge.ldModeInv s) (hlp0 : Discharge.LandingP0 s)
    (hls : Discharge.LandingStream s) (hlane : Discharge.laneInv s)
    (hcap : Discharge.CapInv s m) (hshape : streamShapeInv s) (hX : StreamRelX s m)
    (tables : Tables) (hspacing : Discharge.host_sck_spacing s pin)
    (h19 : ¬ (s.arb.heldValid = true ∧ (hostCfgOf s).isSome = true))
    (hwindow : Discharge.WindowWire.WindowQuiet s)
    (hsize : m.cfg.img.size = Machine.Util.cfgSize)
    (hrelease : runRst s pin = false → pin.rstn = true →
      Discharge.BankWire.MaskedZero (Machine.cfgNext m.cfg m.cw)) :
    ChipRel (step s pin) (Machine.step m pin) :=
  chip_step_refines s m pin hrel hinv
    (fun hact => premises_of s m pin hrel hinv habs hexec hpinv hldm hlp0 hls hlane
      hcap hshape hX tables hspacing h19 hwindow hsize hact) hrelease

/-- The `CapInv` step of the trace: A2's `CapInv` is preserved on an active cycle
under the per-cycle input agreement and the mode quietness (the reset branch
needs neither). -/
theorem capInv_step_of_premises (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hls : Discharge.LandingStream s)
    (hcap : Discharge.CapInv s m) (tables : Tables)
    (hq : Discharge.stream_mode_quiet s pin) :
    Discharge.CapInv (step s pin) (Machine.step m pin) := by
  by_cases hact : runRst s pin = true
  · exact Discharge.capInv_step_active s m pin hrel hact hcap
      (streamInputAgree_of s m pin hrel hinv hls tables hact) hq
  · exact Discharge.capInv_step_reset s m pin (by simpa using hact) hcap

/-- **Trace corollary from reset**, every invariant from its `_trace` theorem,
carrying `CapInv` and the landing relation `StreamRelX` alongside `ChipRel`. -/
theorem trace_refines'_all (pins : Nat → Machine.PinIn) (cont : Contents)
    (tables : Tables) (initial : InitialConditions cont)
    (env : ∀ n, PinPremises (cutStateAt pins (resetState cont) n) (pins n)) :
    ∀ n, ChipRel (cutStateAt pins (resetState cont) n)
        (machineStateAt pins (absChip (resetState cont)) n) ∧
      Discharge.CapInv (cutStateAt pins (resetState cont) n)
        (machineStateAt pins (absChip (resetState cont)) n) ∧
      StreamRelX (cutStateAt pins (resetState cont) n)
        (machineStateAt pins (absChip (resetState cont)) n) := by
  have hquiet n := (env n).streamModeQuiet
  have hsize : (absChip (resetState cont)).cfg.img.size = Machine.Util.cfgSize :=
    initial.cfgSize
  intro n
  induction n with
  | zero =>
    exact ⟨rel_reset cont initial.maskedZero, Discharge.capInv_reset cont,
      streamRelX_reset cont (absChip (resetState cont))⟩
  | succ n ih =>
    obtain ⟨hrelN, hcapN, hrelXN⟩ := ih
    rw [cutStateAt_succ, machineStateAt_succ]
    refine ⟨chip_step_refines' _ _ _ hrelN
      (inv_trace pins cont n) (Discharge.absInv_trace pins cont n)
      (Discharge.execInv_trace pins cont n) (hostPinInv_trace pins cont n)
      (Discharge.ldModeInv_trace pins cont hquiet n)
      (Discharge.landingP0_trace pins cont initial.ramOwner n)
      (Discharge.landingStream_trace pins cont hquiet n)
      (Discharge.laneInv_trace pins cont initial.ramOwner n)
      hcapN (streamShapeInv_trace pins cont hquiet n) hrelXN tables (env n).hostSckSpacing
      (Discharge.PremiseWire.cwH19_trace pins cont n)
      (Discharge.WindowWire.windowQuiet_trace pins cont n)
      (Discharge.trace_cfg_size pins _ hsize n)
      (maskedZero_release_trace pins cont n _ hrelN), ?_, ?_⟩
    · exact capInv_step_of_premises _ _ _ hrelN (inv_trace pins cont n)
        (Discharge.landingStream_trace pins cont hquiet n) hcapN tables (hquiet n)
    · exact streamRelX_step _ _ _ hrelN (inv_trace pins cont n)
        (Discharge.landingStream_trace pins cont hquiet n) tables
        hrelXN (Discharge.ldModeInv_trace pins cont hquiet n) (hquiet n)

/-- **Trace corollary from reset**, every invariant from its `_trace` theorem. -/
theorem trace_refines' (pins : Nat → Machine.PinIn) (cont : Contents)
    (tables : Tables) (initial : InitialConditions cont)
    (env : ∀ n, PinPremises (cutStateAt pins (resetState cont) n) (pins n)) :
    ∀ n, ChipRel (cutStateAt pins (resetState cont) n)
      (machineStateAt pins (absChip (resetState cont)) n) :=
  fun n => (trace_refines'_all pins cont tables initial env n).1

/-! ## Non-vacuity -/

section

set_option maxRecDepth 8192

open Discharge

private def idlePins (n : Nat) : Machine.PinIn :=
  { ui := 2, uio := 0, rstn := decide (0 < n ∧ n < 4) }

private def idleState (n : Nat) : State :=
  cutStateAt idlePins (resetState Contents.init) n

private theorem idleAfterReset (n : Nat) (hn : 4 ≤ n) :
    step (idleState n) (idlePins n) = resetChip (idleState n) (idlePins n) := by
  have hr : (idlePins n).rstn = false := by
    simp [idlePins, show ¬ n < 4 by omega]
  simp [step, runRst, hr]

private theorem idleSck (n : Nat) : SpiPins.sck (idleState n).sync = false := by
  match n with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | n + 5 =>
    change SpiPins.sck (step (idleState (n + 4)) (idlePins (n + 4))).sync = false
    rw [idleAfterReset (n + 4) (by omega)]
    simp [resetChip, resetState, SpiPins.resetState, SpiPins.sck, SpiPins.bit]

private theorem idleSpacing (n : Nat) : host_sck_spacing (idleState n) (idlePins n) := by
  intro h
  have hc := idleSck n
  simp [HostCmd.completing, HostCmd.sr, HostRead.Input.toHostCmd, hostReadIn, hc] at h

private theorem idleMode (n : Nat) (k : Fin 2) : stateMode (idleState n) k = 0 := by
  have hk : k = 0 ∨ k = 1 := by omega
  match n with
  | 0 | 1 | 2 | 3 | 4 =>
    rcases hk with rfl | rfl <;> rfl
  | n + 5 =>
    change stateMode (step (idleState (n + 4)) (idlePins (n + 4))) k = 0
    rw [idleAfterReset (n + 4) (by omega)]
    have hr : (idlePins (n + 4)).rstn = false := by simp [idlePins]
    have hmode : stateMode (resetChip (idleState (n + 4)) (idlePins (n + 4))) k =
        stateMode (resetState Contents.init) k := by
      simp [stateMode, resetChip, resetState, contentsReset, Machine.resetStep, hr, Contents.init] <;> rfl
    rw [hmode]
    rcases hk with rfl | rfl <;> rfl

private theorem idlePremises (n : Nat) : PinPremises (idleState n) (idlePins n) := by
  refine ⟨idleSpacing n, ?_⟩
  intro k hchange
  exact (hchange ((idleMode (n + 1) k).trans (idleMode n k).symm)).elim

/-- With CS_N high and SCK and MOSI low, release reset for one active cycle
before asserting it again. Stream 0 issues a transmit fetch request. -/
theorem trace_premises_satisfiable_active :
    ∃ (pins : Nat → Machine.PinIn) (cont : Contents),
      InitialConditions cont ∧
        (∀ n, PinPremises (cutStateAt pins (resetState cont) n) (pins n)) ∧
        ∃ n, runRst (cutStateAt pins (resetState cont) n) (pins n) = true ∧
          (streamAt (cutStateAt pins (resetState cont) (n + 1)) 0).rq = true :=
  ⟨idlePins, Contents.init, ⟨rfl, Discharge.BankWire.maskedZero_zero, rfl⟩,
    idlePremises, 3, rfl, rfl⟩

/-- The initial conditions and pin contracts have a common witness. -/
theorem trace_premises_satisfiable (_tables : Tables) :
    ∃ (pins : Nat → Machine.PinIn) (cont : Contents),
      InitialConditions cont ∧
        ∀ n, PinPremises (cutStateAt pins (resetState cont) n) (pins n) := by
  obtain ⟨pins, cont, initial, env, _⟩ := trace_premises_satisfiable_active
  exact ⟨pins, cont, initial, env⟩

end

end Metronome.ChipCut
