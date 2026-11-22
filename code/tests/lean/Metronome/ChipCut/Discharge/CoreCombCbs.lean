/-
# Closing `contents_open_cbs` and the stream debug sub-fields (`record`/`apply`/`late`)

Two wiring hypotheses were left in `WIRE_CORECOMB_NOTES.md` (§6, §7):

* `MemHostCfg.contents_open_cbs` — the *whole* per-core combinational bundle at `m`
  equals the one at `absChip s`;
* `StreamDbg.StreamWire`'s capture/replay sub-fields — the machine's `record`,
  `apply` and `late` entries of the per-stream input are the cut's.

This file reports, for each, either a theorem or a proved counterexample.

## 1. `contents_open_cbs`: the field is **false** as stated

`Machine.CoreComb` carries eleven fields, and three of them (`taken`, `npc`) are
decoded from `IR` *unconditionally*, while `ChipRel.CoreRegsRel` pins `IR` only
while `XV` is set.  The cut captures the program-memory output on every unfrozen
cycle and the machine only on `load`, so in an `XV = 0` cycle the two `IR`
registers genuinely differ.  `contents_open_cbs_counterexample` gives a
`ChipRel`/`Inv` state pair (the cut's power-on contents with the reset flop set,
against the canonical abstraction with one core's `IR` changed) whose `taken`
bits are `1` and `0`.

The fields `coreNext` actually reads (`load`, `jmp`, `disp`, `dispThread`,
`fetch`) are IR-free at `XV = 0`; `contents_open_proj` proves those congruent
(under the canonical-abstraction relation, §3 of the notes) and
`contents_mout_of_fetch` shows that only `fetch` enters `premise_contents`'
`mout` goal (`coreNext`'s `mout` is `cs.mout`/`word`, and `word` is a function
of `cb.fetch`).

## 2. The stream `record`/`apply`/`late` inputs

They reduce to `Bridge.Debug.cev_bridge` / `apply_bridge` / `late_bridge` with
real (unfrozen) inputs, `DbgRel`'s `DC`, the first replay slot (read only under
`BufRel`'s `WV` guard) and the pin level (`Bridge.Debug.level_toNat` and the
previous-level analogue proved here).  The `record` field needs no unfrozen
hypothesis; `apply`/`late` do.

No `sorry`, no `native_decide`.
-/

import Metronome.ChipCut.Discharge.CoreCombWire
import Metronome.ChipCut.Discharge.GuardSrc

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Metronome.ChipCut.Discharge

open Metronome

/-! ## 1. Bit plumbing for the capture record -/

/-- A 19-bit `DC` and a 13-bit level concatenate to `dc * 2^13 + level`. -/
theorem cat_dc_lvl (dc : BitVec 19) (l : BitVec 13) :
    (dc ++ l).toNat = dc.toNat * 2 ^ 13 + l.toNat := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq, Nat.or_comm,
    Bridge.Glue.or_shift l.toNat dc.toNat 13 l.isLt]

/-- The cut's previous-level vector is the machine's `pinView` previous level. -/
theorem pinPrev_toNat (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    (pinPrev s).toNat = (Machine.pinView m.sync m.dbg).prev := by
  obtain ⟨-, -, hsp⟩ := hrel.sync
  have hrpl : s.dbgCtrl.replay = m.dbg.rpl := (DbgRel.rpl_eq hrel.dbg).symm
  have hemask : s.dbgCtrl.emask = m.dbg.emask := (DbgRel.emask_eq hrel.dbg).symm
  have hrlvp : s.dbgCtrl.rlvPrev = m.dbg.rlvp := (DbgRel.rlvp_eq hrel.dbg).symm
  unfold pinPrev
  rw [Bridge.Debug.previous_toNat, hsp, hrpl, hemask, hrlvp, pinVec_toNat]
  rfl

/-! ## 2. The capture event: `cev` and its record -/

/-- **The machine's capture record of the cycle** is the cut's
`captureRecord = {DC, PIN}`.  No freeze hypothesis: the record is not gated. -/
theorem captureRecord_bridge (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    (machCevRec m).2 = (captureRecord s).toNat := by
  have hdc : m.dbg.dc = s.dbgCtrl.dc := DbgRel.dc_eq hrel.dbg
  have hN : Machine.Tables.N_IN_PINS = 13 := rfl
  have hcat : (captureRecord s).toNat = s.dbgCtrl.dc.toNat * 2 ^ 13 + (pinLvl s).toNat := by
    unfold captureRecord
    exact cat_dc_lvl s.dbgCtrl.dc (pinLvl s)
  unfold machCevRec Machine.captureEvent
  rw [hcat, hdc, pinLvl_toNat s m hrel, hN]

/-- **The machine's `cev` of the cycle** is the cut's `Debug.Ctrl.cev` at the cut's
debug control block and pin vectors (`Bridge.Debug.cev_bridge`). -/
theorem machCev_bridge (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    (machCevRec m).1 =
      Debug.Ctrl.cev s.dbgCtrl.cen s.dbgCtrl.replay s.freeze.frz (riseVec s) (fallVec s)
        s.dbgCtrl.emask := by
  have hcen : m.dbg.cen = s.dbgCtrl.cen := DbgRel.cen_eq hrel.dbg
  have hrpl : m.dbg.rpl = s.dbgCtrl.replay := DbgRel.rpl_eq hrel.dbg
  have hfrz : m.dbg.frz = s.freeze.frz := DbgRel.frz_eq hrel.dbg
  have hem : m.dbg.emask = s.dbgCtrl.emask := DbgRel.emask_eq hrel.dbg
  have hcev := Bridge.Debug.cev_bridge m.dbg (Machine.pinView m.sync m.dbg) m.dbg.frz
    (pinLvl s) (pinPrev s) (riseVec s) (fallVec s)
    (pinLvl_toNat s m hrel).symm (pinPrev_toNat s m hrel).symm rfl rfl
  unfold machCevRec
  rw [hcev, hcen, hrpl, hfrz, hem]

/-! ## 3. The replay `apply`/`late` pair

`Machine.replayApply` reads the first replay slot's `WV`/`WB`; `WV` is pinned by
`AbsRelB`, and `WB` by `BufRel` **only while `WV`** (`BufRel.wb_of_wv`).  When
`WV` is clear both `apply` and `late` are false on both sides, so the guarded
`WB` equality is enough. -/

/-- With `WV` clear the machine's replay `apply` is false. -/
theorem replayApply_fst_wv_false (d : Machine.DbgSt) (st : Machine.StreamSt) (frz : Bool)
    (h : st.wv = false) : (Machine.replayApply d st frz).1 = false := by
  unfold Machine.replayApply
  rw [h]
  simp

/-- With `WV` clear the machine's replay `late` is false. -/
theorem replayApply_snd_wv_false (d : Machine.DbgSt) (st : Machine.StreamSt) (frz : Bool)
    (h : st.wv = false) : (Machine.replayApply d st frz).2 = false := by
  unfold Machine.replayApply
  rw [h]
  simp

/-- The cut's replay `apply` with an invalid slot is false. -/
theorem ctrlApply_valid_false (replay frz : Bool) (dc : BitVec 19) (w : BitVec 32) :
    Debug.Ctrl.apply replay frz false dc w = false := by
  simp [Debug.Ctrl.apply]

/-- The cut's replay `late` with an invalid slot is false. -/
theorem ctrlLate_valid_false (replay frz : Bool) (dc : BitVec 19) (w : BitVec 32) :
    Debug.Ctrl.late replay frz false dc w = false := by
  simp [Debug.Ctrl.late]

/-- **The machine's replay `apply`/`late` pair** is the cut's `Debug.Ctrl.apply`/
`late` at the cut's replay registers and first slot. -/
theorem machApplyLate_bridge (s : State) (m : Machine.State) (hrel : ChipRel s m) :
    (machApplyLate m).1 =
      Debug.Ctrl.apply s.dbgCtrl.replay s.freeze.frz (streamAt s 0).wv s.dbgCtrl.dc
        (streamAt s 0).wb ∧
    (machApplyLate m).2 =
      Debug.Ctrl.late s.dbgCtrl.replay s.freeze.frz (streamAt s 0).wv s.dbgCtrl.dc
        (streamAt s 0).wb := by
  have hrpl : m.dbg.rpl = s.dbgCtrl.replay := DbgRel.rpl_eq hrel.dbg
  have hdc : m.dbg.dc = s.dbgCtrl.dc := DbgRel.dc_eq hrel.dbg
  have hfrz : m.dbg.frz = s.freeze.frz := DbgRel.frz_eq hrel.dbg
  have hbuf : Bridge.StreamB.BufRel ((0 : Fin 2).val == 0) (streamAt s (0 : Fin 2).val)
      m.streams[(0 : Fin 2)] :=
    AbsRelB.bufRel (hrel.streams (0 : Fin 2))
  have hwv : (streamAt s (0 : Fin 2).val).wv = m.streams[(0 : Fin 2)].wv := hbuf.wv_eq
  unfold machApplyLate
  by_cases h : (streamAt s (0 : Fin 2).val).wv = true
  · have hwb : (streamAt s (0 : Fin 2).val).wb = m.streams[(0 : Fin 2)].wb :=
      hbuf.wb_of_wv h
    have hb := Bridge.Debug.apply_bridge s.dbgCtrl.replay m.dbg.frz true s.dbgCtrl.dc
      (streamAt s (0 : Fin 2).val).wb m.dbg m.streams[(0 : Fin 2)] hrpl hdc
      (by rw [← hwv]; exact h) hwb.symm
    rw [← h] at hb
    rw [hfrz] at hb ⊢
    exact hb
  · have hf : (streamAt s (0 : Fin 2).val).wv = false := by simpa using h
    have hmv : m.streams[(0 : Fin 2)].wv = false := by rw [← hwv, hf]
    have hwv0 : m.streams[0].wv = false := hmv
    have hf0 : (streamAt s 0).wv = false := hf
    constructor
    · rw [replayApply_fst_wv_false m.dbg m.streams[0] m.dbg.frz hwv0,
        show (streamAt s 0).wv = false from hf0, ctrlApply_valid_false]
    · rw [replayApply_snd_wv_false m.dbg m.streams[0] m.dbg.frz hwv0,
        show (streamAt s 0).wv = false from hf0, ctrlLate_valid_false]

/-! ## 4. The per-stream input's `record`, `apply` and `late`

`Machine.runStep` fills `record`/`apply`/`late` of stream `k` from the cycle's
capture event and replay pair, gating `apply`/`late` on `k == 0`; the bridge's
`absIn` takes `capRec`, and `gatedIn` applies the same gate. -/

/-- The cut's capture push strobe. -/
theorem streamIn_capPush (s : State) (pin : Machine.PinIn) (k : Nat) :
    (streamIn s pin k).capPush =
      Debug.Ctrl.cev s.dbgCtrl.cen s.dbgCtrl.replay s.freeze.frz (riseVec s) (fallVec s)
        s.dbgCtrl.emask := rfl

/-- The cut's capture record. -/
theorem streamIn_capRec (s : State) (pin : Machine.PinIn) (k : Nat) :
    (streamIn s pin k).capRec = captureRecord s := rfl

/-- The cut's replay `apply`. -/
theorem streamIn_replayApply (s : State) (pin : Machine.PinIn) (k : Nat) :
    (streamIn s pin k).replayApply =
      Debug.Ctrl.apply s.dbgCtrl.replay s.freeze.frz (streamAt s 0).wv s.dbgCtrl.dc
        (streamAt s 0).wb := rfl

/-- The cut's replay `late`. -/
theorem streamIn_replayLate (s : State) (pin : Machine.PinIn) (k : Nat) :
    (streamIn s pin k).replayLate =
      Debug.Ctrl.late s.dbgCtrl.replay s.freeze.frz (streamAt s 0).wv s.dbgCtrl.dc
        (streamAt s 0).wb := rfl

/-- The stream input's `cev` field (`k == 0` gated capture edge). -/
theorem stream_cev_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (k : Fin 2) :
    (machStreamIn m k).cev = (absInOf k (streamAt s k.val) (streamIn s pin k.val)).cev := by
  simp only [machStreamIn, absInOf, Bridge.StreamB.absIn, gatedIn, machCev_bridge s m hrel,
    streamIn_capPush]

/-- **`StreamWire.record`** (both streams): the machine's capture record is the
cut's `{DC, PIN}`. -/
theorem stream_record_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (k : Fin 2) :
    (machStreamIn m k).record = (absInOf k (streamAt s k.val) (streamIn s pin k.val)).record := by
  simp only [machStreamIn, absInOf, Bridge.StreamB.absIn, gatedIn, captureRecord_bridge s m hrel,
    streamIn_capRec]

/-- **`StreamWire.apply`** (both streams). -/
theorem stream_apply_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (k : Fin 2) :
    (machStreamIn m k).apply = (absInOf k (streamAt s k.val) (streamIn s pin k.val)).apply := by
  simp only [machStreamIn, absInOf, Bridge.StreamB.absIn, gatedIn,
    (machApplyLate_bridge s m hrel).1, streamIn_replayApply]

/-- **`StreamWire.late`** (both streams). -/
theorem stream_late_eq (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (k : Fin 2) :
    (machStreamIn m k).late = (absInOf k (streamAt s k.val) (streamIn s pin k.val)).late := by
  simp only [machStreamIn, absInOf, Bridge.StreamB.absIn, gatedIn,
    (machApplyLate_bridge s m hrel).2, streamIn_replayLate]

/-- The three sub-fields in the shape `StreamWire` states them. -/
theorem streamWire_record_apply_late (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) :
    (∀ k : Fin 2, (machStreamIn m k).record =
        (absInOf k (streamAt s k.val) (streamIn s pin k.val)).record) ∧
      (∀ k : Fin 2, (machStreamIn m k).apply =
        (absInOf k (streamAt s k.val) (streamIn s pin k.val)).apply) ∧
      (∀ k : Fin 2, (machStreamIn m k).late =
        (absInOf k (streamAt s k.val) (streamIn s pin k.val)).late) :=
  ⟨fun k => stream_record_eq s m pin hrel k, fun k => stream_apply_eq s m pin hrel k,
    fun k => stream_late_eq s m pin hrel k⟩

/-! ## 5. `contents_open_cbs`: the whole bundle is **false**

`Machine.CoreComb.taken`/`npc` decode `IR` unconditionally, while
`ChipRel.CoreRegsRel` pins `IR` only while `XV`; the cut captures the program
memory output in every unfrozen cycle and the machine only on `load`.  So in an
`XV = 0` cycle the two `IR` registers are free to differ, and with a `JMODE`
field of `1` on one side and `0` on the other the `taken` bits are `true` and
`false`.  The witness below uses the power-on contents with the reset flop pair
set (so `runRst` is high) and the canonical abstraction with core 0's `IR`
replaced by `0xA`. -/

/-- The machine's `IR` register of core `0` replaced (free while `XV = 0`). -/
def irBroken (s : State) (w : BitVec 64) : Machine.State :=
  { absChip s with
    cores := Vector.ofFn fun c =>
      if c.val = 0 then { (absChip s).cores[c] with ir := w } else (absChip s).cores[c] }

/-- The power-on cut state with the reset flop pair set (`runRst` is high). -/
def cbsWitnessState (cont : Contents) : State :=
  { resetState cont with rst := ({ rstM := true, rstQ := true } : Debug.Reset.State) }

/-- The witness pin sample (`rst_n` high). -/
def cbsWitnessPin : Machine.PinIn := { ui := 0, uio := 0, rstn := true }

/-- `ChipRel` at the power-on state with an arbitrary reset flop pair: the
relation reads only `rstM`/`rstQ` of the reset cut (and, of the machine state,
`host` through `linkRelR_host_congr`). -/
theorem chipRel_abs_rst (cont : Contents) (r1 rq : Bool) (hzero : BankWire.MaskedZero cont.cfg) :
    ChipRel { resetState cont with rst := { rstM := r1, rstQ := rq } }
      { absChip (resetState cont) with r1 := r1, rq := rq } := by
  have h := rel_reset cont hzero
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25⟩ := h
  refine ⟨rfl, rfl, rfl, h4, h5, h6, h7, h8, h9, h10, h11, ?_, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25⟩
  exact linkRelR_host_congr (m := { absChip (resetState cont) with r1 := r1, rq := rq })
    (m' := (absChip (resetState cont))) rfl h12

/-- `ChipRel` is preserved by replacing one machine core's `IR` while every cut
core has `XV = 0` (the relation's `IR` clause is then vacuous). -/
theorem chipRel_ir_broken (s : State) (m : Machine.State) (h : ChipRel s m)
    (hxv : ∀ c : Fin 2, (s.cores[c.val]).xv = false) (w : BitVec 64) :
    ChipRel s { m with cores := Vector.ofFn fun c =>
      if c.val = 0 then { m.cores[c] with ir := w } else m.cores[c] } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_, h9, h10, h11, ?_, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25⟩
  · intro c
    simp only [vecGet_ofFn]
    by_cases hc : c.val = 0
    · rw [if_pos hc]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h7 c
      refine ⟨a1, ?_, a3, a4, a5, a6, a7⟩
      intro hx
      rw [hxv c] at hx
      exact Bool.noConfusion hx
    · rw [if_neg hc]
      exact h7 c
  · intro c
    simp only [vecGet_ofFn]
    by_cases hc : c.val = 0
    · rw [if_pos hc]
      exact h8 c
    · rw [if_neg hc]
      exact h8 c
  · exact linkRelR_host_congr (m := { m with cores := Vector.ofFn fun c =>
      if c.val = 0 then { m.cores[c] with ir := w } else m.cores[c] }) (m' := m) rfl h12

/-- The witness cut state relates to the broken canonical abstraction. -/
theorem chipRel_cbsWitness (cont : Contents) (w : BitVec 64) (hzero : BankWire.MaskedZero cont.cfg) :
    ChipRel (cbsWitnessState cont) (irBroken (cbsWitnessState cont) w) := by
  have h : ChipRel (cbsWitnessState cont) (absChip (cbsWitnessState cont)) :=
    chipRel_abs_rst cont true true hzero
  exact chipRel_ir_broken (cbsWitnessState cont) (absChip (cbsWitnessState cont)) h
    (fun c => by simp [cbsWitnessState, resetState]) w

/-- The witness cut state satisfies `Inv`. -/
theorem inv_cbsWitness (cont : Contents) : Inv (cbsWitnessState cont) := by
  obtain ⟨a1, a2, a3, a4⟩ := inv_reset cont
  exact ⟨a1, a2, a3, a4⟩

/-- The witness cut state is in an active cycle at `cbsWitnessPin`. -/
theorem runRst_cbsWitness (cont : Contents) :
    runRst (cbsWitnessState cont) cbsWitnessPin = true := by
  simp [runRst, cbsWitnessState, cbsWitnessPin]

/-- The bundle at the broken abstraction has `taken = true` (`JMODE = 1`). -/
theorem taken_irBroken :
    (mhcCbs (irBroken (cbsWitnessState Contents.init) 0xA) cbsWitnessPin)[0].taken = true := by
  decide

/-- The bundle at the canonical abstraction has `taken = false` (`JMODE = 0`). -/
theorem taken_absChip :
    (mhcCbs (absChip (cbsWitnessState Contents.init)) cbsWitnessPin)[0].taken = false := by
  decide

/-- **`contents_open_cbs` is false**: the whole-bundle equality fails on a
`ChipRel`/`Inv`/`runRst` state triple, at the `taken` field. -/
theorem contents_open_cbs_counterexample :
    ∃ (s : State) (m : Machine.State) (pin : Machine.PinIn),
      ChipRel s m ∧ Inv s ∧ runRst s pin = true ∧
        (mhcCbs m pin)[0] ≠ (mhcCbs (absChip s) pin)[0] := by
  refine ⟨cbsWitnessState Contents.init, irBroken (cbsWitnessState Contents.init) 0xA,
    cbsWitnessPin, chipRel_cbsWitness Contents.init 0xA BankWire.maskedZero_zero, inv_cbsWitness Contents.init,
    runRst_cbsWitness Contents.init, ?_⟩
  intro h
  have ht : (mhcCbs (irBroken (cbsWitnessState Contents.init) 0xA) cbsWitnessPin)[0].taken =
      (mhcCbs (absChip (cbsWitnessState Contents.init)) cbsWitnessPin)[0].taken := by rw [h]
  rw [taken_irBroken, taken_absChip] at ht
  exact Bool.noConfusion ht

/-! ## 6. The projection congruence: the fields `coreNext` reads

The whole-bundle equality is false (§5), but `coreNext`'s program-memory output
reads only `cb.fetch` (and `cs.mout`), and the state transition reads `load`,
`jmp`, `disp`, `dispThread` and `fetch`.  Those five fields *are* congruent, by
routing both machine states through the cut core (`Bridge.Core.out_bridge` at
`sIr s m c` and at `sIr s (absChip s) c = s.cores[c]`): the only difference
between the two `sIr` states is `IR`, which is unobservable at `XV = 0`.

The canonical-abstraction relation `ChipRel s (absChip s)` is the one named
hypothesis: it is *not* a consequence of `ChipRel s m` + `Inv s` as the relation
stands, because its `host` clause pins the cut host-link phase shape and its
`streams` clause carries `BufRel`'s `¬(RQ ∧ LD)`.  Given it, the global tables and
`Inv`/`runRst`, everything else is discharged. -/

/-- `mhcCbs` is `ltCbs` (identical definitions). -/
theorem mhcCbs_eq_ltCbs (m : Machine.State) (pin : Machine.PinIn) :
    mhcCbs m pin = ltCbs m := rfl

/-- At the canonical abstraction the `sIr` core state is the cut's own. -/
theorem sIr_absChip (s : State) (c : Fin 2) : sIr s (absChip s) c = s.cores[c.val] := by
  have hc : (absChip s).cores[c] = Bridge.Core.absCore (s.cont.mout[c.val]) (s.cores[c.val]) := by
    simp [absChip, vecGet_ofFn]
  have h : (absChip s).cores[c].ir = (s.cores[c.val]).ir := by rw [hc]; rfl
  rw [sIr, h]

/-- With `XV = 0` the core's `IR` is unobservable in `jmp`, `load` and `disp`. -/
theorem core_ir_irrel (cb : Bool) (x : Core.State) (i : Core.Input) (w : BitVec 64)
    (hx : x.xv = false) :
    Core.jmp { x with ir := w } i = Core.jmp x i ∧
      Core.load { x with ir := w } i = Core.load x i ∧
      Core.disp cb { x with ir := w } i = Core.disp cb x i := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Core.jmp, Core.load, Core.ra, Core.pse, Core.xa, Core.disp, Core.free, Core.cand, hx]

/-- The cut core's `jmp` is unchanged by the `sIr` substitution. -/
theorem core_jmp_sIr (s : State) (m : Machine.State) (pin : Machine.PinIn) (hrel : ChipRel s m)
    (c : Fin 2) :
    Core.jmp (sIr s m c) (coreIn s pin c.val) = Core.jmp (s.cores[c.val]) (coreIn s pin c.val) := by
  have hm : sIr s m c = { s.cores[c.val] with ir := m.cores[c].ir } := rfl
  rw [hm]
  by_cases hx : (s.cores[c.val]).xv = true
  · have hir : m.cores[c].ir = (s.cores[c.val]).ir := (hrel.cores c).2.1 hx
    rw [hir]
  · exact (core_ir_irrel false _ _ _ (by simpa using hx)).1

/-- The cut core's `load` is unchanged by the `sIr` substitution. -/
theorem core_load_sIr (s : State) (m : Machine.State) (pin : Machine.PinIn) (hrel : ChipRel s m)
    (c : Fin 2) :
    Core.load (sIr s m c) (coreIn s pin c.val) = Core.load (s.cores[c.val]) (coreIn s pin c.val) := by
  have hm : sIr s m c = { s.cores[c.val] with ir := m.cores[c].ir } := rfl
  rw [hm]
  by_cases hx : (s.cores[c.val]).xv = true
  · have hir : m.cores[c].ir = (s.cores[c.val]).ir := (hrel.cores c).2.1 hx
    rw [hir]
  · exact (core_ir_irrel false _ _ _ (by simpa using hx)).2.1

/-- The cut core's `disp` is unchanged by the `sIr` substitution. -/
theorem core_disp_sIr (s : State) (m : Machine.State) (pin : Machine.PinIn) (hrel : ChipRel s m)
    (c : Fin 2) :
    Core.disp (c.val == 1) (sIr s m c) (coreIn s pin c.val) =
      Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) := by
  have hm : sIr s m c = { s.cores[c.val] with ir := m.cores[c].ir } := rfl
  rw [hm]
  by_cases hx : (s.cores[c.val]).xv = true
  · have hir : m.cores[c].ir = (s.cores[c.val]).ir := (hrel.cores c).2.1 hx
    rw [hir]
  · exact (core_ir_irrel (c.val == 1) _ _ _ (by simpa using hx)).2.2

/-- The cut core's `fetchEn` is unchanged by the `sIr` substitution. -/
theorem core_fetchEn_sIr (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (c : Fin 2) :
    Core.fetchEn (c.val == 1) (sIr s m c) (coreIn s pin c.val) =
      Core.fetchEn (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) :=
  fetchEn_sIr hrel (c.val == 1) (coreIn s pin c.val)

/-- The cut core's `fetchAddr` is unchanged by the `sIr` substitution. -/
theorem core_fetchAddr_sIr (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (c : Fin 2) :
    Core.fetchAddr (c.val == 1) (sIr s m c) (coreIn s pin c.val) =
      Core.fetchAddr (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) :=
  fetchAddr_sIr hrel (c.val == 1) (coreIn s pin c.val)

/-- The cut core's `fetch` bucket at a cut core state. -/
def fetchCut (s : State) (pin : Machine.PinIn) (c : Fin 2) : Option Nat :=
  if Core.fetchEn (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) = true then
    some (Core.fetchAddr (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).toNat
  else none

/-- **The machine bundle's `fetch` at a related state is the cut's.** -/
theorem coreFetch_cut (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
        Core.JG_TABLE.getD n 62)
    (c : Fin 2) :
    (ltCbs m)[c].fetch = fetchCut s pin c := by
  have h := Bridge.Core.fetch_bridge (rel_of_bus s m pin c hrel hinv (hbus c)) hJGTab
  rw [ltCbs_eq_mCoreComb, mCoreComb_cut s m pin hrel c, h, core_fetchEn_sIr s m pin hrel c,
    core_fetchAddr_sIr s m pin hrel c]
  rfl

/-- **The machine bundle's `jmp` at a related state is the cut's.** -/
theorem coreJmp_cut (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
        Core.JG_TABLE.getD n 62)
    (c : Fin 2) :
    (ltCbs m)[c].jmp = Core.jmp (s.cores[c.val]) (coreIn s pin c.val) := by
  have h := Bridge.Core.jmp_bridge (rel_of_bus s m pin c hrel hinv (hbus c)) hJGTab
  rw [ltCbs_eq_mCoreComb, mCoreComb_cut s m pin hrel c, ← h, core_jmp_sIr s m pin hrel c]

/-- **The machine bundle's `load` at a related state is the cut's.** -/
theorem coreLoad_cut (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
        Core.JG_TABLE.getD n 62)
    (c : Fin 2) :
    (ltCbs m)[c].load = Core.load (s.cores[c.val]) (coreIn s pin c.val) := by
  have h := Bridge.Core.load_bridge (rel_of_bus s m pin c hrel hinv (hbus c)) hJGTab
  rw [ltCbs_eq_mCoreComb, mCoreComb_cut s m pin hrel c, ← h, core_load_sIr s m pin hrel c]

/-- **The machine bundle's `disp` at a related state is the cut's.** -/
theorem coreDisp_cut (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c)) (c : Fin 2) :
    (ltCbs m)[c].disp = Core.disp (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val) := by
  have h := Bridge.Core.disp_bridge (rel_of_bus s m pin c hrel hinv (hbus c))
  rw [ltCbs_eq_mCoreComb, mCoreComb_cut s m pin hrel c, ← h, core_disp_sIr s m pin hrel c]

/-- **The projection congruence** (`load`, `jmp`, `disp`, `dispThread` under
`disp`, and `fetch`). -/
theorem contents_open_proj (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hrelA : ChipRel s (absChip s))
    (hG : Bridge.Glue.GuardTable) (hS : Bridge.Glue.SrcTable)
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
        Core.JG_TABLE.getD n 62)
    (c : Fin 2) :
    (mhcCbs m pin)[c].load = (mhcCbs (absChip s) pin)[c].load ∧
      (mhcCbs m pin)[c].jmp = (mhcCbs (absChip s) pin)[c].jmp ∧
      (mhcCbs m pin)[c].disp = (mhcCbs (absChip s) pin)[c].disp ∧
      ((mhcCbs m pin)[c].disp = true →
        (mhcCbs m pin)[c].dispThread = (mhcCbs (absChip s) pin)[c].dispThread) ∧
      (mhcCbs m pin)[c].fetch = (mhcCbs (absChip s) pin)[c].fetch := by
  have hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c) :=
    fun c => coreInputBus hG hS s m pin c hrel hinv hact
  have hbusA : ∀ c : Fin 2, CoreInputBus s (absChip s) pin c (sIr s (absChip s) c) :=
    fun c => coreInputBus hG hS s (absChip s) pin c hrelA hinv hact
  have hload : (mhcCbs m pin)[c].load = (mhcCbs (absChip s) pin)[c].load := by
    rw [mhcCbs_eq_ltCbs, mhcCbs_eq_ltCbs]
    rw [coreLoad_cut s m pin hrel hinv hbus hJGTab c,
      coreLoad_cut s (absChip s) pin hrelA hinv hbusA hJGTab c]
  have hjmp : (mhcCbs m pin)[c].jmp = (mhcCbs (absChip s) pin)[c].jmp := by
    rw [mhcCbs_eq_ltCbs, mhcCbs_eq_ltCbs]
    rw [coreJmp_cut s m pin hrel hinv hbus hJGTab c,
      coreJmp_cut s (absChip s) pin hrelA hinv hbusA hJGTab c]
  have hdisp : (mhcCbs m pin)[c].disp = (mhcCbs (absChip s) pin)[c].disp := by
    rw [mhcCbs_eq_ltCbs, mhcCbs_eq_ltCbs]
    rw [coreDisp_cut s m pin hrel hinv hbus c,
      coreDisp_cut s (absChip s) pin hrelA hinv hbusA c]
  have hfetch : (mhcCbs m pin)[c].fetch = (mhcCbs (absChip s) pin)[c].fetch := by
    rw [mhcCbs_eq_ltCbs, mhcCbs_eq_ltCbs]
    rw [coreFetch_cut s m pin hrel hinv hbus hJGTab c,
      coreFetch_cut s (absChip s) pin hrelA hinv hbusA hJGTab c]
  refine ⟨hload, hjmp, hdisp, ?_, hfetch⟩
  intro hd
  have hdA : (mhcCbs (absChip s) pin)[c].disp = true := by rw [← hdisp]; exact hd
  have hdL : (ltCbs m)[c].disp = true := by rw [← mhcCbs_eq_ltCbs]; exact hd
  have hdLA : (ltCbs (absChip s))[c].disp = true := by rw [← mhcCbs_eq_ltCbs]; exact hdA
  have h1 := coreDispThread_eq s m pin hrel hinv hbus hJGTab c hdL
  have h2 := coreDispThread_eq s (absChip s) pin hrelA hinv hbusA hJGTab c hdLA
  rw [mhcCbs_eq_ltCbs, mhcCbs_eq_ltCbs, h1, h2]

/-- `coreNext`'s memory output reads only the program word and the core's own
`mout`, not the bundle (`cb` is unused in the `mout` equation). -/
theorem coreNext_mout_congr' (a b : Machine.CoreSt) (cv : Machine.CfgView)
    (cb cb' : Machine.CoreComb) (word : Option Nat) (frozen : Bool)
    (hmout : a.mout = b.mout) :
    (Machine.coreNext a cv cb word frozen).mout = (Machine.coreNext b cv cb' word frozen).mout := by
  by_cases hf : frozen = true
  · simp [Machine.coreNext, hf, hmout]
  · have hf' : frozen = false := by cases frozen <;> simp_all
    cases word with
    | none => simp [Machine.coreNext, hf', hmout]
    | some w => simp [Machine.coreNext, hf']

/-- **`ContentsEq.mout` from the `fetch` congruence alone.**  This is the first
field of `MemHostCfg.premise_contents` with `contents_open_cbs` replaced by its
`fetch` projection. -/
theorem contents_mout_of_fetch (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hact : runRst s pin = true)
    (hfetch : ∀ c : Fin 2, (mhcCbs m pin)[c].fetch = (mhcCbs (absChip s) pin)[c].fetch)
    (c : Fin 2) :
    (Machine.step m pin).cores[c].mout = (activeStep s pin).cont.mout[c.val] := by
  have hq : (m.rq && pin.rstn) = true := by rw [← hrel.rstQ]; exact hact
  have hq2 : ((absChip s).rq && pin.rstn) = true := by simpa [absChip, runRst] using hact
  have hmach : Machine.step (absChip s) pin = (Machine.runStep (absChip s) pin).1 := by
    simp [Machine.step, Machine.stepObs, hq2]
  have hfrz : m.dbg.frz = (absChip s).dbg.frz := by rw [dbgRel_frz hrel.dbg]; rfl
  have hcfgA : (absChip s).cfg = s.cont.cfg := rfl
  have hpmemA : (absChip s).pmem = s.cont.pmem := rfl
  rw [step_mout m pin hq c]
  have hcont : (activeStep s pin).cont.mout[c.val] =
      (Machine.step (absChip s) pin).cores[c].mout := by
    show (contentsNext s pin).mout[c.val] = _
    simp only [contentsNext]
    rw [vgetNat_ofFn _ _ c.isLt, ← hmach]
    rfl
  rw [hcont, step_mout (absChip s) pin hq2 c]
  have hcs : m.cores[c].mout = (absChip s).cores[c].mout := by
    rw [hrel.mout c]
    exact (absChip_mout s c).symm
  rw [hfetch c, hrel.cfg, hcfgA, hrel.pmem, hpmemA, hfrz]
  exact coreNext_mout_congr' m.cores[c] (absChip s).cores[c]
    (Machine.cfgView s.cont.cfg) ((mhcCbs m pin)[c]) ((mhcCbs (absChip s) pin)[c])
    (((mhcCbs (absChip s) pin)[c]).fetch.map fun a => Machine.progWord s.cont.pmem[c] a)
    (absChip s).dbg.frz hcs

/-! ## 7. The cut-side reachable invariant `AbsInv`

`ChipRel s (absChip s)` needs two cut-side shape invariants that `Inv` does not
carry: the host byte-state/command round trip and the streams' `¬(RQ ∧ LD)`.
They are collected in `AbsInv`, proved at reset, preserved by one product step
and lifted to the trace.  (The `BankRel` clause of `ChipRel` is the pre-existing
latch-image contract, carried separately, see §9.) -/

/-- The host byte-state shape: one of the five `HostCmd` states, a non-command
history byte in the ignored transaction, `isRd` exactly for a read command byte,
and `HostCmd`'s own `Tagged` invariant. -/
def HostShape (t : HostCmd.State) : Prop :=
  (t.phase = HostCmd.ST_CMD ∨ t.phase = HostCmd.ST_AH ∨ t.phase = HostCmd.ST_AL ∨
      t.phase = HostCmd.ST_DATA ∨ t.phase = HostCmd.ST_IGN) ∧
    (t.phase = HostCmd.ST_IGN →
      t.cmd ≠ HostCmd.CMD_WRITE ∧ t.cmd ≠ HostCmd.CMD_READ) ∧
    ((t.isRd = true) ↔ (t.cmd = HostCmd.CMD_READ)) ∧ HostCmd.Tagged t

/-- The cut-side reachable invariant for the canonical abstraction. -/
structure AbsInv (s : State) : Prop where
  /-- The host byte-state shape. -/
  host : HostShape s.hostCmd
  /-- Stream 0 never has `RQ` and `LD` set together. -/
  s0 : ¬ ((streamAt s 0).rq = true ∧ (streamAt s 0).ld = true)
  /-- Stream 1 never has `RQ` and `LD` set together. -/
  s1 : ¬ ((streamAt s 1).rq = true ∧ (streamAt s 1).ld = true)

/-! ### Host shape lemmas -/

/-- `cmdOf` of a command byte is nonzero. -/
theorem cmdOf_ne_zero {c : BitVec 8} (h : c = HostCmd.CMD_WRITE ∨ c = HostCmd.CMD_READ) :
    cmdOf c ≠ 0 := by
  rcases h with rfl | rfl <;> decide

/-- `cmdOf` of a non-command byte is zero. -/
theorem cmdOf_eq_zero {c : BitVec 8} (h1 : c ≠ HostCmd.CMD_WRITE)
    (h2 : c ≠ HostCmd.CMD_READ) : cmdOf c = 0 := by
  simp only [cmdOf, HostCmd.CMD_WRITE, HostCmd.CMD_READ] at h1 h2 ⊢
  split <;> simp_all

/-- `cmdOf` never takes the code `3`. -/
theorem cmdOf_ne_three (c : BitVec 8) : cmdOf c ≠ 3 := by
  by_cases h1 : c = HostCmd.CMD_READ
  · rw [cmdOf, if_pos h1]; decide
  · by_cases h2 : c = HostCmd.CMD_WRITE
    · rw [cmdOf, if_neg h1, if_pos h2]; decide
    · rw [cmdOf, if_neg h1, if_neg h2]; decide

/-- A read command byte has `cmdOf = 2`. -/
theorem cmdOf_read {c : BitVec 8} (h : c = HostCmd.CMD_READ) : cmdOf c = 2 := by
  subst h; decide

/-- The byte state stays in the five encoded states. -/
theorem phaseNext_mem (t : HostCmd.State) (i : HostCmd.Input)
    (h : t.phase = HostCmd.ST_CMD ∨ t.phase = HostCmd.ST_AH ∨ t.phase = HostCmd.ST_AL ∨
      t.phase = HostCmd.ST_DATA ∨ t.phase = HostCmd.ST_IGN) :
    HostCmd.phaseNext t i = HostCmd.ST_CMD ∨ HostCmd.phaseNext t i = HostCmd.ST_AH ∨
      HostCmd.phaseNext t i = HostCmd.ST_AL ∨ HostCmd.phaseNext t i = HostCmd.ST_DATA ∨
      HostCmd.phaseNext t i = HostCmd.ST_IGN := by
  simp only [HostCmd.phaseNext]
  rcases h with hp | hp | hp | hp | hp <;> rw [hp]
  · -- command byte
    by_cases h1 : i.resetN = true
    · by_cases h2 : i.csN = true
      · left; simp [h1, h2]
      · by_cases h3 : HostCmd.completing t i = true
        · by_cases h4 : HostCmd.byteIn t i = 2#8 ∨ HostCmd.byteIn t i = 3#8
          · right; left; simp [h1, h2, h3, h4]
          · right; right; right; right; simp [h1, h2, h3, h4]
        · left; simp [h1, h2, h3]
    · left; simp [h1]
  · -- address high
    by_cases h1 : i.resetN = true
    · by_cases h2 : i.csN = true
      · left; simp [h1, h2]
      · by_cases h3 : HostCmd.completing t i = true
        · right; right; left; simp [h1, h2, h3]
        · right; left; simp [h1, h2, h3]
    · left; simp [h1]
  · -- address low
    by_cases h1 : i.resetN = true
    · by_cases h2 : i.csN = true
      · left; simp [h1, h2]
      · by_cases h3 : HostCmd.completing t i = true
        · right; right; right; left; simp [h1, h2, h3]
        · right; right; left; simp [h1, h2, h3]
    · left; simp [h1]
  · -- data
    by_cases h1 : i.resetN = true
    · by_cases h2 : i.csN = true
      · left; simp [h1, h2]
      · by_cases h3 : HostCmd.completing t i = true
        · right; right; right; left; simp [h1, h2, h3]
        · right; right; right; left; simp [h1, h2, h3]
    · left; simp [h1]
  · -- ignored
    by_cases h1 : i.resetN = true
    · by_cases h2 : i.csN = true
      · left; simp [h1, h2]
      · by_cases h3 : HostCmd.completing t i = true
        · right; right; right; right; simp [h1, h2, h3]
        · right; right; right; right; simp [h1, h2, h3]
    · left; simp [h1]

/-- An ignored byte state carries a non-command history byte (preservation needs
the same fact at the previous state: in the ignored state the phase does not
move). -/
theorem phaseNext_ign (t : HostCmd.State) (i : HostCmd.Input)
    (hprev : t.phase = HostCmd.ST_IGN →
      t.cmd ≠ HostCmd.CMD_WRITE ∧ t.cmd ≠ HostCmd.CMD_READ) :
    HostCmd.phaseNext t i = HostCmd.ST_IGN →
      HostCmd.cmdNext t i ≠ HostCmd.CMD_WRITE ∧ HostCmd.cmdNext t i ≠ HostCmd.CMD_READ := by
  intro h
  by_cases h1 : i.resetN = true
  · by_cases h2 : i.csN = true
    · simp [HostCmd.phaseNext, h1, h2] at h
    · by_cases h3 : HostCmd.completing t i = true
      · by_cases h4 : t.phase = 0#3
        · have hne : HostCmd.byteIn t i ≠ 2#8 ∧ HostCmd.byteIn t i ≠ 3#8 := by
            simpa [HostCmd.phaseNext, h1, h2, h3, h4] using h
          rw [HostCmd.cmdNext, if_neg (by simp [h1]), if_neg h2,
            if_pos (by simp [h3, h4])]
          exact hne
        · have hp : t.phase = 4#3 := by
            by_cases h5 : t.phase = 1#3
            · simp [HostCmd.phaseNext, h1, h2, h3, h4, h5] at h
            · by_cases h6 : t.phase = 2#3
              · simp [HostCmd.phaseNext, h1, h2, h3, h4, h5, h6] at h
              · simpa [HostCmd.phaseNext, h1, h2, h3, h4, h5, h6] using h
          rw [HostCmd.cmdNext, if_neg (by simp [h1]), if_neg h2,
            if_neg (by simp [h3, h4])]
          exact hprev (by simpa using hp)
      · have hp : t.phase = 4#3 := by
          simpa [HostCmd.phaseNext, h1, h2, h3] using h
        rw [HostCmd.cmdNext, if_neg (by simp [h1]), if_neg h2, if_neg (by simp [h3])]
        exact hprev (by simpa using hp)
  · have h1' : i.resetN = false := by simpa using h1
    simp [HostCmd.phaseNext, h1'] at h

/-- `cmdOf` is `2` exactly for the read command byte. -/
theorem cmdOf_eq_two (c : BitVec 8) : (cmdOf c = 2) ↔ (c = HostCmd.CMD_READ) := by
  constructor
  · intro h
    by_cases h1 : c = HostCmd.CMD_READ
    · exact h1
    · by_cases h2 : c = HostCmd.CMD_WRITE
      · rw [cmdOf, if_neg h1, if_pos h2] at h
        exact absurd h (by decide)
      · rw [cmdOf, if_neg h1, if_neg h2] at h
        exact absurd h (by decide)
  · intro h; rw [h]; decide

/-- The converse of `isRdNext_imp`: a read command byte leaves `isRd` set. -/
theorem isRdNext_back (t : HostCmd.State) (i : HostCmd.Input)
    (h : t.cmd = HostCmd.CMD_READ → t.isRd = true) :
    HostCmd.cmdNext t i = HostCmd.CMD_READ → HostCmd.isRdNext t i = true := by
  intro h1
  by_cases hrn : i.resetN = true
  · by_cases hcs : i.csN = true
    · have hc : t.cmd = HostCmd.CMD_READ := by
        simpa [HostCmd.cmdNext, hrn, hcs] using h1
      rw [HostCmd.isRdNext, if_neg (by simp [hrn])]
      rw [if_neg (by
        intro hc2
        simp [HostCmd.completing, HostCmd.sr, hcs] at hc2)]
      exact h hc
    · by_cases hcm : HostCmd.completing t i = true
      · by_cases hp : t.phase = 0#3
        · have hpb : (t.phase == HostCmd.ST_CMD) = true := by simpa using hp
          have hb : HostCmd.byteIn t i = HostCmd.CMD_READ := by
            simpa [HostCmd.cmdNext, hrn, hcs, hcm, hp] using h1
          rw [HostCmd.isRdNext, if_neg (by simp [hrn]), if_pos hcm, if_pos hpb]
          rw [hb]; rfl
        · have hc : t.cmd = HostCmd.CMD_READ := by
            simpa [HostCmd.cmdNext, hrn, hcs, hcm, hp] using h1
          rw [HostCmd.isRdNext, if_neg (by simp [hrn]), if_pos hcm,
            if_neg (by simpa using hp)]
          exact h hc
      · have hc : t.cmd = HostCmd.CMD_READ := by
          simpa [HostCmd.cmdNext, hrn, hcs, hcm] using h1
        rw [HostCmd.isRdNext, if_neg (by simp [hrn]), if_neg hcm]
        exact h hc
  · have hr : i.resetN = false := by simpa using hrn
    simp [HostCmd.cmdNext, hr] at h1

/-- A latched read is a read command. -/
theorem isRdNext_imp (t : HostCmd.State) (i : HostCmd.Input)
    (h : t.isRd = true → t.cmd = HostCmd.CMD_READ) :
    HostCmd.isRdNext t i = true → HostCmd.cmdNext t i = HostCmd.CMD_READ := by
  intro h1
  by_cases hrn : i.resetN = true
  · have h1' : (if HostCmd.completing t i then
        (if (t.phase == HostCmd.ST_CMD) then (HostCmd.byteIn t i == HostCmd.CMD_READ) else t.isRd)
      else t.isRd) = true := by
      simpa [HostCmd.isRdNext, hrn] using h1
    by_cases hcm : HostCmd.completing t i = true
    · rw [if_pos hcm] at h1'
      by_cases hp : t.phase = 0#3
      · have hpb : (t.phase == HostCmd.ST_CMD) = true := by simpa using hp
        rw [if_pos hpb] at h1'
        by_cases hcs : i.csN = true
        · exfalso
          simp [HostCmd.completing, HostCmd.sr, hcs] at hcm
        · rw [HostCmd.cmdNext, if_neg (by simp [hrn]), if_neg hcs,
            if_pos (by simp [hcm, hp])]
          simpa using h1'
      · have hpb : ¬(t.phase == HostCmd.ST_CMD) = true := by simpa using hp
        rw [if_neg hpb] at h1'
        have hir : t.isRd = true := h1'
        rw [HostCmd.cmdNext, if_neg (by simp [hrn])]
        by_cases hcs : i.csN = true
        · rw [if_pos hcs]; exact h hir
        · rw [if_neg hcs, if_neg (by simp [hcm, hp])]
          exact h hir
    · rw [if_neg hcm] at h1'
      have hir : t.isRd = true := h1'
      rw [HostCmd.cmdNext, if_neg (by simp [hrn])]
      by_cases hcs : i.csN = true
      · rw [if_pos hcs]; exact h hir
      · rw [if_neg hcs, if_neg (by simp [hcm])]
        exact h hir
  · have hr : i.resetN = false := by simpa using hrn
    simp [HostCmd.isRdNext, hr] at h1

/-- `isRd` is preserved as the exact read-command flag. -/
theorem isRdNext_iff (t : HostCmd.State) (i : HostCmd.Input)
    (h : (t.isRd = true) ↔ (t.cmd = HostCmd.CMD_READ)) :
    (HostCmd.isRdNext t i = true) ↔ (HostCmd.cmdNext t i = HostCmd.CMD_READ) :=
  ⟨isRdNext_imp t i h.1, isRdNext_back t i h.2⟩

/-- The host shape is preserved by one sampled edge. -/
theorem hostShape_step (t : HostCmd.State) (i : HostCmd.Input) (h : HostShape t) :
    HostShape (HostCmd.step t i) := by
  obtain ⟨hp, hign, hisrd, htag⟩ := h
  refine ⟨phaseNext_mem t i hp, phaseNext_ign t i hign, isRdNext_iff t i hisrd,
    HostCmd.tagged_step t i htag⟩

/-! ### The streams' `RQ`/`LD` exclusion -/

/-- `RQ` and `LD` are never set together: `LD'` is either clear or `RQ'` is. -/
theorem stream_rqLd_step (cap : Bool) (st : Stream.State) (i : Stream.Input)
    (h : ¬ (st.rq = true ∧ st.ld = true)) :
    ¬ ((Stream.step cap st i).rq = true ∧ (Stream.step cap st i).ld = true) := by
  have hb : (st.rq && st.ld) = false := by
    cases hr : st.rq <;> cases hl : st.ld <;> simp_all
  intro hcon
  obtain ⟨h1, h2⟩ := hcon
  have hrq : (Stream.step cap st i).rq = Stream.rqNext cap st i := rfl
  have hld : (Stream.step cap st i).ld = Stream.ldNext cap st i := rfl
  rw [hrq] at h1
  rw [hld] at h2
  simp only [Stream.rqNext, Stream.ldNext, Stream.rpl, Stream.cen, Stream.txMode, hb] at h1 h2
  bv_decide

/-! ### Reset and one-step preservation -/

/-- `absInv_reset`. -/
theorem absInv_reset (cont : Contents) : AbsInv (resetState cont) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [resetState, HostCmd.resetState]
    · intro h
      simp [resetState, HostCmd.resetState] at h
    · simp [resetState, HostCmd.resetState]
    · simpa [resetState, HostCmd.resetState] using HostCmd.tagged_resetState
  · rw [streamAt_resetState]; simp [Stream.resetState]
  · rw [streamAt_resetState]; simp [Stream.resetState]

/-- `absInv_step`: one product step preserves `AbsInv`. -/
theorem absInv_step (s : State) (pin : Machine.PinIn) (hinv : Inv s) (h : AbsInv s) :
    AbsInv (step s pin) := by
  by_cases hrun : runRst s pin = true
  · have hstep : step s pin = activeStep s pin := by simp [step, hrun]
    rw [hstep]
    have hh : (activeStep s pin).hostCmd = HostCmd.step s.hostCmd (hostCmdIn s pin) := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hh]
      exact hostShape_step s.hostCmd (hostCmdIn s pin) h.host
    · have hs : streamAt (activeStep s pin) 0 = (activeStep s pin).streams[(0 : Fin 2)] :=
        streamAt_get _ (0 : Fin 2)
      rw [hs, activeStep_streams]
      exact stream_rqLd_step ((0 : Fin 2).val == 0) (streamAt s 0) (streamIn s pin 0) h.s0
    · have hs : streamAt (activeStep s pin) 1 = (activeStep s pin).streams[(1 : Fin 2)] :=
        streamAt_get _ (1 : Fin 2)
      rw [hs, activeStep_streams]
      exact stream_rqLd_step ((1 : Fin 2).val == 0) (streamAt s 1) (streamIn s pin 1) h.s1
  · have hstep : step s pin = resetChip s pin := by simp [step, hrun]
    rw [hstep]
    have hh : (resetChip s pin).hostCmd = HostCmd.resetState := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hh]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [HostCmd.resetState]
      · intro hq
        simp [HostCmd.resetState] at hq
      · simp [HostCmd.resetState]
      · exact HostCmd.tagged_resetState
    · rw [streamAt_resetChip]
      simp [Stream.resetState]
    · rw [streamAt_resetChip]
      simp [Stream.resetState]

/-- `AbsInv` along the product trace from the reset state. -/
theorem absInv_trace (pins : Nat → Machine.PinIn) (cont : Contents) :
    ∀ n, AbsInv (cutStateAt pins (resetState cont) n) := by
  intro n
  induction n with
  | zero => exact absInv_reset cont
  | succ n ih =>
    rw [cutStateAt_succ]
    exact absInv_step _ _ (inv_trace pins cont n) ih

/-! ### `ChipRel s (absChip s)`

The canonical abstraction is related to its own cut state, given `Inv` (for the
host-link register agreement the relation does not re-derive), `AbsInv` and the
latch-image contract `BankRel s.bank s.cont.cfg` (the contract `premise_bank`
consumes; `Inv` does not carry it, see §9). -/

/-- Two 8-bit halves concatenate to `x * 2^8 + y`. -/
theorem cat8_toNat (x y : BitVec 8) : (x ++ y).toNat = x.toNat * 2 ^ 8 + y.toNat := by
  rw [BitVec.toNat_append, Nat.shiftLeft_eq, Nat.or_comm,
    Bridge.Glue.or_shift y.toNat x.toNat 8 y.isLt]

/-- A 16-bit word splits into its high and low synchroniser bytes. -/
theorem split16 (a : BitVec 16) :
    BitVec.truncate 8 (BitVec.ushiftRight a 8) ++ BitVec.truncate 8 a = a := by
  apply BitVec.eq_of_toNat_eq
  rw [cat8_toNat, BitVec.truncate_eq_setWidth, BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have hshift : (BitVec.ushiftRight a 8).toNat = a.toNat / 2 ^ 8 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [hshift]
  have h256 : a.toNat / 2 ^ 8 % 2 ^ 8 = a.toNat / 2 ^ 8 := by
    apply Nat.mod_eq_of_lt
    have := a.isLt
    omega
  rw [h256]
  have hdm := Nat.mod_add_div a.toNat (2 ^ 8)
  omega

/-- The selected thread is the thread-file slot. -/
theorem threadAt_get (s : State) (t : Fin 6) : threadAt s t.val = s.threads[t.val] := by
  rcases t with ⟨n, hn⟩
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The abstraction's core `c` is `absCore` of the cut's core `c`. -/
theorem absChip_cores (s : State) (c : Fin 2) :
    (absChip s).cores[c] = Bridge.Core.absCore (s.cont.mout[c.val]) (s.cores[c.val]) := by
  simp [absChip, vecGet_ofFn]

/-- The host byte-state round trip: the cut's `phase` is `phaseOf` of the
machine host record the abstraction builds (`nbyteOf`/`cmdOf`/`phaseOf`). -/
theorem phase_absChip (s : State) (h : HostShape s.hostCmd) :
    s.hostCmd.phase = Bridge.Host.phaseOf (absChip s).host := by
  obtain ⟨hph, hign, hisrd, htag⟩ := h
  simp only [Bridge.Host.phaseOf]
  rw [show (absChip s).host.nbyte = nbyteOf s.hostCmd.phase from rfl,
    show (absChip s).host.cmd = cmdOf s.hostCmd.cmd from rfl]
  rcases hph with hp | hp | hp | hp | hp
  · -- command byte
    rw [hp]
    simp [nbyteOf, HostCmd.ST_CMD]
  · -- address high
    rw [hp]
    have hc : cmdOf s.hostCmd.cmd ≠ 0 := cmdOf_ne_zero (htag (Or.inl hp)).1
    have hc' : (cmdOf s.hostCmd.cmd).toNat ≠ 0 := by
      intro hz
      exact hc (BitVec.eq_of_toNat_eq (by simpa using hz))
    simp [nbyteOf, hc', HostCmd.ST_AH, HostCmd.ST_IGN, HostCmd.ST_CMD]
  · -- address low
    rw [hp]
    have hc : cmdOf s.hostCmd.cmd ≠ 0 := cmdOf_ne_zero (htag (Or.inr (Or.inl hp))).1
    have hc' : (cmdOf s.hostCmd.cmd).toNat ≠ 0 := by
      intro hz
      exact hc (BitVec.eq_of_toNat_eq (by simpa using hz))
    simp [nbyteOf, hc', HostCmd.ST_AL, HostCmd.ST_AH, HostCmd.ST_IGN, HostCmd.ST_CMD]
  · -- data
    rw [hp]
    have hc : cmdOf s.hostCmd.cmd ≠ 0 := cmdOf_ne_zero (htag (Or.inr (Or.inr hp))).1
    have hc' : (cmdOf s.hostCmd.cmd).toNat ≠ 0 := by
      intro hz
      exact hc (BitVec.eq_of_toNat_eq (by simpa using hz))
    simp [nbyteOf, hc', HostCmd.ST_DATA, HostCmd.ST_AL, HostCmd.ST_AH, HostCmd.ST_IGN,
      HostCmd.ST_CMD]
  · -- ignored
    rw [hp]
    have hz : (cmdOf s.hostCmd.cmd).toNat = 0 := by
      rw [cmdOf_eq_zero (hign hp).1 (hign hp).2]; rfl
    simp [nbyteOf, hz, HostCmd.ST_IGN, HostCmd.ST_AH, HostCmd.ST_CMD]

/-- `AbsRelB` holds between a stream state and its own abstraction, given the
`RQ`/`LD` exclusion (the only non-reflexive conjunct, `BufRel`'s third). -/
theorem absRelB_abs (cap : Bool) (st : Stream.State)
    (h : ¬ (st.rq = true ∧ st.ld = true)) :
    Bridge.StreamB.AbsRelB cap st (Bridge.StreamB.abs st) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  refine ⟨?_, ?_, h⟩
  · intro hc
    exact ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩
  · intro hc
    exact ⟨rfl, rfl, rfl⟩

/-- `ChipRel` of the canonical abstraction, from `Inv`, `AbsInv` and the
latch-image contract. -/
theorem chipRel_absChip_of_bank (s : State) (hinv : Inv s) (habs : AbsInv s)
    (hbank : BankRel s.bank s.cont.cfg) : ChipRel s (absChip s) := by
  obtain ⟨hph, hign, hisrd, htag⟩ := habs.host
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, hbank, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- sync
    refine ⟨(split16 s.sync.s1).symm, (split16 s.sync.s2).symm, (split16 s.sync.sp).symm⟩
  · -- lines
    intro l
    simp [absChip, vecGet_ofFn, lineAt_get]
  · -- threads
    intro t
    simp [absChip, vecGet_ofFn, threadAt_get]
  · -- cores
    intro c
    rw [absChip_cores]
    exact ⟨rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- mout
    intro c
    rw [absChip_cores]
    rfl
  · -- units
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro k; simp [absChip, vecGet_ofFn]
    · intro k; simp [absChip, vecGet_ofFn, shAt_get]
    · intro k; simp [absChip, vecGet_ofFn, cntAt_get]
    · intro k; simp [absChip, vecGet_ofFn, lfAt_get]
  · -- p0
    exact p0Rel_abs s.p0
  · -- streams
    intro k
    have hk : ¬ ((streamAt s k.val).rq = true ∧ (streamAt s k.val).ld = true) := by
      rcases k with ⟨n, hn⟩
      rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
      · exact habs.s0
      · exact habs.s1
    have hs : (absChip s).streams[k] = Bridge.StreamB.abs (streamAt s k.val) := by
      simp [absChip, vecGet_ofFn, streamAt_get]
    rw [hs]
    exact absRelB_abs (k.val == 0) (streamAt s k.val) hk
  · -- host
    refine ⟨?_, rfl, ?_⟩
    · rw [HostPins.toHostCmd_agrees s.hostRead s.hostCmd hinv.hostAgrees]
      refine ⟨phase_absChip s habs.host, rfl, ?_, ?_, ?_, ?_, rfl, rfl, ?_, rfl, ?_⟩
      · -- receive shift register width
        show s.hostCmd.rx.toNat = (BitVec.setWidth 8 s.hostCmd.rx).toNat % 128
        have hx : s.hostCmd.rx.toNat < 128 := by simpa using s.hostCmd.rx.isLt
        rw [BitVec.toNat_setWidth]
        have h256 : s.hostCmd.rx.toNat % 2 ^ 8 = s.hostCmd.rx.toNat :=
          Nat.mod_eq_of_lt (by have := s.hostCmd.rx.isLt; omega)
        have h128 : s.hostCmd.rx.toNat % 128 = s.hostCmd.rx.toNat :=
          Nat.mod_eq_of_lt hx
        rw [h256, h128]
      · -- `cmd` code zero
        show (cmdOf s.hostCmd.cmd = 0) ↔
          (s.hostCmd.cmd ≠ HostCmd.CMD_WRITE ∧ s.hostCmd.cmd ≠ HostCmd.CMD_READ)
        constructor
        · intro hz
          by_cases hw : s.hostCmd.cmd = HostCmd.CMD_WRITE
          · rw [hw] at hz; simp [cmdOf] at hz
          · by_cases hr : s.hostCmd.cmd = HostCmd.CMD_READ
            · rw [hr] at hz; simp [cmdOf] at hz
            · exact ⟨hw, hr⟩
        · intro hc
          exact cmdOf_eq_zero hc.1 hc.2
      · -- `cmd` code never three
        show cmdOf s.hostCmd.cmd ≠ 3
        exact cmdOf_ne_three _
      · -- `isRd` exactly for a read command byte
        show (s.hostCmd.isRd = true) ↔ (cmdOf s.hostCmd.cmd = 2)
        exact (habs.host.2.2.1).trans (Iff.symm (cmdOf_eq_two s.hostCmd.cmd))
      · -- write byte while strobing
        intro _
        rfl
      · -- register-read acknowledgement of the command state
        obtain ⟨-, -, -, -, -, -, -, -, hrack⟩ := hinv.hostAgrees
        exact hrack.symm
    · -- waiting acknowledgement value
      intro _
      rfl
  · -- control
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- debug
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- config write
    exact cwRel_abs s.cq s.arb

/-- `ChipRel` of the canonical abstraction: the latch-image contract comes from
any related machine state (`ChipRel.bank` transported along `ChipRel.cfg`). -/
theorem chipRel_absChip (s : State) (m : Machine.State) (hrel : ChipRel s m) (hinv : Inv s)
    (habs : AbsInv s) : ChipRel s (absChip s) :=
  chipRel_absChip_of_bank s hinv habs (by
    rw [← hrel.cfg]
    exact hrel.bank)

/-- The `CoreInputBus` at the canonical abstraction. -/
theorem coreInputBus_abs (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) (habs : AbsInv s)
    (hG : Bridge.Glue.GuardTable) (hS : Bridge.Glue.SrcTable) (c : Fin 2) :
    CoreInputBus s (absChip s) pin c (sIr s (absChip s) c) :=
  coreInputBus hG hS s (absChip s) pin c (chipRel_absChip s m hrel hinv habs) hinv hact

/-- **The projection congruence with the side hypothesis `hrelA` replaced by the
reachable invariant `AbsInv`.**  This is the form `premise_contents` can consume:
`ChipRel s m`, `Inv s`, `runRst s pin = true`, `AbsInv s` and the global tables. -/
theorem contents_open_proj_abs (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true) (habs : AbsInv s)
    (hG : Bridge.Glue.GuardTable) (hS : Bridge.Glue.SrcTable)
    (hJGTab : ∀ n : Nat,
      Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
        Core.JG_TABLE.getD n 62)
    (c : Fin 2) :
    (mhcCbs m pin)[c].load = (mhcCbs (absChip s) pin)[c].load ∧
      (mhcCbs m pin)[c].jmp = (mhcCbs (absChip s) pin)[c].jmp ∧
      (mhcCbs m pin)[c].disp = (mhcCbs (absChip s) pin)[c].disp ∧
      ((mhcCbs m pin)[c].disp = true →
        (mhcCbs m pin)[c].dispThread = (mhcCbs (absChip s) pin)[c].dispThread) ∧
      (mhcCbs m pin)[c].fetch = (mhcCbs (absChip s) pin)[c].fetch :=
  contents_open_proj s m pin hrel hinv hact (chipRel_absChip s m hrel hinv habs) hG hS hJGTab c

/-! ## 9. The one clause `AbsInv` does not cover: the latch-image contract

`ChipRel`'s `bank` clause relates the cut's latch bank to the *machine's*
configuration image; `Inv` and `AbsInv` say nothing about the bank, so the
`hrel`-free form `Inv s → AbsInv s → ChipRel s (absChip s)` is false.  The
witness below is a reset state with a nonzero latch under a full mask: `Inv` and
`AbsInv` hold, `BankRel` does not.  This is the same stated contract that
`MemHostCfg.premise_bank` consumes as `bank_open_mask`/`bank_open_cfg`/
`bank_open_size`; `chipRel_absChip` above takes it from the related state. -/

/-- A reset state with a one-byte `0xFF` configuration image and a fully masked,
zero latch: the latch reads `0` while the image byte is `0xFF`. -/
def bankBroken : State :=
  { resetState { Contents.init with cfg := ⟨ByteArray.mk (Array.mk [0xFF])⟩ } with
    bank := ⟨fun _ => 0xFF, fun _ => 0⟩ }

/-- `Inv` is bank- and image-independent. -/
theorem bankBroken_inv : Inv bankBroken := by
  obtain ⟨a1, a2, a3, a4⟩ := inv_reset Contents.init
  exact ⟨a1, a2, a3, a4⟩

/-- `AbsInv` is bank- and image-independent. -/
theorem bankBroken_absInv : AbsInv bankBroken := by
  obtain ⟨a1, a2, a3⟩ := absInv_reset Contents.init
  exact ⟨a1, a2, a3⟩

/-- The latch-image contract fails at the broken bank: the image byte reads
`0xFF`, the latch reads `0`. -/
theorem bankBroken_not_bankRel : ¬ BankRel bankBroken.bank bankBroken.cont.cfg := by
  intro h
  have hbyte := h.2 ⟨0, by decide⟩
  exact (by decide : ¬ (Bank.read bankBroken.bank ⟨0, by decide⟩ =
    BitVec.ofNat 8 (Machine.Util.cfgByte bankBroken.cont.cfg (Machine.Tables.LINE_BASE + 0)) &&&
      bankBroken.bank.mask ⟨0, by decide⟩)) hbyte

/-- **The `hrel`-free form is false**: `Inv` and `AbsInv` do not imply
`ChipRel s (absChip s)`. -/
theorem chipRel_absChip_needs_bank :
    ∃ s : State, Inv s ∧ AbsInv s ∧ ¬ ChipRel s (absChip s) :=
  ⟨bankBroken, bankBroken_inv, bankBroken_absInv, fun h => bankBroken_not_bankRel h.bank⟩

end Metronome.ChipCut.Discharge
