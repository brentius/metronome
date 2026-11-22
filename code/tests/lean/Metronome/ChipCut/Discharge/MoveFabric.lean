/-
# ChipCut discharge: the machine's padded six-slot move fabric

`Bridge.Moves.resolveMoves_pick` is stated for **six** machine moves (`six m`, one
per `(core, move slot)`), while `Machine.runStep` lists only the *enabled* moves
(`coreComb.moves` is a `filterMap`).  This file supplies

* the padding step (`resolveAux_null`, `resolveAux_filter_some`,
  `resolveMoves_filter_some`) — a move whose group is `none` leaves the resolver's
  state unchanged wherever it sits in the list;
* the six-slot padded machine list `machMove` (the machine's own move when the
  slot is enabled, a `dst = 0` placeholder otherwise), `mAllMoves_enum` and
  `resolveMoves_mAllMoves` — the machine resolves `mAllMoves` and the padded six
  slots identically (`foldl_filterMap_getD` is the general list lemma);
* `MoveBus` — the cross-model move-bus agreement, proved from `Bridge.Core.Rel`
  for the cut's `sIr`, a `Core.out` congruence (`out_move_congr`) and `ChipRel`
  (the `line`/`thread` slots read the core registers);
* `moveAgree_of_bus` / `moveTable_of_bus` — `Bridge.Moves.MoveAgree` and
  `MoveTable` for `bundleOf`, and `winners_machMove` — the machine's winners and
  conflict flag on the cut's bundle.

Everything is quantified over `(s m pin)` with `ChipRel`, `Inv`, the active-cycle
sample, the global string-table hypotheses and the core-input bus (the `cores`
task's single remaining wiring obligation, `CoreInputBus`).
-/
import Metronome.ChipCut.Proof
import Metronome.Bridge.Moves
import Metronome.Bridge.Core
import Metronome.Bridge.Units
import Metronome.Bridge.Glue
import Metronome.Bridge.Line
import Metronome.Bridge.Thread
import Metronome.Bridge.Mem
import Metronome.ChipCut.Discharge.CoreUnits
import Metronome.ChipCut.Discharge.LineThread
import Metronome.ChipCut.Discharge.Glue
import Metronome.ChipCut.Discharge.MemHostCfg
import Metronome.ChipCut.Discharge.StreamDbg

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 4096

namespace Metronome.ChipCut.Discharge.MoveFabric

open Metronome

/-! ## 1. The padding step (unchanged interface) -/

/-- A `NULL` move leaves the resolver state unchanged. -/
theorem stepOn_null (acc : Bridge.Moves.St) (m : Machine.Move)
    (h : Machine.moveGroup m = none) : Bridge.Moves.stepOn acc m = acc :=
  Bridge.Moves.stepOn_none acc m h

/-- A list of `NULL` moves is the identity on the resolver state. -/
theorem resolveAux_null (ms : List Machine.Move) (acc : Bridge.Moves.St)
    (h : ∀ m ∈ ms, Machine.moveGroup m = none) :
    Bridge.Moves.resolveAux ms acc = acc := by
  induction ms generalizing acc with
  | nil => rfl
  | cons m ms ih =>
    simp only [Bridge.Moves.resolveAux, List.foldl_cons]
    rw [stepOn_null acc m (h m List.mem_cons_self)]
    exact ih acc (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- Dropping the `NULL` moves anywhere in the list does not change the resolver
state. -/
theorem resolveAux_filter_some (ms : List Machine.Move) (acc : Bridge.Moves.St) :
    Bridge.Moves.resolveAux (ms.filter (fun m => (Machine.moveGroup m).isSome)) acc =
      Bridge.Moves.resolveAux ms acc := by
  induction ms generalizing acc with
  | nil => rfl
  | cons m ms ih =>
    by_cases hm : (Machine.moveGroup m).isSome = true
    · rw [List.filter_cons, if_pos hm]
      simp only [Bridge.Moves.resolveAux, List.foldl_cons]
      exact ih (Bridge.Moves.stepOn acc m)
    · have hn : Machine.moveGroup m = none := by
        cases hg : Machine.moveGroup m with
        | none => rfl
        | some g => rw [hg] at hm; exact absurd rfl hm
      rw [List.filter_cons, if_neg hm]
      simp only [Bridge.Moves.resolveAux, List.foldl_cons]
      rw [stepOn_null acc m hn]
      exact ih acc

/-- The same for `Machine.resolveMoves`: the padded six-slot list and the machine's
filtered list resolve to the same winners and conflict flag. -/
theorem resolveMoves_filter_some (ms : List Machine.Move) :
    Machine.resolveMoves (ms.filter (fun m => (Machine.moveGroup m).isSome)) =
      Machine.resolveMoves ms := by
  rw [Bridge.Moves.resolveMoves_eq, Bridge.Moves.resolveMoves_eq, resolveAux_filter_some]

/-- `six m` has six entries. -/
theorem six_length (m : Nat → Machine.Move) : (Bridge.Moves.six m).length = 6 := rfl

/-! ## 2. The six-slot padded machine list -/

/-- The core of slot `q` (`0..2` are core 0, `3..5` core 1). -/
def coreOf : Nat → Fin 2
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | _ => 1

/-- The placeholder written into a disabled slot: `NULL` destination, but the
slot's own core/line/thread (`MoveAgree.line`/`thread` are unconditional). -/
def machNull (s : State) (m : Machine.State) (c : Fin 2) (mi : Nat) : Machine.Move :=
  { Bridge.Core.moveVal m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
      (s.cores[c.val]) c.val mi with dst := 0 }

/-- The machine's move of slot `q`, when it has one. -/
def machSlot (m : Machine.State) (pin : Machine.PinIn) (q : Nat) : Option Machine.Move :=
  Bridge.Core.moveAt (mCoreComb m pin (coreOf q)) (q % 3)

/-- The machine's move of slot `q` this cycle (a `NULL` placeholder when the slot
is disabled). -/
def machMove (s : State) (m : Machine.State) (pin : Machine.PinIn) (q : Nat) : Machine.Move :=
  match machSlot m pin q with
  | some mv => mv
  | none => machNull s m (coreOf q) (q % 3)

theorem machMove_of_some {s m pin q mv} (h : machSlot m pin q = some mv) :
    machMove s m pin q = mv := by
  simp only [machMove, h]

theorem machMove_of_none {s m pin q} (h : machSlot m pin q = none) :
    machMove s m pin q = machNull s m (coreOf q) (q % 3) := by
  simp only [machMove, h]

/-- `machMove q` is the padded lookup of `machSlot q`. -/
theorem machMove_eq_getD (s : State) (m : Machine.State) (pin : Machine.PinIn) (q : Nat) :
    machMove s m pin q = (machSlot m pin q).getD (machNull s m (coreOf q) (q % 3)) := by
  simp only [machMove]
  cases machSlot m pin q <;> rfl

/-- `six` is the range map. -/
theorem six_eq_map (f : Nat → Machine.Move) :
    Bridge.Moves.six f = (List.range 6).map f := rfl

/-- A `filterMap` over a prefix is the padded `map` when the missing entries are
`NULL` moves: the general padding lemma behind `resolveMoves_mAllMoves`. -/
theorem foldl_filterMap_getD (g : Nat → Option Machine.Move) (pad : Nat → Machine.Move)
    (hpad : ∀ q, Machine.moveGroup (pad q) = none) :
    ∀ (n : Nat) (acc : Bridge.Moves.St),
      List.foldl Bridge.Moves.stepOn acc ((List.range n).filterMap g) =
        List.foldl Bridge.Moves.stepOn acc ((List.range n).map (fun q => (g q).getD (pad q)))
  | 0, acc => rfl
  | n + 1, acc => by
    rw [List.range_succ, List.filterMap_append, List.map_append, List.foldl_append,
      List.foldl_append, foldl_filterMap_getD g pad hpad n]
    cases h : g n with
    | none =>
      rw [List.filterMap_cons, List.filterMap_nil, List.map_cons, List.map_nil, h]
      simp only [List.foldl_cons, List.foldl_nil, Option.getD_none]
      exact (stepOn_null _ (pad n) (hpad n)).symm
    | some mv =>
      rw [List.filterMap_cons, List.filterMap_nil, List.map_cons, List.map_nil, h]
      simp only [List.foldl_cons, List.foldl_nil, Option.getD_some]

/-- The `resolveAux` form of `foldl_filterMap_getD`. -/
theorem resolveAux_filterMap_getD (g : Nat → Option Machine.Move) (pad : Nat → Machine.Move)
    (hpad : ∀ q, Machine.moveGroup (pad q) = none) (n : Nat) (acc : Bridge.Moves.St) :
    Bridge.Moves.resolveAux ((List.range n).filterMap g) acc =
      Bridge.Moves.resolveAux ((List.range n).map (fun q => (g q).getD (pad q))) acc :=
  foldl_filterMap_getD g pad hpad n acc

/-! ## 3. `mAllMoves` as the six padded slots -/

/-- The machine's `moveAt` is a `find?` on the core's move list. -/
theorem moveAt_def (cb : Machine.CoreComb) (mi : Nat) :
    Bridge.Core.moveAt cb mi = cb.moves.find? (fun mv => mv.idx == mi) := rfl

/-- One core's move list is the three slots' `moveAt` list (the padded six-slot
list's per-core half). -/
theorem coreComb_moves_enum (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2)
    (x : Core.State) (i : Core.Input)
    (h : Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) x i)
    (hfrz : m.dbg.frz = i.frz) :
    (mCoreComb m pin c).moves =
      (List.range 3).filterMap (fun mi => Bridge.Core.moveAt (mCoreComb m pin c) mi) := by
  have hcb : mCoreComb m pin c = Machine.coreComb m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (Bridge.Core.coreNat (c.val == 1)) i.frz := by
    simp only [mCoreComb, hfrz, coreNat_fin2]
  by_cases hxa : Core.xa x i = true
  · have hpt : ∀ mi, mi < 3 → Bridge.Core.moveAt (Machine.coreComb m (Machine.cfgView m.cfg)
        (Machine.pinView m.sync m.dbg) (Bridge.Core.coreNat (c.val == 1)) i.frz) mi =
        Bridge.Core.moveCand m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg) x
          (Bridge.Core.coreNat (c.val == 1)) mi :=
      fun mi hm => Bridge.Core.moveAt_eq_cand h hxa mi hm
    rw [hcb, Bridge.Core.coreComb_moves_of_xa h hxa, Bridge.Core.range3]
    simp only [List.filterMap_cons, List.filterMap_nil]
    rw [hpt 0 (by omega), hpt 1 (by omega), hpt 2 (by omega)]
  · have hxaf : Core.xa x i = false := by simpa using hxa
    have hnone : ∀ mi, mi < 3 → Bridge.Core.moveAt (Machine.coreComb m (Machine.cfgView m.cfg)
        (Machine.pinView m.sync m.dbg) (Bridge.Core.coreNat (c.val == 1)) i.frz) mi = none := by
      intro mi hm
      unfold Bridge.Core.moveAt
      rw [Bridge.Core.coreComb_moves_of_idle h hxaf]
      rfl
    rw [hcb, Bridge.Core.coreComb_moves_of_idle h hxaf, Bridge.Core.range3]
    simp only [List.filterMap_cons, List.filterMap_nil, hnone 0 (by omega), hnone 1 (by omega),
      hnone 2 (by omega)]

/-- The six-slot split of a `filterMap` over `range 6`. -/
theorem filterMap_six_split (f g h : Nat → Option Machine.Move)
    (e0 : f 0 = g 0) (e1 : f 1 = g 1) (e2 : f 2 = g 2)
    (e3 : f 3 = h 0) (e4 : f 4 = h 1) (e5 : f 5 = h 2) :
    (List.range 6).filterMap f =
      (List.range 3).filterMap g ++ (List.range 3).filterMap h := by
  rw [show List.range 6 = [0, 1, 2, 3, 4, 5] from by decide, Bridge.Core.range3]
  simp only [List.filterMap_cons, List.filterMap_nil, e0, e1, e2, e3, e4, e5]
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases h 0 <;> cases h 1 <;> cases h 2 <;> rfl

/-- The machine's enabled moves, in slot order, are the six slots of `machSlot`. -/
theorem mAllMoves_enum (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (h : ∀ c : Fin 2, Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (sIr s m c) (coreIn s pin c.val))
    (hfrz : ∀ c : Fin 2, m.dbg.frz = (coreIn s pin c.val).frz) :
    mAllMoves m pin = (List.range 6).filterMap (machSlot m pin) := by
  have h0 := coreComb_moves_enum m pin 0 (sIr s m 0) (coreIn s pin 0) (h 0) (hfrz 0)
  have h1 := coreComb_moves_enum m pin 1 (sIr s m 1) (coreIn s pin 1) (h 1) (hfrz 1)
  show (mCoreComb m pin 0).moves ++ (mCoreComb m pin 1).moves
      = (List.range 6).filterMap (machSlot m pin)
  rw [h0, h1]
  exact (filterMap_six_split (machSlot m pin)
    (fun mi => Bridge.Core.moveAt (mCoreComb m pin 0) mi)
    (fun mi => Bridge.Core.moveAt (mCoreComb m pin 1) mi)
    (by simp [machSlot, coreOf])
    (by simp [machSlot, coreOf])
    (by simp [machSlot, coreOf])
    (by simp [machSlot, coreOf])
    (by simp [machSlot, coreOf])
    (by simp [machSlot, coreOf])).symm

/-- **The machine's own list resolves like the padded six slots.** -/
theorem resolveMoves_mAllMoves (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hkind : Bridge.Moves.DstKindTable)
    (h : ∀ c : Fin 2, Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (sIr s m c) (coreIn s pin c.val))
    (hfrz : ∀ c : Fin 2, m.dbg.frz = (coreIn s pin c.val).frz) :
    Machine.resolveMoves (mAllMoves m pin) =
      Machine.resolveMoves (Bridge.Moves.six (machMove s m pin)) := by
  have hpad : ∀ q, Machine.moveGroup (machNull s m (coreOf q) (q % 3)) = none := by
    intro q
    exact Bridge.Moves.moveGroup_null_of_dst_zero hkind _ rfl
  have hmain : Bridge.Moves.resolveAux (mAllMoves m pin) ([], [], false)
      = Bridge.Moves.resolveAux (Bridge.Moves.six (machMove s m pin)) ([], [], false) := by
    rw [mAllMoves_enum s m pin h hfrz, six_eq_map]
    have h := resolveAux_filterMap_getD (machSlot m pin)
      (fun q => machNull s m (coreOf q) (q % 3)) hpad 6 ([], [], false)
    rw [show (fun q => (machSlot m pin q).getD (machNull s m (coreOf q) (q % 3)))
        = machMove s m pin from funext (fun q => (machMove_eq_getD s m pin q).symm)] at h
    exact h
  rw [Bridge.Moves.resolveMoves_eq, Bridge.Moves.resolveMoves_eq, hmain]

/-! ## 4. The cross-model move bus

`mvEn`/`mvDst`/`mvDat` are the cut's packed buses, `machSlot` the machine's own
list.  `MoveBus` is the per-slot agreement: the enabled bit is "the slot has a
move", and an enabled slot's destination/data words are the cut's slices.  Its
`grp`/`line`/`thread` fields are cut-side (`mvGrp = DG_MAP mvDst`, the core's
`XL`/`XT`), proved here from the cut's own definitions and `ChipRel`. -/

/-- `Core.out`'s move words read only `XV`, `IR` and `XL` of the core state. -/
theorem out_move_eq {s1 s2 : Core.State} {i : Core.Input} (c : Bool)
    (hxv : s1.xv = s2.xv) (hir : s1.ir = s2.ir) (hxl : s1.xl = s2.xl) :
    (Core.out c s1 i).mvEn = (Core.out c s2 i).mvEn ∧
    (Core.out c s1 i).mvSrc = (Core.out c s2 i).mvSrc ∧
    (Core.out c s1 i).mvDst = (Core.out c s2 i).mvDst ∧
    (Core.out c s1 i).mvData = (Core.out c s2 i).mvData := by
  cases s1
  cases s2
  simp_all only [Core.out, Core.mvEnAt, Core.xa, Core.i_g, Core.i_d, Core.i_s, Core.i_imm,
    Core.i_cond, Core.cc, Core.srcByte, Core.srcVec, Core.withSlot]
  simp

/-- `Core.out`'s move-bus fields are unchanged by an `IR` replacement that
only happens while `XV = 0` (the `ChipRel` core clause). -/
theorem out_move_congr {s1 s2 : Core.State} {i : Core.Input} (c : Bool) (mi : Nat)
    (hxv : s1.xv = s2.xv) (hir : s1.xv = true → s1.ir = s2.ir) (hxl : s1.xl = s2.xl) :
    (Core.bitOf (Core.out c s1 i).mvEn mi = Core.bitOf (Core.out c s2 i).mvEn mi) ∧
    (Core.bitOf (Core.out c s1 i).mvEn mi = true →
      Core.slice (Core.out c s1 i).mvDst (6 * mi) 6 =
        Core.slice (Core.out c s2 i).mvDst (6 * mi) 6 ∧
      Core.slice (Core.out c s1 i).mvData (8 * mi) 8 =
        Core.slice (Core.out c s2 i).mvData (8 * mi) 8) := by
  by_cases hx : s1.xv = true
  · have h := out_move_eq (s1 := s1) (s2 := s2) (i := i) c hxv (hir hx) hxl
    rw [h.1, h.2.2.1, h.2.2.2]
    exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  · have hx1 : s1.xv = false := by simpa using hx
    have hx2 : s2.xv = false := by rw [← hxv]; exact hx1
    have hz1 : Core.bitOf (Core.out c s1 i).mvEn mi = false := by
      rw [Core.mvEn_zero c s1 i (Or.inl hx1)]
      exact Bridge.Core.bitOf_zero mi
    have hz2 : Core.bitOf (Core.out c s2 i).mvEn mi = false := by
      rw [Core.mvEn_zero c s2 i (Or.inl hx2)]
      exact Bridge.Core.bitOf_zero mi
    rw [hz1, hz2]
    exact ⟨rfl, fun h => absurd h (by simp)⟩

/-- The same for `Core.out`'s **source** slice (the `HOST.IN`/`MEMHAZ` side). -/
theorem out_src_congr {s1 s2 : Core.State} {i : Core.Input} (c : Bool) (mi : Nat)
    (hxv : s1.xv = s2.xv) (hir : s1.xv = true → s1.ir = s2.ir) (hxl : s1.xl = s2.xl) :
    (Core.bitOf (Core.out c s1 i).mvEn mi = Core.bitOf (Core.out c s2 i).mvEn mi) ∧
    (Core.bitOf (Core.out c s1 i).mvEn mi = true →
      Core.slice (Core.out c s1 i).mvSrc (6 * mi) 6 =
        Core.slice (Core.out c s2 i).mvSrc (6 * mi) 6) := by
  by_cases hx : s1.xv = true
  · have h := out_move_eq (s1 := s1) (s2 := s2) (i := i) c hxv (hir hx) hxl
    rw [h.1, h.2.1]
    exact ⟨rfl, fun _ => rfl⟩
  · have hx1 : s1.xv = false := by simpa using hx
    have hx2 : s2.xv = false := by rw [← hxv]; exact hx1
    have hz1 : Core.bitOf (Core.out c s1 i).mvEn mi = false := by
      rw [Core.mvEn_zero c s1 i (Or.inl hx1)]
      exact Bridge.Core.bitOf_zero mi
    have hz2 : Core.bitOf (Core.out c s2 i).mvEn mi = false := by
      rw [Core.mvEn_zero c s2 i (Or.inl hx2)]
      exact Bridge.Core.bitOf_zero mi
    rw [hz1, hz2]
    exact ⟨rfl, fun h => absurd h (by simp)⟩

/-- `CoreCtl.bitAt` is `Core.bitOf`. -/
theorem bitAt_eq_bitOf {w : Nat} (v : BitVec w) (k : Nat) : CoreCtl.bitAt v k = Core.bitOf v k :=
  rfl

/-- A `Fin 2` index is `0` or `1` (as a `Fin` equality, so `subst` applies). -/
theorem fin2_cases (c : Fin 2) : c = 0 ∨ c = 1 := by
  rcases (by omega : c.val = 0 ∨ c.val = 1) with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-- The cut's six-slot destination slice `q` is core `q / 3`'s `mvDst` slice. -/
theorem mvDst_slot (s : State) (pin : Machine.PinIn) (c : Fin 2) (mi : Nat) (hmi : mi < 3) :
    Core.slice (mvDst s pin) (6 * (3 * c.val + mi)) 6 =
      Core.slice (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).mvDst
        (6 * mi) 6 := by
  rcases fin2_cases c with hc | hc
  · subst hc
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [slice_getLsbD (hj := hj), slice_getLsbD (hj := hj)]
    simp only [mvDst]
    have hidx : 6 * (3 * (0 : Fin 2).val + mi) + j = 6 * mi + j := by simp
    rw [BitVec.getLsbD_append, hidx]
    simp only [show (0 : Fin 2).val = 0 from rfl, show ((0 : Fin 2).val == 1) = false from rfl,
      show ((0 : Nat) == 1) = false from by decide,
      show 6 * mi + j < 18 by omega, if_true]
  · subst hc
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [slice_getLsbD (hj := hj), slice_getLsbD (hj := hj)]
    simp only [mvDst]
    have hidx : 6 * (3 * (1 : Fin 2).val + mi) + j = 18 + 6 * mi + j := by
      have h1 : (1 : Fin 2).val = 1 := rfl
      rw [h1]; omega
    rw [BitVec.getLsbD_append, hidx]
    simp only [show (1 : Fin 2).val = 1 from rfl, show ((1 : Fin 2).val == 1) = true from rfl,
      show ((1 : Nat) == 1) = true from by decide,
      show ¬ (18 + 6 * mi + j < 18) by omega, if_false,
      show 18 + 6 * mi + j - 18 = 6 * mi + j by omega]
  all_goals rfl

/-- The cut's six-slot data slice `q` is core `q / 3`'s `mvData` slice. -/

theorem mvSrc_slot (s : State) (pin : Machine.PinIn) (c : Fin 2) (mi : Nat) (hmi : mi < 3) :
    Core.slice (mvSrc s pin) (6 * (3 * c.val + mi)) 6 =
      Core.slice (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).mvSrc
        (6 * mi) 6 := by
  rcases fin2_cases c with hc | hc
  · subst hc
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [slice_getLsbD (hj := hj), slice_getLsbD (hj := hj)]
    simp only [mvSrc]
    have hidx : 6 * (3 * (0 : Fin 2).val + mi) + j = 6 * mi + j := by simp
    rw [BitVec.getLsbD_append, hidx]
    simp only [show (0 : Fin 2).val = 0 from rfl, show ((0 : Fin 2).val == 1) = false from rfl,
      show ((0 : Nat) == 1) = false from by decide,
      show 6 * mi + j < 18 by omega, if_true]
  · subst hc
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [slice_getLsbD (hj := hj), slice_getLsbD (hj := hj)]
    simp only [mvSrc]
    have hidx : 6 * (3 * (1 : Fin 2).val + mi) + j = 18 + 6 * mi + j := by
      have h1 : (1 : Fin 2).val = 1 := rfl
      rw [h1]; omega
    rw [BitVec.getLsbD_append, hidx]
    simp only [show (1 : Fin 2).val = 1 from rfl, show ((1 : Fin 2).val == 1) = true from rfl,
      show ((1 : Nat) == 1) = true from by decide,
      show ¬ (18 + 6 * mi + j < 18) by omega, if_false,
      show 18 + 6 * mi + j - 18 = 6 * mi + j by omega]
  all_goals rfl

/-- The cut's six-slot data slice `q` is core `q / 3`'s `mvData` slice. -/
theorem mvDat_slot (s : State) (pin : Machine.PinIn) (c : Fin 2) (mi : Nat) (hmi : mi < 3) :
    Core.slice (mvDat s pin) (8 * (3 * c.val + mi)) 8 =
      Core.slice (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).mvData
        (8 * mi) 8 := by
  rcases fin2_cases c with hc | hc
  · subst hc
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [slice_getLsbD (hj := hj), slice_getLsbD (hj := hj)]
    simp only [mvDat]
    have hidx : 8 * (3 * (0 : Fin 2).val + mi) + j = 8 * mi + j := by simp
    rw [BitVec.getLsbD_append, hidx]
    simp only [show (0 : Fin 2).val = 0 from rfl, show ((0 : Fin 2).val == 1) = false from rfl,
      show ((0 : Nat) == 1) = false from by decide,
      show 8 * mi + j < 24 by omega, if_true]
  · subst hc
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [slice_getLsbD (hj := hj), slice_getLsbD (hj := hj)]
    simp only [mvDat]
    have hidx : 8 * (3 * (1 : Fin 2).val + mi) + j = 24 + 8 * mi + j := by
      have h1 : (1 : Fin 2).val = 1 := rfl
      rw [h1]; omega
    rw [BitVec.getLsbD_append, hidx]
    simp only [show (1 : Fin 2).val = 1 from rfl, show ((1 : Fin 2).val == 1) = true from rfl,
      show ((1 : Nat) == 1) = true from by decide,
      show ¬ (24 + 8 * mi + j < 24) by omega, if_false,
      show 24 + 8 * mi + j - 24 = 8 * mi + j by omega]
  all_goals rfl

/-- The cut's `mv_en` bit `q` is core `q / 3`'s enable bit. -/
theorem mvEn_slot (s : State) (pin : Machine.PinIn) (c : Fin 2) (mi : Nat) (hmi : mi < 3) :
    CoreCtl.bitAt (mvEn s pin) (3 * c.val + mi) =
      Core.bitOf (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).mvEn mi := by
  rcases fin2_cases c with hc | hc
  · subst hc
    have hidx : 3 * (0 : Fin 2).val + mi = mi := by simp
    rw [bitAt_eq_bitOf, hidx, Bridge.Core.bitOf_eq_getLsbD]
    rw [show Core.bitOf (Core.out ((0 : Fin 2).val == 1) s.cores[(0 : Fin 2).val]
        (coreIn s pin (0 : Fin 2).val)).mvEn mi
        = (Core.out ((0 : Fin 2).val == 1) s.cores[(0 : Fin 2).val]
          (coreIn s pin (0 : Fin 2).val)).mvEn.getLsbD mi
        from Bridge.Core.bitOf_eq_getLsbD _ _]
    rw [mvEn, BitVec.getLsbD_append]
    simp only [show (0 : Fin 2).val = 0 from rfl, show ((0 : Fin 2).val == 1) = false from rfl,
      show ((0 : Nat) == 1) = false from by decide,
      show mi < 3 by omega, if_true]
  · subst hc
    have hidx : 3 * (1 : Fin 2).val + mi = 3 + mi := by
      have h1 : (1 : Fin 2).val = 1 := rfl
      rw [h1]
    rw [bitAt_eq_bitOf, hidx, Bridge.Core.bitOf_eq_getLsbD]
    rw [show Core.bitOf (Core.out ((1 : Fin 2).val == 1) s.cores[(1 : Fin 2).val]
        (coreIn s pin (1 : Fin 2).val)).mvEn mi
        = (Core.out ((1 : Fin 2).val == 1) s.cores[(1 : Fin 2).val]
          (coreIn s pin (1 : Fin 2).val)).mvEn.getLsbD mi
        from Bridge.Core.bitOf_eq_getLsbD _ _]
    rw [mvEn, BitVec.getLsbD_append]
    simp only [show (1 : Fin 2).val = 1 from rfl, show ((1 : Fin 2).val == 1) = true from rfl,
      show ((1 : Nat) == 1) = true from by decide,
      show ¬ (3 + mi < 3) by omega, if_false,
      show 3 + mi - 3 = mi by omega]
  all_goals rfl

/-- The cut's `XL` slice of slot `q`'s core is that core's `xl`. -/
theorem mvXl_slot (s : State) (c : Fin 2) :
    Core.slice (mvXl s) (2 * c.val) 2 = (s.cores[c.val]).xl := by
  rcases fin2_cases c with hc | hc
  · subst hc
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [slice_getLsbD (hj := hj)]
    simp only [mvXl]
    have hidx : 2 * (0 : Fin 2).val + j = j := by simp
    rw [BitVec.getLsbD_append, hidx]
    simp only [show (0 : Fin 2).val = 0 from rfl, show j < 2 by omega, if_true]
  · subst hc
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [slice_getLsbD (hj := hj)]
    simp only [mvXl]
    have hidx : 2 * (1 : Fin 2).val + j = 2 + j := by
      have h1 : (1 : Fin 2).val = 1 := rfl
      rw [h1]
    rw [BitVec.getLsbD_append, hidx]
    simp only [show (1 : Fin 2).val = 1 from rfl,
      show ¬ (2 + j < 2) by omega, if_false,
      show 2 + j - 2 = j by omega]
  all_goals rfl

/-- The cut's `XT` slice of slot `q`'s core is that core's `xt`. -/
theorem mvXt_slot (s : State) (c : Fin 2) :
    Core.slice (mvXt s) (3 * c.val) 3 = (s.cores[c.val]).xt := by
  rcases fin2_cases c with hc | hc
  · subst hc
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [slice_getLsbD (hj := hj)]
    simp only [mvXt]
    have hidx : 3 * (0 : Fin 2).val + j = j := by simp
    rw [BitVec.getLsbD_append, hidx]
    simp only [show (0 : Fin 2).val = 0 from rfl, show j < 3 by omega, if_true]
  · subst hc
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [slice_getLsbD (hj := hj)]
    simp only [mvXt]
    have hidx : 3 * (1 : Fin 2).val + j = 3 + j := by
      have h1 : (1 : Fin 2).val = 1 := rfl
      rw [h1]
    rw [BitVec.getLsbD_append, hidx]
    simp only [show (1 : Fin 2).val = 1 from rfl,
      show ¬ (3 + j < 3) by omega, if_false,
      show 3 + j - 3 = j by omega]
  all_goals rfl

/-- `moveVal`'s line is its core's `xl`. -/
theorem moveVal_line {ms cv p s c m} : (Bridge.Core.moveVal ms cv p s c m).line = s.xl.toNat :=
  rfl

/-- `moveVal`'s thread is its core's `xt`. -/
theorem moveVal_thread {ms cv p s c m} : (Bridge.Core.moveVal ms cv p s c m).thread = s.xt.toNat :=
  rfl

/-- The cross-model move bus agreement, plus the cut-side packing fields. -/
structure MoveBus (s : State) (m : Machine.State) (pin : Machine.PinIn) : Prop where
  /-- slot `q` is enabled on the cut iff the machine has a move there -/
  en : ∀ q, q < 6 → CoreCtl.bitAt (mvEn s pin) q = (machSlot m pin q).isSome
  /-- an enabled slot's destination word is the cut's `mvDst` slice -/
  dst : ∀ q, q < 6 → ∀ mv, machSlot m pin q = some mv →
    mv.dst = (Core.slice (mvDst s pin) (6 * q) 6).toNat
  /-- an enabled slot's data byte is the cut's `mvDat` slice -/
  dat : ∀ q, q < 6 → ∀ mv, machSlot m pin q = some mv →
    mv.v = (Core.slice (mvDat s pin) (8 * q) 8).toNat
  /-- an enabled slot's source code is the cut's `mvSrc` slice (needed by the
  `HOST.IN` read / `MEMHAZ` side) -/
  src : ∀ q, q < 6 → ∀ mv, machSlot m pin q = some mv →
    mv.src = (Core.slice (mvSrc s pin) (6 * q) 6).toNat
  /-- the slot's line is the cut's `XL` slice (a core register, `ChipRel`) -/
  line : ∀ q, q < 6 → (machMove s m pin q).line = (Core.slice (mvXl s) (2 * (q / 3)) 2).toNat
  /-- the slot's thread is the cut's `XT` slice (a core register, `ChipRel`) -/
  thread : ∀ q, q < 6 → (machMove s m pin q).thread =
    (Core.slice (mvXt s) (3 * (q / 3)) 3).toNat
  /-- the cut-side packing `mvGrp = DG_MAP mvDst` (`dgTable` of the slot's
  destination); see `WIRE_MOVEFABRIC_NOTES.md` -/
  grp : ∀ q, q < 6 →
    ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
      (mvXl s) (mvXt s)).get q).group =
      Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).dst)

/-- The machine's slot `3 * c + mi` is core `c`'s `moveAt mi`. -/
theorem machSlot_eq (s : State) (m : Machine.State) (pin : Machine.PinIn) (c : Fin 2) (mi : Nat)
    (hmi : mi < 3) (hfrz : m.dbg.frz = (coreIn s pin c.val).frz) :
    machSlot m pin (3 * c.val + mi) =
      Bridge.Core.moveAt (Machine.coreComb m (Machine.cfgView m.cfg)
        (Machine.pinView m.sync m.dbg) (Bridge.Core.coreNat (c.val == 1))
        (coreIn s pin c.val).frz) mi := by
  have hmod : (3 * c.val + mi) % 3 = mi := by omega
  have hco : coreOf (3 * c.val + mi) = c := by
    rcases fin2_cases c with h | h <;> subst h <;>
      (rcases (by omega : mi = 0 ∨ mi = 1 ∨ mi = 2) with rfl | rfl | rfl) <;> rfl
  have hcb : mCoreComb m pin c = Machine.coreComb m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (Bridge.Core.coreNat (c.val == 1))
      (coreIn s pin c.val).frz := by
    simp only [mCoreComb, hfrz, coreNat_fin2]
  show Bridge.Core.moveAt (mCoreComb m pin (coreOf (3 * c.val + mi)))
    ((3 * c.val + mi) % 3) = _
  rw [hco, hmod, hcb]

/-- A slot index `q < 6` splits into `3 * c + mi`. -/
theorem slot_split (q : Nat) (hq : q < 6) :
    ∃ (c : Fin 2) (mi : Nat), mi < 3 ∧ 3 * c.val + mi = q := by
  by_cases h : q < 3
  · refine ⟨0, q, by omega, ?_⟩
    simp
  · refine ⟨1, q - 3, by omega, ?_⟩
    simp
    omega

/-- The move bus, from `Bridge.Core.Rel` for the cut's `sIr` plus `ChipRel`
(the `line`/`thread` slots read the core registers). -/
theorem moveBus_of_rel (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m)
    (hcore : ∀ c : Fin 2, Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (sIr s m c) (coreIn s pin c.val))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst)) :
    MoveBus s m pin := by
  have hfrz : ∀ c : Fin 2, m.dbg.frz = (coreIn s pin c.val).frz := by
    intro c
    rw [hrel.dbg.2.1]
    simp [coreIn]
  have hcngr : ∀ (c : Fin 2) (mi : Nat),
      (Core.bitOf (Core.out (c.val == 1) (sIr s m c) (coreIn s pin c.val)).mvEn mi =
        Core.bitOf (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).mvEn mi) ∧
      (Core.bitOf (Core.out (c.val == 1) (sIr s m c) (coreIn s pin c.val)).mvEn mi = true →
        Core.slice (Core.out (c.val == 1) (sIr s m c) (coreIn s pin c.val)).mvDst (6 * mi) 6 =
          Core.slice (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).mvDst
            (6 * mi) 6 ∧
        Core.slice (Core.out (c.val == 1) (sIr s m c) (coreIn s pin c.val)).mvData (8 * mi) 8 =
          Core.slice (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).mvData
            (8 * mi) 8) := by
    intro c mi
    exact out_move_congr (c := (c.val == 1)) (s1 := sIr s m c) (s2 := s.cores[c.val])
      (i := coreIn s pin c.val) mi rfl (fun hx => (hrel.cores c).2.1 hx) rfl
  have hcngS : ∀ (c : Fin 2) (mi : Nat),
      (Core.bitOf (Core.out (c.val == 1) (sIr s m c) (coreIn s pin c.val)).mvEn mi =
        Core.bitOf (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).mvEn mi) ∧
      (Core.bitOf (Core.out (c.val == 1) (sIr s m c) (coreIn s pin c.val)).mvEn mi = true →
        Core.slice (Core.out (c.val == 1) (sIr s m c) (coreIn s pin c.val)).mvSrc (6 * mi) 6 =
          Core.slice (Core.out (c.val == 1) (s.cores[c.val]) (coreIn s pin c.val)).mvSrc
            (6 * mi) 6) := by
    intro c mi
    exact out_src_congr (c := (c.val == 1)) (s1 := sIr s m c) (s2 := s.cores[c.val])
      (i := coreIn s pin c.val) mi rfl (fun hx => (hrel.cores c).2.1 hx) rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hgrp⟩
  · intro q hq
    obtain ⟨c, mi, hmi, hqeq⟩ := slot_split q hq
    subst hqeq
    rw [mvEn_slot s pin c mi hmi, machSlot_eq s m pin c mi hmi (hfrz c)]
    exact (hcngr c mi).1.symm.trans
      (Bridge.Core.moves_bridge (c := (c.val == 1)) (hcore c) mi hmi).1
  · intro q hq mv hmv
    obtain ⟨c, mi, hmi, hqeq⟩ := slot_split q hq
    subst hqeq
    rw [machSlot_eq s m pin c mi hmi (hfrz c)] at hmv
    have hb := Bridge.Core.moves_bridge (c := (c.val == 1)) (hcore c) mi hmi
    have hen : Core.bitOf (Core.out (c.val == 1) (sIr s m c) (coreIn s pin c.val)).mvEn mi
        = true := by
      rw [hb.1, hmv]
      rfl
    have hs := (hcngr c mi).2 hen
    have hdst : mv.dst = (Core.slice (Core.out (c.val == 1) (sIr s m c)
        (coreIn s pin c.val)).mvDst (6 * mi) 6).toNat := (hb.2.2.1 mv hmv).2.2.1
    rw [hdst, mvDst_slot s pin c mi hmi]
    exact congrArg BitVec.toNat hs.1
  · intro q hq mv hmv
    obtain ⟨c, mi, hmi, hqeq⟩ := slot_split q hq
    subst hqeq
    rw [machSlot_eq s m pin c mi hmi (hfrz c)] at hmv
    have hb := Bridge.Core.moves_bridge (c := (c.val == 1)) (hcore c) mi hmi
    have hen : Core.bitOf (Core.out (c.val == 1) (sIr s m c) (coreIn s pin c.val)).mvEn mi
        = true := by
      rw [hb.1, hmv]
      rfl
    have hs := (hcngr c mi).2 hen
    have hdat : mv.v = (Core.slice (Core.out (c.val == 1) (sIr s m c)
        (coreIn s pin c.val)).mvData (8 * mi) 8).toNat := (hb.2.2.1 mv hmv).2.2.2
    rw [hdat, mvDat_slot s pin c mi hmi]
    exact congrArg BitVec.toNat hs.2
  · intro q hq mv hmv
    obtain ⟨c, mi, hmi, hqeq⟩ := slot_split q hq
    subst hqeq
    rw [machSlot_eq s m pin c mi hmi (hfrz c)] at hmv
    have hb := Bridge.Core.moves_bridge (c := (c.val == 1)) (hcore c) mi hmi
    have hen : Core.bitOf (Core.out (c.val == 1) (sIr s m c) (coreIn s pin c.val)).mvEn mi
        = true := by
      rw [hb.1, hmv]
      rfl
    have hs := (hcngS c mi).2 hen
    have hsrc : mv.src = (Core.slice (Core.out (c.val == 1) (sIr s m c)
        (coreIn s pin c.val)).mvSrc (6 * mi) 6).toNat := (hb.2.2.1 mv hmv).2.1
    rw [hsrc, mvSrc_slot s pin c mi hmi]
    exact congrArg BitVec.toNat hs
  · intro q hq
    obtain ⟨c, mi, hmi, hqeq⟩ := slot_split q hq
    subst hqeq
    have hq3 : (3 * c.val + mi) / 3 = c.val := by omega
    rw [hq3]
    by_cases hmv : machSlot m pin (3 * c.val + mi) = none
    · rw [machMove_of_none hmv]
      have hco : coreOf (3 * c.val + mi) = c := by
        rcases fin2_cases c with h | h <;> subst h <;>
          (rcases (by omega : mi = 0 ∨ mi = 1 ∨ mi = 2) with rfl | rfl | rfl) <;> rfl
      have hmod : (3 * c.val + mi) % 3 = mi := by omega
      rw [hco, hmod, mvXl_slot]
      simp only [machNull, moveVal_line]
    · obtain ⟨mv, hmv0⟩ : ∃ mv, machSlot m pin (3 * c.val + mi) = some mv := by
        cases h : machSlot m pin (3 * c.val + mi) with
        | none => exact absurd h hmv
        | some mv => exact ⟨mv, rfl⟩
      have hmv1 : Bridge.Core.moveAt (Machine.coreComb m (Machine.cfgView m.cfg)
          (Machine.pinView m.sync m.dbg) (Bridge.Core.coreNat (c.val == 1))
          (coreIn s pin c.val).frz) mi = some mv := by
        rw [← machSlot_eq s m pin c mi hmi (hfrz c)]
        exact hmv0
      have hxa : Core.xa (sIr s m c) (coreIn s pin c.val) = true := by
        by_cases h : Core.xa (sIr s m c) (coreIn s pin c.val) = true
        · exact h
        · have hf : Core.xa (sIr s m c) (coreIn s pin c.val) = false := by simpa using h
          unfold Bridge.Core.moveAt at hmv1
          rw [Bridge.Core.coreComb_moves_of_idle (hcore c) hf] at hmv1
          exact absurd hmv1 (by simp)
      have hval : mv = Bridge.Core.moveVal m (Machine.cfgView m.cfg)
          (Machine.pinView m.sync m.dbg) (sIr s m c) (Bridge.Core.coreNat (c.val == 1)) mi := by
        have h1 : Bridge.Core.moveAt (Machine.coreComb m (Machine.cfgView m.cfg)
            (Machine.pinView m.sync m.dbg) (Bridge.Core.coreNat (c.val == 1))
            (coreIn s pin c.val).frz) mi =
            Bridge.Core.moveCand m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
              (sIr s m c) (Bridge.Core.coreNat (c.val == 1)) mi :=
          Bridge.Core.moveAt_eq_cand (hcore c) hxa mi hmi
        rw [h1] at hmv1
        exact Bridge.Core.moveCand_eq_some hmv1
      rw [machMove_of_some hmv0, hval, moveVal_line, mvXl_slot]
      rfl
  · intro q hq
    obtain ⟨c, mi, hmi, hqeq⟩ := slot_split q hq
    subst hqeq
    have hq3 : (3 * c.val + mi) / 3 = c.val := by omega
    rw [hq3]
    by_cases hmv : machSlot m pin (3 * c.val + mi) = none
    · rw [machMove_of_none hmv]
      have hco : coreOf (3 * c.val + mi) = c := by
        rcases fin2_cases c with h | h <;> subst h <;>
          (rcases (by omega : mi = 0 ∨ mi = 1 ∨ mi = 2) with rfl | rfl | rfl) <;> rfl
      have hmod : (3 * c.val + mi) % 3 = mi := by omega
      rw [hco, hmod, mvXt_slot]
      simp only [machNull, moveVal_thread]
    · obtain ⟨mv, hmv0⟩ : ∃ mv, machSlot m pin (3 * c.val + mi) = some mv := by
        cases h : machSlot m pin (3 * c.val + mi) with
        | none => exact absurd h hmv
        | some mv => exact ⟨mv, rfl⟩
      have hmv1 : Bridge.Core.moveAt (Machine.coreComb m (Machine.cfgView m.cfg)
          (Machine.pinView m.sync m.dbg) (Bridge.Core.coreNat (c.val == 1))
          (coreIn s pin c.val).frz) mi = some mv := by
        rw [← machSlot_eq s m pin c mi hmi (hfrz c)]
        exact hmv0
      have hxa : Core.xa (sIr s m c) (coreIn s pin c.val) = true := by
        by_cases h : Core.xa (sIr s m c) (coreIn s pin c.val) = true
        · exact h
        · have hf : Core.xa (sIr s m c) (coreIn s pin c.val) = false := by simpa using h
          unfold Bridge.Core.moveAt at hmv1
          rw [Bridge.Core.coreComb_moves_of_idle (hcore c) hf] at hmv1
          exact absurd hmv1 (by simp)
      have hval : mv = Bridge.Core.moveVal m (Machine.cfgView m.cfg)
          (Machine.pinView m.sync m.dbg) (sIr s m c) (Bridge.Core.coreNat (c.val == 1)) mi := by
        have h1 : Bridge.Core.moveAt (Machine.coreComb m (Machine.cfgView m.cfg)
            (Machine.pinView m.sync m.dbg) (Bridge.Core.coreNat (c.val == 1))
            (coreIn s pin c.val).frz) mi =
            Bridge.Core.moveCand m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
              (sIr s m c) (Bridge.Core.coreNat (c.val == 1)) mi :=
          Bridge.Core.moveAt_eq_cand (hcore c) hxa mi hmi
        rw [h1] at hmv1
        exact Bridge.Core.moveCand_eq_some hmv1
      rw [machMove_of_some hmv0, hval, moveVal_thread, mvXt_slot]
      rfl

/-! ## 5. Two byte-width witnesses (`WireAgree.sym` / `WireAgree.ctl`)

`LineThread.WireAgree.sym` compares the machine's `SymWrite` record with the
cut's: `ltLineIn`'s `v` is the winning move's **whole** data byte, while
`Wire.lineIn.symD` is `BitVec.truncate 4` of the picked word (the low nibble).
`WireAgree.ctl` has the same shape (`ctlD` is `BitVec.ofNat 3` of the data byte).
Both consumption sites use only those bits (`Machine.stagedNext`'s `bv 4 v`,
`Machine.lineNext`'s `nbit v 0/1/2`), so the fields are stronger than the RTL
needs: they fail on every cycle whose winning `L.SYM`/`Lk.CTL` data byte has high
bits set.  The kernel-checked separations below are the numeric core of that
finding; a full reachable-state witness would have to exhibit a `ChipRel` state
with such a winner (not constructed here). -/

/-- The machine's symbol data byte 255 is not the cut's 4-bit truncation. -/
theorem sym_data_witness : (255 : Nat) ≠ (BitVec.truncate 4 (255 : BitVec 8)).toNat := by
  decide

/-- The machine's control data byte 255 is not the cut's 3-bit truncation. -/
theorem ctl_data_witness : (255 : Nat) ≠ (BitVec.ofNat 3 (255 : Nat)).toNat := by
  decide


/-! ## 6. `MoveAgree` and `MoveTable` for `bundleOf` -/

/-- **The move bus from `ChipRel` + `Inv` + the core-input bus.**  The only
remaining cross-component input besides `ChipRel`/`Inv` is `CoreInputBus` (the
`cores` task's single open wiring obligation, `DISCHARGE_COREUNITS_NOTES` §2) and
the cut-side packing identity `hgrp` (`WIRE_MOVEFABRIC_NOTES` §4). -/
theorem moveBus_of_chipRel (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst)) :
    MoveBus s m pin :=
  moveBus_of_rel s m pin hrel (fun c => rel_of_bus s m pin c hrel hinv (hbus c)) hgrp

/-- **The machine's own move list resolves like the padded six slots**, from
`ChipRel` + `Inv` + the core-input bus. -/
theorem resolveMoves_mAllMoves_of_chipRel (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hkind : Bridge.Moves.DstKindTable) :
    Machine.resolveMoves (mAllMoves m pin) =
      Machine.resolveMoves (Bridge.Moves.six (machMove s m pin)) :=
  resolveMoves_mAllMoves s m pin hkind
    (fun c => rel_of_bus s m pin c hrel hinv (hbus c))
    (fun c => by rw [hrel.dbg.2.1]; simp [coreIn])

/-- `mWs` is the padded six-slot resolution's winner list. -/
theorem mWs_eq_six (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hkind : Bridge.Moves.DstKindTable)
    (h : ∀ c : Fin 2, Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (sIr s m c) (coreIn s pin c.val))
    (hfrz : ∀ c : Fin 2, m.dbg.frz = (coreIn s pin c.val).frz) :
    mWs m pin = (Machine.resolveMoves (Bridge.Moves.six (machMove s m pin))).1 := by
  show (Machine.resolveMoves (mAllMoves m pin)).1 = _
  rw [resolveMoves_mAllMoves s m pin hkind h hfrz]

/-- `(bundleOf …).get k`'s fields are the buses' `k`-th slices. -/
theorem bundle_en (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) (dat : BitVec 48)
    (xl : BitVec 4) (xt : BitVec 6) (k : Nat) (hk : k < 6) :
    ((Moves.bundleOf en grp dst dat xl xt).get k).enabled = CoreCtl.bitAt en k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem bundle_dst (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) (dat : BitVec 48)
    (xl : BitVec 4) (xt : BitVec 6) (k : Nat) (hk : k < 6) :
    ((Moves.bundleOf en grp dst dat xl xt).get k).dst = CoreCtl.slice dst (6 * k) 6 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem bundle_data (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) (dat : BitVec 48)
    (xl : BitVec 4) (xt : BitVec 6) (k : Nat) (hk : k < 6) :
    ((Moves.bundleOf en grp dst dat xl xt).get k).data = CoreCtl.slice dat (8 * k) 8 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem bundle_line (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) (dat : BitVec 48)
    (xl : BitVec 4) (xt : BitVec 6) (k : Nat) (hk : k < 6) :
    ((Moves.bundleOf en grp dst dat xl xt).get k).line = CoreCtl.slice xl (2 * (k / 3)) 2 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem bundle_thread (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) (dat : BitVec 48)
    (xl : BitVec 4) (xt : BitVec 6) (k : Nat) (hk : k < 6) :
    ((Moves.bundleOf en grp dst dat xl xt).get k).thread = CoreCtl.slice xt (3 * (k / 3)) 3 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **`MoveAgree` for the padded six slots**, from the move bus. -/
theorem moveAgree_of_bus (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) :
    Bridge.Moves.MoveAgree (Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin)
      (mvDat s pin) (mvXl s) (mvXt s)) (machMove s m pin) where
  dst := by
    intro k hk hen
    have hbit : CoreCtl.bitAt (mvEn s pin) k = true := by
      rw [bundle_en _ _ _ _ _ _ k hk] at hen
      exact hen
    have hs : (machSlot m pin k).isSome = true := by
      rw [← hbus.en k hk]
      exact hbit
    obtain ⟨mv, hmv⟩ : ∃ mv, machSlot m pin k = some mv := by
      cases h : machSlot m pin k with
      | none => rw [h] at hs; exact absurd hs (by simp)
      | some mv => exact ⟨mv, rfl⟩
    rw [bundle_dst _ _ _ _ _ _ k hk, machMove_of_some hmv]
    exact hbus.dst k hk mv hmv
  pad := by
    intro k hk hen
    have hbit : CoreCtl.bitAt (mvEn s pin) k = false := by
      rw [bundle_en _ _ _ _ _ _ k hk] at hen
      exact hen
    have hs : (machSlot m pin k).isSome = false := by
      rw [← hbus.en k hk]
      exact hbit
    have hn : machSlot m pin k = none := by
      cases h : machSlot m pin k with
      | none => rfl
      | some mv => rw [h] at hs; exact absurd hs (by simp)
    rw [machMove_of_none hn]
    rfl
  grp := fun k hk => hbus.grp k hk
  line := by
    intro k hk
    rw [bundle_line _ _ _ _ _ _ k hk]
    exact hbus.line k hk
  thread := by
    intro k hk
    rw [bundle_thread _ _ _ _ _ _ k hk]
    exact hbus.thread k hk

/-- **`MoveTable` for the padded six slots.** -/
theorem moveTable_of_bus (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hkind : Bridge.Moves.DstKindTable) (hbus : MoveBus s m pin) :
    Bridge.Moves.MoveTable (Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin)
      (mvDat s pin) (mvXl s) (mvXt s)) (Bridge.Moves.six (machMove s m pin)) :=
  Bridge.Moves.moveTable_of_agree hkind _ _ (moveAgree_of_bus s m pin hbus)

/-- **The machine's winners and conflict on the cut's bundle**: the machine's
resolved list is the cut's `winAt` filter, and its conflict flag is the cut's
`conflictEv`. -/
theorem winners_machMove (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hkind : Bridge.Moves.DstKindTable) (hbus : MoveBus s m pin) :
    (Machine.resolveMoves (Bridge.Moves.six (machMove s m pin))).1 =
      (List.range 6).filterMap (fun k =>
        if Moves.winAt (Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)) k then some (machMove s m pin k) else none) ∧
    (Machine.resolveMoves (Bridge.Moves.six (machMove s m pin))).2 =
      Moves.conflictEv (Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)) := by
  have hMT := moveTable_of_bus s m pin hkind hbus
  exact ⟨Bridge.Moves.resolveMoves_winners hMT, Bridge.Moves.resolveMoves_conflict hMT⟩

/-! ## 7. The `Glue` control move-fabric field `conflict`

`ctrlInTrue`'s `conflict` is the machine's own `resolveMoves` flag on `mAllMoves`,
so it is the cut's `conflictOf` once the machine's list is identified with the
padded six slots.  The only extra ingredient is that `conflictEv` reads just the
`enabled`/`group`/`line`/`thread` projections of a bundle, so `arbBundle` (no
destination/data) and the real bundle agree. -/

/-- `conflictEv` does not read the destination or the data bytes. -/
theorem conflictEv_bundleOf (en : BitVec 6) (grp : BitVec 30) (xl : BitVec 4) (xt : BitVec 6)
    (d d' : BitVec 36) (a a' : BitVec 48) :
    Moves.conflictEv (Moves.bundleOf en grp d a xl xt) =
      Moves.conflictEv (Moves.bundleOf en grp d' a' xl xt) := by
  simp only [Moves.conflictEv, Moves.winAt, Moves.validAt, Moves.blocked, Moves.sameKey,
    show List.range 6 = [0, 1, 2, 3, 4, 5] from by decide,
    show List.range 5 = [0, 1, 2, 3, 4] from by decide,
    show List.range 4 = [0, 1, 2, 3] from by decide,
    show List.range 3 = [0, 1, 2] from by decide,
    show List.range 2 = [0, 1] from by decide,
    show List.range 1 = [0] from by decide,
    List.range_zero, List.any_cons, List.any_nil, Moves.bundleOf, Moves.Bundle.get]

/-- **The `Glue` `CtrlMoveFabric.conflict` field.** -/
theorem ctrlMoveFabric_conflict (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hkind : Bridge.Moves.DstKindTable)
    (hcore : ∀ c : Fin 2, Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (sIr s m c) (coreIn s pin c.val))
    (hfrz : ∀ c : Fin 2, m.dbg.frz = (coreIn s pin c.val).frz)
    (hbus : MoveBus s m pin) :
    (ctrlInTrue m pin).conflict =
      Moves.conflictOf (mvEn s pin) (mvGrp s pin) (mvXl s) (mvXt s) := by
  have hMT := moveTable_of_bus s m pin hkind hbus
  show (Machine.resolveMoves (mAllMoves m pin)).2 =
    Moves.conflictOf (mvEn s pin) (mvGrp s pin) (mvXl s) (mvXt s)
  rw [resolveMoves_mAllMoves s m pin hkind hcore hfrz,
    Bridge.Moves.resolveMoves_conflict hMT]
  exact (conflictEv_bundleOf (mvEn s pin) (mvGrp s pin) (mvXl s) (mvXt s)
    (d := mvDst s pin) (d' := 0) (a := mvDat s pin) (a' := 0)).symm

/-- **The same from `ChipRel` + `Inv` + the core-input bus.** -/
theorem ctrlMoveFabric_conflict_of_chipRel (s : State) (m : Machine.State)
    (pin : Machine.PinIn) (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable) :
    (ctrlInTrue m pin).conflict =
      Moves.conflictOf (mvEn s pin) (mvGrp s pin) (mvXl s) (mvXt s) :=
  ctrlMoveFabric_conflict s m pin hkind
    (fun c => rel_of_bus s m pin c hrel hinv (hbus c))
    (fun c => by rw [hrel.dbg.2.1]; simp [coreIn])
    (moveBus_of_chipRel s m pin hrel hinv hJGTab hbus hgrp)
/-! ## 9. The group pick: the machine's scan is the cut's `pickWord`

`mUnitsIn`, `ctrlInTrue`, `ltLineIn`, `streamIn` and `mhcP0Move` all scan the
resolved winners with a `dstOp`-based pattern.  The lemmas below turn such a scan
into the cut's `Moves.pickWord` of the destination's write group: the machine's
first winner in a real group is the cut's lowest contender, and its
`{we, dst, data}` word is the group's pick.  (The argument does not use the
non-keyed restriction: the *lowest* hit always wins, because everything that could
block it would itself be a hit.  The per-line / per-thread variants of §10 refine
the scan by `mv.line`/`mv.thread`.) -/

/-- The cut's six-slot move bundle of the cycle. -/
abbrev movBundle (s : State) (pin : Machine.PinIn) : Moves.Bundle :=
  Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin) (mvXl s) (mvXt s)

/-- Slot `q`'s destination word as a `Core.slice`. -/
theorem movBundle_dst (s : State) (pin : Machine.PinIn) (q : Nat) (hq : q < 6) :
    ((movBundle s pin).get q).dst = Core.slice (mvDst s pin) (6 * q) 6 :=
  bundle_dst (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin) (mvXl s) (mvXt s) q hq

/-- Slot `q`'s data byte as a `Core.slice`. -/
theorem movBundle_data (s : State) (pin : Machine.PinIn) (q : Nat) (hq : q < 6) :
    ((movBundle s pin).get q).data = Core.slice (mvDat s pin) (8 * q) 8 :=
  bundle_data (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin) (mvXl s) (mvXt s) q hq

/-- `(if c then some a else none).bind g` is the guarded `g`. -/
theorem bind_ite {β γ : Type} (c : Bool) (a : Option β) (g : β → Option γ) :
    (if c then a else none).bind g = if c then a.bind g else none := by
  cases c <;> rfl

/-- A `filterMap` scan is the scan of the winners: the machine's `findSome?` over
its winner list is the `findSome?` over the six slots. -/
theorem scan_rewrite {α γ : Type} (l : List α) (c : α → Bool) (mv : α → Machine.Move)
    (g : Machine.Move → Option γ) :
    (l.filterMap (fun k => if c k then some (mv k) else none)).findSome? g =
      l.findSome? (fun k => if c k then g (mv k) else none) := by
  rw [← List.head?_filterMap, List.filterMap_filterMap]
  simp only [bind_ite, Option.bind_some]
  rw [List.head?_filterMap]

/-- `findSome?` is `none` when every entry is `none`. -/
theorem findSome?_eq_none {α β : Type} {h : α → Option β} :
    ∀ (l : List α), (∀ a ∈ l, h a = none) → l.findSome? h = none
  | [], _ => rfl
  | a :: as, hall => by
    rw [List.findSome?_cons, hall a (by simp)]
    exact findSome?_eq_none as (fun b hb => hall b (by simp [hb]))

/-- `findSome?` is `some e` when the first hit of `range 6` is at `k`. -/
theorem findSome_range_six {β : Type} (h : Nat → Option β) {k : Nat} (hk : k < 6) {e : β}
    (hat : h k = some e) (hbefore : ∀ j, j < k → h j = none) :
    (List.range 6).findSome? h = some e := by
  have h6 : List.range 6 = [0, 1, 2, 3, 4, 5] := by decide
  rw [h6]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [List.findSome?_cons, hat]
  · simp only [List.findSome?_cons, hbefore 0 (by omega), hat]
  · simp only [List.findSome?_cons, hbefore 0 (by omega), hbefore 1 (by omega), hat]
  · simp only [List.findSome?_cons, hbefore 0 (by omega), hbefore 1 (by omega),
      hbefore 2 (by omega), hat]
  · simp only [List.findSome?_cons, hbefore 0 (by omega), hbefore 1 (by omega),
      hbefore 2 (by omega), hbefore 3 (by omega), hat]
  · simp only [List.findSome?_cons, hbefore 0 (by omega), hbefore 1 (by omega),
      hbefore 2 (by omega), hbefore 3 (by omega), hbefore 4 (by omega), hat]

/-- The machine's slot `q` has a move exactly when the cut's slot is enabled. -/
theorem machSlot_isSome (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (q : Nat) (hq : q < 6) :
    (machSlot m pin q).isSome = ((movBundle s pin).get q).enabled := by
  rw [← hbus.en q hq, bundle_en _ _ _ _ _ _ q hq]

/-- An enabled slot's move carries the cut's destination code. -/
theorem machMove_dst (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (q : Nat) (hq : q < 6)
    (h : ((movBundle s pin).get q).enabled = true) :
    (machMove s m pin q).dst = ((movBundle s pin).get q).dst.toNat := by
  have hs : (machSlot m pin q).isSome = true := by rw [machSlot_isSome s m pin hbus q hq, h]
  obtain ⟨mv, hmv⟩ : ∃ mv, machSlot m pin q = some mv := by
    cases hh : machSlot m pin q with
    | none => rw [hh] at hs; exact absurd hs (by simp)
    | some mv => exact ⟨mv, rfl⟩
  rw [machMove_of_some hmv, hbus.dst q hq mv hmv, movBundle_dst s pin q hq]

/-- An enabled slot's move carries the cut's data byte. -/
theorem machMove_data (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (q : Nat) (hq : q < 6)
    (h : ((movBundle s pin).get q).enabled = true) :
    (machMove s m pin q).v = ((movBundle s pin).get q).data.toNat := by
  have hs : (machSlot m pin q).isSome = true := by rw [machSlot_isSome s m pin hbus q hq, h]
  obtain ⟨mv, hmv⟩ : ∃ mv, machSlot m pin q = some mv := by
    cases hh : machSlot m pin q with
    | none => rw [hh] at hs; exact absurd hs (by simp)
    | some mv => exact ⟨mv, rfl⟩
  rw [machMove_of_some hmv, hbus.dat q hq mv hmv, movBundle_data s pin q hq]

/-- A slot the cut leaves disabled has the `NULL` destination `0` in the machine. -/
theorem machMove_dst_null (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (q : Nat) (hq : q < 6)
    (h : ((movBundle s pin).get q).enabled = false) :
    (machMove s m pin q).dst = 0 := by
  have hs : (machSlot m pin q).isSome = false := by
    rw [machSlot_isSome s m pin hbus q hq, h]
  have hn : machSlot m pin q = none := by
    cases hh : machSlot m pin q with
    | none => rfl
    | some mv => rw [hh] at hs; exact absurd hs (by simp)
  rw [machMove_of_none hn]
  rfl

/-- `hitAt` is "valid and in group `G`" on the cut's bundle. -/
theorem hitAt_bundle (s : State) (pin : Machine.PinIn) (G : BitVec 5)
    (hGn : (G == Moves.dgNone) = false) (q : Nat) (hq : q < 6) :
    Moves.hitAt (mvEn s pin) (mvGrp s pin) G q =
      (Moves.validAt ((movBundle s pin).get q) && (((movBundle s pin).get q).group == G)) :=
  Bridge.Moves.hitAt_eq_valid_group _ _ _ _ _ _ G hGn q hq

/-- A hit slot is enabled and in the group. -/
theorem hit_enabled (s : State) (pin : Machine.PinIn) (G : BitVec 5)
    (hGn : (G == Moves.dgNone) = false) (q : Nat) (hq : q < 6)
    (h : Moves.hitAt (mvEn s pin) (mvGrp s pin) G q = true) :
    ((movBundle s pin).get q).enabled = true ∧ (((movBundle s pin).get q).group == G) = true := by
  rw [hitAt_bundle s pin G hGn q hq, Bool.and_eq_true] at h
  obtain ⟨hv, hg⟩ := h
  rw [Moves.validAt, Bool.and_eq_true] at hv
  exact ⟨hv.1, hg⟩
/-- The machine's slot `q`'s group code is the cut's group, when the slot has a move. -/
theorem dgTable_machMove (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (q : Nat) (hq : q < 6)
    (h : ((movBundle s pin).get q).enabled = true) :
    Moves.dgTable (BitVec.ofNat 6 (machMove s m pin q).dst) = ((movBundle s pin).get q).group := by
  rw [machMove_dst s m pin hbus q hq h, Bridge.Moves.ofNat_toNat_6]
  exact (hbus.grp q hq).symm

/-- A hit slot's `P` is the cut's `Q` of the slot's destination. -/
theorem P_hit_true (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (G : BitVec 5) (hGn : (G == Moves.dgNone) = false)
    {α : Type} (P : Machine.DstOp → Option α) (Q : BitVec 6 → Option α)
    (hPQ : ∀ d, d < 64 → P (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == G) then Q (BitVec.ofNat 6 d) else none))
    (q : Nat) (hq : q < 6) (h : Moves.hitAt (mvEn s pin) (mvGrp s pin) G q = true) :
    P (Machine.dstOp (machMove s m pin q).dst) = Q ((movBundle s pin).get q).dst := by
  obtain ⟨hen, hgrp⟩ := hit_enabled s pin G hGn q hq h
  have hd : (machMove s m pin q).dst = ((movBundle s pin).get q).dst.toNat :=
    machMove_dst s m pin hbus q hq hen
  have hlt : ((movBundle s pin).get q).dst.toNat < 64 := by
    simpa using ((movBundle s pin).get q).dst.isLt
  have hh := hPQ ((movBundle s pin).get q).dst.toNat hlt
  rw [Bridge.Moves.ofNat_toNat_6, ← hbus.grp q hq, hgrp] at hh
  rw [hd]
  simpa using hh

/-- A non-hit slot's `P` is `none`. -/
theorem P_hit_false (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (G : BitVec 5) (hGn : (G == Moves.dgNone) = false)
    {α : Type} (P : Machine.DstOp → Option α) (Q : BitVec 6 → Option α)
    (hPQ : ∀ d, d < 64 → P (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == G) then Q (BitVec.ofNat 6 d) else none))
    (q : Nat) (hq : q < 6) (h : Moves.hitAt (mvEn s pin) (mvGrp s pin) G q = false) :
    P (Machine.dstOp (machMove s m pin q).dst) = none := by
  by_cases hen : ((movBundle s pin).get q).enabled = true
  · have hd : (machMove s m pin q).dst = ((movBundle s pin).get q).dst.toNat :=
      machMove_dst s m pin hbus q hq hen
    have hlt : ((movBundle s pin).get q).dst.toNat < 64 := by
      simpa using ((movBundle s pin).get q).dst.isLt
    have hg : (((movBundle s pin).get q).group == G) = false := by
      rw [hitAt_bundle s pin G hGn q hq] at h
      cases hb : (((movBundle s pin).get q).group == G) with
      | false => rfl
      | true =>
        exfalso
        have hgEq : ((movBundle s pin).get q).group = G := by simpa using hb
        rw [Moves.validAt, hen, Bool.true_and, hgEq, hGn] at h
        simp at h
    have hh := hPQ ((movBundle s pin).get q).dst.toNat hlt
    rw [Bridge.Moves.ofNat_toNat_6, ← hbus.grp q hq] at hh
    rw [show (((movBundle s pin).get q).group == G) = false from hg] at hh
    rw [hd]
    simpa using hh
  · have hnf : ((movBundle s pin).get q).enabled = false := by simpa using hen
    have hz := machMove_dst_null s m pin hbus q hq hnf
    have hh := hPQ 0 (by omega)
    have hg0 : (Moves.dgTable (BitVec.ofNat 6 0) == G) = false := by
      rw [show (BitVec.ofNat 6 0 : BitVec 6) = 0 from rfl, Moves.dgTable_null,
        Moves.beq_comm_5]
      exact hGn
    rw [hg0] at hh
    rw [hz]
    simpa using hh

/-- The lowest hit of a real group wins the machine's resolution. -/
theorem winAt_of_hits (s : State) (pin : Machine.PinIn) (G : BitVec 5)
    (hGn : (G == Moves.dgNone) = false) (k : Nat) (hk : k < 6)
    (hbefore : ∀ j, j < k → Moves.hitAt (mvEn s pin) (mvGrp s pin) G j = false)
    (hhit : Moves.hitAt (mvEn s pin) (mvGrp s pin) G k = true) :
    Moves.winAt (movBundle s pin) k = true := by
  obtain ⟨hen, hgrp⟩ := hit_enabled s pin G hGn k hk hhit
  refine Moves.win_of_first _ G k ?_ hgrp hen ?_
  · simpa using hGn
  · intro j hj
    have hj6 : j < 6 := by omega
    have h := hbefore j hj
    rw [hitAt_bundle s pin G hGn j hj6] at h
    rw [Bridge.Moves.contender_eq_valid_group _ G hGn]
    exact h

/-- The scan value at a winning hit slot. -/
theorem scan_at_hit (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (G : BitVec 5) (hGn : (G == Moves.dgNone) = false)
    {α : Type} (P : Machine.DstOp → Option α) (Q : BitVec 6 → Option α)
    (hPQ : ∀ d, d < 64 → P (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == G) then Q (BitVec.ofNat 6 d) else none))
    (q : Nat) (hq : q < 6) (hhit : Moves.hitAt (mvEn s pin) (mvGrp s pin) G q = true)
    (hwin : Moves.winAt (movBundle s pin) q = true) :
    (if Moves.winAt (movBundle s pin) q then
        (P (Machine.dstOp (machMove s m pin q).dst)).map
          (fun a => (a, (machMove s m pin q).v)) else none)
      = (Q ((movBundle s pin).get q).dst).map
        (fun a => (a, ((movBundle s pin).get q).data.toNat)) := by
  obtain ⟨hen, _⟩ := hit_enabled s pin G hGn q hq hhit
  have hp := P_hit_true s m pin hbus G hGn P Q hPQ q hq hhit
  have hd := machMove_data s m pin hbus q hq hen
  rw [if_pos hwin, hp, hd]

/-- A pair scan under a data transform, as the transform of the untransformed scan. -/
theorem pair_map_T {α : Type} {β : Type} (o : Option α) (v : Nat) (T : Nat → β) :
    (o.map (fun a => (a, v))).map (fun p : α × Nat => (p.1, T p.2)) =
      o.map (fun a => (a, T v)) := by
  cases o <;> rfl

/-- The scan value at a non-hit slot is `none`. -/
theorem scan_at_no_hit (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (G : BitVec 5) (hGn : (G == Moves.dgNone) = false)
    {α : Type} (P : Machine.DstOp → Option α) (Q : BitVec 6 → Option α)
    (hPQ : ∀ d, d < 64 → P (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == G) then Q (BitVec.ofNat 6 d) else none))
    (q : Nat) (hq : q < 6) (h : Moves.hitAt (mvEn s pin) (mvGrp s pin) G q = false) :
    (if Moves.winAt (movBundle s pin) q then
        (P (Machine.dstOp (machMove s m pin q).dst)).map
          (fun a => (a, (machMove s m pin q).v)) else none) = none := by
  rw [P_hit_false s m pin hbus G hGn P Q hPQ q hq h]
  cases Moves.winAt (movBundle s pin) q <;> rfl

/-- A slot scan with a data transform `T` is the untransformed scan, transformed. -/
theorem scan_T (s : State) (m : Machine.State) (pin : Machine.PinIn)
    {α : Type} {β : Type} (P : Machine.DstOp → Option α) (T : Nat → β) (q : Nat) :
    (if Moves.winAt (movBundle s pin) q then
        (P (Machine.dstOp (machMove s m pin q).dst)).map
          (fun a => (a, T (machMove s m pin q).v)) else none)
      = ((if Moves.winAt (movBundle s pin) q then
          (P (Machine.dstOp (machMove s m pin q).dst)).map
            (fun a => (a, (machMove s m pin q).v)) else none)).map
        (fun p : α × Nat => (p.1, T p.2)) := by
  by_cases h : Moves.winAt (movBundle s pin) q = true
  · rw [if_pos h, if_pos h]
    exact (pair_map_T _ _ T).symm
  · have h' : Moves.winAt (movBundle s pin) q = false := by simpa using h
    rw [if_neg h, if_neg h]
    rfl

/-- A winning hit slot's `T`-scanned value is the cut's `Q` of the slot word. -/
theorem scan_at_hit_T (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (G : BitVec 5) (hGn : (G == Moves.dgNone) = false)
    {α : Type} {β : Type} (P : Machine.DstOp → Option α) (Q : BitVec 6 → Option α)
    (T : Nat → β)
    (hPQ : ∀ d, d < 64 → P (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == G) then Q (BitVec.ofNat 6 d) else none))
    (q : Nat) (hq : q < 6) (hhit : Moves.hitAt (mvEn s pin) (mvGrp s pin) G q = true)
    (hwin : Moves.winAt (movBundle s pin) q = true) :
    (if Moves.winAt (movBundle s pin) q then
        (P (Machine.dstOp (machMove s m pin q).dst)).map
          (fun a => (a, T (machMove s m pin q).v)) else none)
      = (Q ((movBundle s pin).get q).dst).map
        (fun a => (a, T ((movBundle s pin).get q).data.toNat)) := by
  rw [scan_T s m pin P T q, scan_at_hit s m pin hbus G hGn P Q hPQ q hq hhit hwin]
  cases hq' : Q ((movBundle s pin).get q).dst <;> rfl

/-- A non-hit slot's `T`-scanned value is `none`. -/
theorem scan_at_no_hit_T (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (G : BitVec 5) (hGn : (G == Moves.dgNone) = false)
    {α : Type} {β : Type} (P : Machine.DstOp → Option α) (Q : BitVec 6 → Option α)
    (T : Nat → β)
    (hPQ : ∀ d, d < 64 → P (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == G) then Q (BitVec.ofNat 6 d) else none))
    (q : Nat) (hq : q < 6) (h : Moves.hitAt (mvEn s pin) (mvGrp s pin) G q = false) :
    (if Moves.winAt (movBundle s pin) q then
        (P (Machine.dstOp (machMove s m pin q).dst)).map
          (fun a => (a, T (machMove s m pin q).v)) else none) = none := by
  rw [scan_T s m pin P T q, scan_at_no_hit s m pin hbus G hGn P Q hPQ q hq h]
  rfl

/-- The first hit of `range n`: every earlier index is not a hit. -/
theorem range_find?_before (p : Nat → Bool) : ∀ (n k : Nat),
    (List.range n).find? p = some k → ∀ j, j < k → p j = false := by
  intro n
  induction n with
  | zero => intro k h; simp at h
  | succ n ih =>
    intro k h j hj
    rw [List.range_succ, List.find?_append] at h
    cases hn : (List.range n).find? p with
    | some a =>
      rw [hn] at h
      simp only [Option.or] at h
      have hka : a = k := by simpa using h
      exact ih a hn j (by omega)
    | none =>
      rw [hn] at h
      simp only [Option.none_or] at h
      rw [List.find?_cons, List.find?_nil] at h
      cases hpn : p n with
      | true =>
        rw [hpn] at h
        simp only at h
        have hkn : n = k := by simpa using h
        have hall := List.find?_eq_none.mp hn
        have hjmem : j ∈ List.range n := List.mem_range.mpr (by omega)
        have h' := hall j hjmem
        cases hh : p j with
        | false => rfl
        | true => exact absurd hh h'
      | false =>
        rw [hpn] at h
        simp at h

/-- No contender for `G`: the RTL's hit mask is zero. -/
theorem hitsMask_eq_zero (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (h : ∀ j, j < 6 → Moves.hitAt en grp G j = false) :
    Moves.hitsMask en grp G = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hb : CoreCtl.bitAt (Moves.hitsMask en grp G) j = false := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Moves.hitsMask_bit_0]; exact h 0 (by omega)
    · rw [Moves.hitsMask_bit_1]; simp [h 0 (by omega), h 1 (by omega)]
    · rw [Moves.hitsMask_bit_2]; simp [h 0 (by omega), h 1 (by omega), h 2 (by omega)]
    · rw [Moves.hitsMask_bit_3]
      simp [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]
    · rw [Moves.hitsMask_bit_4]
      simp [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega)]
    · rw [Moves.hitsMask_bit_5]
      simp [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
        h 5 (by omega)]
  rw [bitAt_eq_bitOf, Bridge.Core.bitOf_eq_getLsbD] at hb
  rw [hb]
  exact (BitVec.getLsbD_zero (w := 6) (i := j)).symm

/-- A later contender of a non-keyed group does not win: the first hit blocks it
(same key). -/
theorem winAt_false_of_later_hit (s : State) (pin : Machine.PinIn) (G : BitVec 5)
    (hGb : (G == Moves.dgNone) = false)
    (hG0 : (G == Moves.dgLSym) = false) (hG1 : (G == Moves.dgTStop) = false)
    {k j : Nat} (hkj : k < j) (hj6 : j < 6)
    (hk : Moves.hitAt (mvEn s pin) (mvGrp s pin) G k = true)
    (hj : Moves.hitAt (mvEn s pin) (mvGrp s pin) G j = true) :
    Moves.winAt (movBundle s pin) j = false := by
  obtain ⟨henk, hgrpk⟩ := hit_enabled s pin G hGb k (by omega) hk
  obtain ⟨henj, hgrpj⟩ := hit_enabled s pin G hGb j hj6 hj
  have hvk : Moves.validAt ((movBundle s pin).get k) = true :=
    Moves.valid_of_group (by simpa using hGb) henk hgrpk
  have hvj : Moves.validAt ((movBundle s pin).get j) = true :=
    Moves.valid_of_group (by simpa using hGb) henj hgrpj
  have hsk : Moves.sameKey ((movBundle s pin).get k) ((movBundle s pin).get j) = true :=
    Bridge.Moves.sameKey_of_group hgrpk hgrpj hG0 hG1
  have hbl : Moves.blocked (movBundle s pin) j = true :=
    (Moves.blocked_spec (movBundle s pin) j).mpr ⟨k, hkj, hvk, hsk⟩
  unfold Moves.winAt
  rw [hvj, hbl]
  rfl

/-- **The group pick.**  A `dstOp`-pattern scan over the machine's resolved winners at
the cut's six-slot bundle is the cut's `pickWord` of the destination's write group:
the lowest contender wins, and its `{we, dst, data}` word is the group's pick.  The
statement is generic in the pattern `P` and the cut-side payload read `Q`; the table
identity `hPQ` (the `DstKindTable`-style payload hypothesis of
`WIRE_MOVEFABRIC_NOTES` §6) links the two, and `T` is the consumer's data projection
(identity, `% 16`, `% 8`, …).  `hG0`/`hG1` exclude the two keyed groups
(`L.SYM`, `T.STOP`), whose picks are per line resp. per thread. -/
theorem pickScan (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) {α : Type} {β : Type} (P : Machine.DstOp → Option α)
    (Q : BitVec 6 → Option α) (T : Nat → β) (G : BitVec 5)
    (hGb : (G == Moves.dgNone) = false)
    (hG0 : (G == Moves.dgLSym) = false) (hG1 : (G == Moves.dgTStop) = false)
    (hPQ : ∀ d, d < 64 → P (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == G) then Q (BitVec.ofNat 6 d) else none)) :
    (List.range 6).findSome? (fun q => if Moves.winAt (movBundle s pin) q then
        (P (Machine.dstOp (machMove s m pin q).dst)).map
          (fun a => (a, T (machMove s m pin q).v)) else none)
      = (if (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) G)
              (mvDst s pin) (mvDat s pin)).we
          then (Q ((Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) G)
              (mvDst s pin) (mvDat s pin)).dst)).map
            (fun a => (a, T ((Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) G)
              (mvDst s pin) (mvDat s pin)).data.toNat)))
          else none) := by
  classical
  by_cases hsome : ((List.range 6).find?
      (fun k => Moves.hitAt (mvEn s pin) (mvGrp s pin) G k)).isSome
  · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hsome
    have hmem := List.mem_of_find?_eq_some hk
    have hhit := List.find?_some hk
    have hk6 : k < 6 := List.mem_range.mp hmem
    have hkmin : ∀ j, j < k → Moves.hitAt (mvEn s pin) (mvGrp s pin) G j = false :=
      range_find?_before (fun j => Moves.hitAt (mvEn s pin) (mvGrp s pin) G j) 6 k hk
    have hwin := winAt_of_hits s pin G hGb k hk6 hkmin hhit
    -- every slot other than `k` scans to `none`
    have hother : ∀ j, j < 6 → j ≠ k →
        (if Moves.winAt (movBundle s pin) j then
          (P (Machine.dstOp (machMove s m pin j).dst)).map
            (fun a => (a, T (machMove s m pin j).v)) else none) = none := by
      intro j hj6 hjk
      by_cases hlt : j < k
      · exact scan_at_no_hit_T s m pin hbus G hGb P Q T hPQ j hj6 (hkmin j hlt)
      · have hgt : k < j := by omega
        by_cases hhj : Moves.hitAt (mvEn s pin) (mvGrp s pin) G j = true
        · rw [winAt_false_of_later_hit s pin G hGb hG0 hG1 hgt hj6 hhit hhj]
          rfl
        · have hf : Moves.hitAt (mvEn s pin) (mvGrp s pin) G j = false := by simpa using hhj
          exact scan_at_no_hit_T s m pin hbus G hGb P Q T hPQ j hj6 hf
    have hkval := scan_at_hit_T s m pin hbus G hGb P Q T hPQ k hk6 hhit hwin
    have hpick := Bridge.Moves.pickWord_eq_word (mvEn s pin) (mvGrp s pin) (mvDst s pin)
      (mvDat s pin) (mvXl s) (mvXt s) G k hk6 hhit hkmin
    have hwe : (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) G)
        (mvDst s pin) (mvDat s pin)).we = true := by
      rw [hpick]
    rw [if_pos hwe]
    rw [hpick]
    cases hQk : Q ((movBundle s pin).get k).dst with
    | some a =>
      have hat : (if Moves.winAt (movBundle s pin) k then
          (P (Machine.dstOp (machMove s m pin k).dst)).map
            (fun a => (a, T (machMove s m pin k).v)) else none)
            = some (a, T ((movBundle s pin).get k).data.toNat) := by
        rw [hkval, hQk]
        rfl
      have hscan := findSome_range_six
        (fun q => if Moves.winAt (movBundle s pin) q then
          (P (Machine.dstOp (machMove s m pin q).dst)).map
            (fun a => (a, T (machMove s m pin q).v)) else none)
        hk6 hat (fun j hj => hother j (by omega) (by omega))
      rw [hscan]
      rfl
    | none =>
      exact findSome?_eq_none _ (fun q hq => by
        rw [List.mem_range] at hq
        by_cases hqk : q = k
        · subst hqk
          rw [hkval, hQk]
          rfl
        · exact hother q hq hqk)
  · have hnone0 : (List.range 6).find?
        (fun k => Moves.hitAt (mvEn s pin) (mvGrp s pin) G k) = none := by
      cases h : (List.range 6).find? (fun k => Moves.hitAt (mvEn s pin) (mvGrp s pin) G k) with
      | none => rfl
      | some k => exact absurd (by rw [h]; rfl) hsome
    have hfalse : ∀ j, j < 6 → Moves.hitAt (mvEn s pin) (mvGrp s pin) G j = false := by
      intro j hj
      have h' := (List.find?_eq_none.mp hnone0) j (List.mem_range.mpr hj)
      cases hb : Moves.hitAt (mvEn s pin) (mvGrp s pin) G j with
      | false => rfl
      | true => exact absurd hb h'
    have hnone : ∀ q ∈ List.range 6,
        (if Moves.winAt (movBundle s pin) q then
          (P (Machine.dstOp (machMove s m pin q).dst)).map
            (fun a => (a, T (machMove s m pin q).v)) else none) = none := by
      intro q hq
      rw [List.mem_range] at hq
      exact scan_at_no_hit_T s m pin hbus G hGb P Q T hPQ q hq (hfalse q hq)
    rw [findSome?_eq_none _ hnone, hitsMask_eq_zero (mvEn s pin) (mvGrp s pin) G hfalse,
      Moves.pickWord_none (0 : BitVec 6) (mvDst s pin) (mvDat s pin) rfl]
    rfl

/-- **The group pick, in the consumer shape.**  The same identity for `mWs`, the
machine's resolved winner list, from `ChipRel` + `Inv` + `CoreInputBus` +
`DstKindTable` (the hypotheses of `premise_cores` and `moveBus_of_chipRel`). -/
theorem pickScan_mWs (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable)
    {α : Type} {β : Type} (P : Machine.DstOp → Option α) (Q : BitVec 6 → Option α)
    (T : Nat → β) (G : BitVec 5) (hGb : (G == Moves.dgNone) = false)
    (hG0 : (G == Moves.dgLSym) = false) (hG1 : (G == Moves.dgTStop) = false)
    (hPQ : ∀ d, d < 64 → P (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == G) then Q (BitVec.ofNat 6 d) else none)) :
    (mWs m pin).findSome? (fun mv => (P (Machine.dstOp mv.dst)).map
        (fun a => (a, T mv.v)))
      = (if (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) G)
              (mvDst s pin) (mvDat s pin)).we
          then (Q ((Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) G)
              (mvDst s pin) (mvDat s pin)).dst)).map
            (fun a => (a, T ((Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) G)
              (mvDst s pin) (mvDat s pin)).data.toNat)))
          else none) := by
  have hbusM := moveBus_of_chipRel s m pin hrel hinv hJGTab hbus hgrp
  have hws := mWs_eq_six s m pin hkind
    (fun c => rel_of_bus s m pin c hrel hinv (hbus c))
    (fun c => by rw [hrel.dbg.2.1]; simp [coreIn])
  have hwin := winners_machMove s m pin hkind hbusM
  rw [hws, hwin.1,
    scan_rewrite (List.range 6) (fun k => Moves.winAt (movBundle s pin) k) (machMove s m pin)
      (fun mv => (P (Machine.dstOp mv.dst)).map (fun a => (a, T mv.v)))]
  exact pickScan s m pin hbusM P Q T G hGb hG0 hG1 hPQ

/-! ## 11. The non-keyed consumer fields: `CtrlMoveFabric.hostOut` and
`UnitInputs.flag`

Both fields are one `pickScan_mWs` instance each.  The remaining hypothesis is the
payload table `hPQ` for the field's write group (the `DstKindTable`-style string
table of `WIRE_MOVEFABRIC_NOTES` §6: `Machine.dstOp` does not reduce on the
generated table's parsed names, `String.splitOnAux` being irreducible). -/

/-- `findSome?` respects a pointwise equality of its function. -/
theorem findSome?_congr {α : Type} {β : Type} {l : List α} {f g : α → Option β}
    (h : ∀ x, f x = g x) : l.findSome? f = l.findSome? g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.findSome?_cons, List.findSome?_cons, h a]
    cases hc : g a with
    | none => simpa only [hc] using ih
    | some b => rfl

/-- A `findSome?` of pairs projects to the `findSome?` of the second components. -/
theorem findSome?_pair_ext {α : Type} {β : Type} {γ : Type} (l : List α)
    (f : α → Option β) (g : α → Nat) (T : Nat → γ) :
    (l.findSome? (fun x => (f x).map (fun a => (a, g x)))).map (fun p => (p.1, T p.2)) =
      l.findSome? (fun x => (f x).map (fun a => (a, T (g x)))) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.findSome?_cons, List.findSome?_cons]
    cases hb : f a with
    | none => simpa [hb] using ih
    | some b => rfl

/-- The projected pair scan is the projection of the pair scan. -/
theorem findSome?_snd_map {α : Type} {β : Type} {γ : Type} (l : List α)
    (f : α → Option β) (g : α → γ) :
    l.findSome? (fun x => ((f x).map (fun a => (a, g x))).map
        (fun p : β × γ => p.2))
      = (l.findSome? (fun x => (f x).map (fun a => (a, g x)))).map
        (fun p : β × γ => p.2) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.findSome?_cons, List.findSome?_cons]
    cases hb : f a with
    | none => simpa only [hb, Option.map_none] using ih
    | some b => rfl

/-- The `T`-projected pair scan is the projection of the pair scan. -/
theorem findSome?_map_ext {α : Type} {β : Type} {γ : Type} (l : List α)
    (f : α → Option β) (g : α → Nat) (T : Nat → γ) :
    l.findSome? (fun x => ((f x).map (fun a => (a, g x))).map
        (fun p : β × Nat => (p.1, T p.2)))
      = (l.findSome? (fun x => (f x).map (fun a => (a, g x)))).map
        (fun p : β × Nat => (p.1, T p.2)) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.findSome?_cons, List.findSome?_cons]
    cases hb : f a with
    | none => simpa only [hb, Option.map_none] using ih
    | some b => rfl

/-- The RTL's `bitAt` on the cut's packed group word is the word's `we`. -/
theorem bitAt_makeWord_14 (we : Bool) (dst : BitVec 6) (data : BitVec 8) :
    Metronome.Glue.bitAt (CoreCtl.makeWord we dst data) 14 = we :=
  CoreCtl.makeWord_we we dst data

/-- The RTL's `slice 8 6` on the cut's packed group word is the word's `dst`. -/
theorem slice_makeWord_8_6 (we : Bool) (dst : BitVec 6) (data : BitVec 8) :
    Metronome.Glue.slice (CoreCtl.makeWord we dst data) 8 6 = dst :=
  CoreCtl.makeWord_dst we dst data

/-- The RTL's `slice 0 8` on the cut's packed group word is the word's `data`. -/
theorem slice_makeWord_0_8 (we : Bool) (dst : BitVec 6) (data : BitVec 8) :
    Metronome.Glue.slice (CoreCtl.makeWord we dst data) 0 8 = data :=
  CoreCtl.makeWord_data we dst data

/-- The RTL's `slice 0 4` on the cut's packed group word is the data byte's nibble. -/
theorem slice_makeWord_0_4 (we : Bool) (dst : BitVec 6) (data : BitVec 8) :
    Metronome.Glue.slice (CoreCtl.makeWord we dst data) 0 4 = BitVec.truncate 4 data := by
  cases we <;>
    (unfold CoreCtl.makeWord Metronome.Glue.slice
     bv_decide)

/-- `truncate 4`'s value is the low nibble. -/
theorem truncate_four_toNat (d : BitVec 8) : (BitVec.truncate 4 d).toNat = d.toNat % 16 := by
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]

/-- **`CtrlMoveFabric.hostOut`**: the mailbox write is the pick of the `HOST.OUT`
write group (code 57). -/
theorem ctrlMoveFabric_hostOut (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable)
    (hPQ : ∀ d, d < 64 →
      (match Machine.dstOp d with | .hostOut => some () | _ => none) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTable 57) then some () else none)) :
    (ctrlInTrue m pin).hostOut = (Bridge.Glue.ctrlInOf (glueIn s pin)).hostOut := by
  have hGb : (Moves.dgTable 57 == Moves.dgNone) = false := by decide
  have hG0 : (Moves.dgTable 57 == Moves.dgLSym) = false := by decide
  have hG1 : (Moves.dgTable 57 == Moves.dgTStop) = false := by decide
  have hscan := pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
    (fun d => match d with | .hostOut => some () | _ => none) (fun _ => some ())
    (fun v => v) (Moves.dgTable 57) hGb hG0 hG1 hPQ
  have hpt : ∀ mv : Machine.Move,
      (match Machine.dstOp mv.dst with | .hostOut => some mv.v | _ => none) =
      ((match Machine.dstOp mv.dst with | .hostOut => some () | _ => none).map
        (fun a => (a, mv.v))).map (fun p : Unit × Nat => p.2) := by
    intro mv
    cases h : Machine.dstOp mv.dst <;> rfl
  rw [show (ctrlInTrue m pin).hostOut = (mWs m pin).findSome? (fun mv =>
      match Machine.dstOp mv.dst with | .hostOut => some mv.v | _ => none) from rfl,
    findSome?_congr (fun mv => hpt mv),
    findSome?_snd_map (mWs m pin)
      (fun mv => match Machine.dstOp mv.dst with | .hostOut => some () | _ => none)
      (fun mv => mv.v), hscan]
  rw [show Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (Moves.dgTable 57))
      (mvDst s pin) (mvDat s pin) = gw s pin 57 from rfl]
  have hcut : (Bridge.Glue.ctrlInOf (glueIn s pin)).hostOut =
      (if (gw s pin 57).we then some (gw s pin 57).data.toNat else none) := by
    simp only [Bridge.Glue.ctrlInOf, Metronome.Glue.hostOutWrite, Metronome.Glue.hostOutData,
      glueIn, houtWord, CoreCtl.GroupWord.pack, bitAt_makeWord_14, slice_makeWord_0_8]
  rw [hcut]
  cases (gw s pin 57).we <;> rfl

/-- **`UnitInputs.flag`, low-nibble form.**  The machine's flag write is the pick of
the `FLAGS` write group (codes 5/6).  The cut consumes the data byte's low nibble
(`Glue.flagsIndex = slice wFlags 0 4`), the machine the whole byte, so only the
projected form is true (see `flag_data_witness`). -/
theorem unitInputs_flag_low4 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable)
    (hPQ : ∀ d, d < 64 →
      (match Machine.dstOp d with | .fset => some true | .fclr => some false | _ => none) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTable 5) then
        some (BitVec.ofNat 6 d == Metronome.Glue.flagsSetDst) else none)) :
    (mUnitsIn m pin).flag.map (fun p : Bool × Nat => (p.1, p.2 % 16)) =
      (Bridge.Glue.unitsInOf (glueIn s pin)).flag := by
  have hGb : (Moves.dgTable 5 == Moves.dgNone) = false := by decide
  have hG0 : (Moves.dgTable 5 == Moves.dgLSym) = false := by decide
  have hG1 : (Moves.dgTable 5 == Moves.dgTStop) = false := by decide
  have hscan := pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
    (fun d => match d with | .fset => some true | .fclr => some false | _ => none)
    (fun dst => some (dst == Metronome.Glue.flagsSetDst)) (fun v => v)
    (Moves.dgTable 5) hGb hG0 hG1 hPQ
  have hpt : ∀ mv : Machine.Move,
      (match Machine.dstOp mv.dst with
        | .fset => some (true, mv.v) | .fclr => some (false, mv.v) | _ => none) =
      (match Machine.dstOp mv.dst with
        | .fset => some true | .fclr => some false | _ => none).map
        (fun a => (a, mv.v)) := by
    intro mv
    cases h : Machine.dstOp mv.dst <;> rfl
  rw [show (mUnitsIn m pin).flag = (mWs m pin).findSome? (fun mv =>
      match Machine.dstOp mv.dst with
      | .fset => some (true, mv.v)
      | .fclr => some (false, mv.v)
      | _ => none) from rfl,
    findSome?_congr (fun mv => hpt mv), hscan]
  rw [show Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (Moves.dgTable 5))
      (mvDst s pin) (mvDat s pin) = gw s pin 5 from rfl]
  have hcut : (Bridge.Glue.unitsInOf (glueIn s pin)).flag =
      (if (gw s pin 5).we then some ((gw s pin 5).dst == Metronome.Glue.flagsSetDst,
        (BitVec.truncate 4 (gw s pin 5).data).toNat) else none) := by
    simp only [Bridge.Glue.unitsInOf, Metronome.Glue.flagsWrite, Metronome.Glue.flagsValue,
      Metronome.Glue.flagsIndex, glueIn, flagsWord, CoreCtl.GroupWord.pack,
      bitAt_makeWord_14, slice_makeWord_8_6, slice_makeWord_0_4]
  rw [hcut]
  cases (gw s pin 5).we <;> simp [truncate_four_toNat]

/-- The machine's flag data byte is not the cut's nibble: `UnitInputs.flag`'s
`(Bool, mv.v)` against `(flagsValue, flagsIndex.toNat)` fails for a winning
`FLAGS` move whose data byte has high bits set. -/
theorem flag_data_witness : (255 : Nat) ≠ (BitVec.truncate 4 (255 : BitVec 8)).toNat := by
  decide
/-! ## 12. The payload table (`DstPayloadTable`) and its consumers

Following `Bridge.Moves.DstKindTable` (line ~43): one global hypothesis for the
machine's *destination payload* decode, checked by compiled evaluation in
`data/raw/lean_chipcut_wire_movefabric_v4_20261121/decode_check_payload.lean`.
The kernel cannot reduce `Machine.Util.dstOfName` on the generated table's parsed
names (`String.splitOnAux` is `@[irreducible]`), so `dstOp` has no kernel value for
`R0..R3`, `SH*`, `CNT*`, `LF*`, `S*`, `L*.CTL`; the table is the single hypothesis
that closes them all.

The families are the cut's **write groups**, not single codes: several groups hold
more than one destination (`ACC` = 7..13, `FLAGS` = 5/6, `SHk` = `LD`/`SH`,
`CNTk` = `LO`/`HI`/`DEC`, `LFk` = `ST`/`B0..B3`, `P0` = `AL`/`AH`/`W`/`R`,
`Sk` = `ADV`/`RX`/`CTL`), which is exactly why the cut reads those groups' picks
through one `gw` word and decides the port from the word's destination code. -/

/-- The cut's write-group families whose payload the machine's decoder must
reproduce. -/
inductive Fam where
  /-- `ACC.LD..ACC.CMP` (group 3, codes 7..13) -/
  | acc
  /-- `FLAGS.SET`/`FLAGS.CLR` (group 2, codes 5/6) -/
  | flags
  /-- `Rk` (group 4+k, code 14+k) -/
  | reg (k : Nat)
  /-- `SHk.LD`/`SHk.SH` (group 8+k, codes 18+k/20+k) -/
  | sh (k : Nat)
  /-- `SHk.CFG` (group 10+k, code 22+k) -/
  | shCfg (k : Nat)
  /-- `CNTk.LO`/`HI`/`DEC` (group 12+k, codes 24+k/27+k/30+k) -/
  | cnt (k : Nat)
  /-- `LFk.ST`/`LFk.B0..B3` (group 15+k, codes 33+k/35+4k+b) -/
  | lf (k : Nat)
  /-- `P0.AL`/`AH`/`W`/`R` (group 17, codes 43..46) -/
  | p0
  /-- `Sk.ADV`/`RX`/`CTL` (group 18+k, codes 47+k/49+k/51+k) -/
  | stream (k : Nat)
  /-- `Lk.CTL` (group 20+k, code 53+k) -/
  | lCtl (k : Nat)
  /-- `HOST.OUT` (group 24, code 57) -/
  | hostOut
deriving Repr, DecidableEq

/-- The machine-side membership predicate of a family: does `dstOp` carry one of
the family's destination codes? -/
def famIn : Fam → Machine.DstOp → Bool
  | .acc, o => match o with | .acc j => decide (j < 7) | _ => false
  | .flags, o => match o with | .fset => true | .fclr => true | _ => false
  | .reg k, o => match o with | .reg j => j == k | _ => false
  | .sh k, o => match o with | .shLd j => j == k | .shSh j => j == k | _ => false
  | .shCfg k, o => match o with | .shCfg j => j == k | _ => false
  | .cnt k, o => match o with
    | .cntLo j => j == k | .cntHi j => j == k | .cntDec j => j == k | _ => false
  | .lf k, o => match o with | .lfSt j => j == k | .lfB j _ => j == k | _ => false
  | .p0, o => match o with | .pAl => true | .pAh => true | .pW => true | .pR => true | _ => false
  | .stream k, o => match o with
    | .sAdv j => j == k | .sRx j => j == k | .sCtl j => j == k | _ => false
  | .lCtl k, o => match o with | .lCtl j => j == k | _ => false
  | .hostOut, o => match o with | .hostOut => true | _ => false

/-- The canonical (lowest) destination code of a family; it fixes the group code. -/
def famCode : Fam → Nat
  | .acc => 7
  | .flags => 5
  | .reg k => 14 + k
  | .sh k => 18 + k
  | .shCfg k => 22 + k
  | .cnt k => 24 + k
  | .lf k => 33 + k
  | .p0 => 43
  | .stream k => 47 + k
  | .lCtl k => 53 + k
  | .hostOut => 57

/-- The family's cut write group. -/
def famG (f : Fam) : BitVec 5 := Moves.dgTable (BitVec.ofNat 6 (famCode f))

/-- One write group's payload: the cut's group test for code `d` is exactly the
machine's membership predicate. -/
def PayloadGroup (P : Machine.DstOp → Bool) (G : BitVec 5) : Prop :=
  ∀ d, d < 64 → (Moves.dgTable (BitVec.ofNat 6 d) == G) = P (Machine.dstOp d)

/-- **The global destination-payload table.**  Every write group's cut code set is
exactly the set of codes whose machine decode carries that group's payload, and
every group has a real (non-`NULL`, non-`L.SYM`, non-`T.STOP`) code — the three
side conditions `pickScan` needs.  This is the `DstKindTable`-style single
hypothesis for the *payload* (the kind table constrains only
`null`/`LSYM`/`TSTOP`/other); `decode_check_payload.lean` checks both components by
compiled evaluation of `Machine.dstOp` for all 64 codes and all `Fam` values. -/
structure DstPayloadTable : Prop where
  /-- the group's codes are exactly the payload's codes -/
  payload : ∀ f : Fam, PayloadGroup (famIn f) (famG f)
  /-- the group is a real, non-keyed group: `pickScan`'s three side conditions -/
  nonkeyed : ∀ f : Fam, (famG f == Moves.dgNone) = false ∧
    (famG f == Moves.dgLSym) = false ∧ (famG f == Moves.dgTStop) = false
  /-- the payload index fixes the code (and so the group's write strobe) for the
  index-carrying families -/
  codeOf : ∀ d, d < 64 → ∀ n : Nat,
    (Machine.dstOp d = .reg n → d = 14 + n) ∧
    (Machine.dstOp d = .shCfg n → d = 22 + n) ∧
    (Machine.dstOp d = .acc n → d = 7 + n)
  /-- the accumulator op code is always one of the seven ISA codes -/
  accRange : ∀ d, d < 64 → ∀ n : Nat, Machine.dstOp d = .acc n → n < 7

/-- The table's per-family payload form. -/
theorem PayloadGroup.of_table {f : Fam} (h : DstPayloadTable) : PayloadGroup (famIn f) (famG f) :=
  h.payload f

/-- The table's per-family side conditions (`NULL`/`L.SYM`/`T.STOP`). -/
theorem famG_nonkeyed {f : Fam} (hT : DstPayloadTable) :
    (famG f == Moves.dgNone) = false ∧ (famG f == Moves.dgLSym) = false ∧
      (famG f == Moves.dgTStop) = false :=
  hT.nonkeyed f

/-- The table turns a family's membership predicate into the `hPQ` shape
`pickScan` needs: a payload read `W` that is defined exactly on the family and
agrees with `Q` there. -/
theorem hPQ_of_payload {α : Type} (P : Machine.DstOp → Bool)
    (W : Machine.DstOp → Option α) (Q : BitVec 6 → Option α) (G : BitVec 5)
    (hpg : PayloadGroup P G)
    (ht : ∀ d, d < 64 → P (Machine.dstOp d) = true →
      W (Machine.dstOp d) = Q (BitVec.ofNat 6 d))
    (hf : ∀ d, d < 64 → P (Machine.dstOp d) = false →
      W (Machine.dstOp d) = none) :
    ∀ d, d < 64 → W (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == G) then Q (BitVec.ofNat 6 d) else none) := by
  intro d hd
  have h := hpg d hd
  cases hp : P (Machine.dstOp d) with
  | true =>
    have hg : (Moves.dgTable (BitVec.ofNat 6 d) == G) = true := by rw [h, hp]
    rw [ht d hd hp, hg, if_pos rfl]
  | false =>
    have hg : (Moves.dgTable (BitVec.ofNat 6 d) == G) = false := by rw [h, hp]
    rw [hf d hd hp, hg]
    rfl

/-- **`CtrlMoveFabric.hostOut` from the payload table** (no `hPQ` hypothesis). -/
theorem ctrlMoveFabric_hostOut_of_table (s : State) (m : Machine.State)
    (pin : Machine.PinIn) (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable) (hT : DstPayloadTable) :
    (ctrlInTrue m pin).hostOut = (Bridge.Glue.ctrlInOf (glueIn s pin)).hostOut := by
  refine ctrlMoveFabric_hostOut s m pin hrel hinv hJGTab hbus hgrp hkind ?_
  refine hPQ_of_payload (famIn .hostOut)
    (fun o => match o with | .hostOut => some () | _ => none) (fun _ => some ())
    (famG .hostOut) (hT.payload .hostOut) ?_ ?_
  · intro d hd hp
    cases h : Machine.dstOp d <;> simp_all [famIn]
  · intro d hd hp
    cases h : Machine.dstOp d <;> simp_all [famIn]




theorem unitInputs_reg (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable) (hT : DstPayloadTable) :
    (mUnitsIn m pin).reg = (Bridge.AccB.absIn (accIn s pin)).reg := by
  have hscan : ∀ k : Nat, k < 4 →
      (mWs m pin).findSome? (fun mv => match Machine.dstOp mv.dst with
        | .reg j => if j == k then some mv.v else none
        | _ => none) =
      (if (gw s pin (BitVec.ofNat 6 (14 + k))).we then
        some (gw s pin (BitVec.ofNat 6 (14 + k))).data.toNat else none) := by
    intro k _hk
    have hpq := hPQ_of_payload (famIn (.reg k))
      (fun o => match o with | .reg j => if j == k then some () else none | _ => none)
      (fun _ => some ()) (famG (.reg k)) (hT.payload (.reg k))
      (by intro d _ hp; cases h : Machine.dstOp d <;> simp_all [famIn])
      (by intro d _ hp; cases h : Machine.dstOp d <;> simp_all [famIn])
    have hpt : ∀ mv : Machine.Move,
        (match Machine.dstOp mv.dst with
          | .reg j => if j == k then some mv.v else none
          | _ => none) =
        ((match Machine.dstOp mv.dst with
          | .reg j => if j == k then some () else none
          | _ => none).map (fun a => (a, mv.v))).map (fun p : Unit × Nat => p.2) := by
      intro mv
      cases h : Machine.dstOp mv.dst <;> simp
    rw [findSome?_congr (fun mv => hpt mv),
      findSome?_snd_map (mWs m pin)
        (fun mv => match Machine.dstOp mv.dst with
          | .reg j => if j == k then some () else none | _ => none)
        (fun mv => mv.v),
      pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
        (fun o => match o with | .reg j => if j == k then some () else none | _ => none)
        (fun _ => some ()) (fun v => v) (famG (.reg k))
        (famG_nonkeyed hT).1 (famG_nonkeyed hT).2.1 (famG_nonkeyed hT).2.2 hpq]
    rw [show gw s pin (BitVec.ofNat 6 (14 + k)) =
        Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.reg k)))
          (mvDst s pin) (mvDat s pin) from rfl]
    cases (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.reg k)))
      (mvDst s pin) (mvDat s pin)).we <;> rfl
  apply Vector.ext
  intro k hk
  have hcut : (Bridge.AccB.absIn (accIn s pin)).reg[k] =
      (if (gw s pin (BitVec.ofNat 6 (14 + k))).we then
        some (gw s pin (BitVec.ofNat 6 (14 + k))).data.toNat else none) := by
    have hb : Metronome.Units.bitAt (accIn s pin).rWe k =
        (gw s pin (BitVec.ofNat 6 (14 + k))).we := by
      simp only [accIn, Metronome.Units.bitAt]
      exact Discharge.packBools_bit 4 (fun j => (gw s pin (BitVec.ofNat 6 (14 + j))).we) k hk
    have hr : Bridge.AccB.rbyte (accIn s pin).rD k =
        (gw s pin (BitVec.ofNat 6 (14 + k))).data := by
      simp only [accIn, Bridge.AccB.rbyte]
      exact Discharge.packNs_slice 8 4 (fun j => (gw s pin (BitVec.ofNat 6 (14 + j))).data) k hk
    rw [show (Bridge.AccB.absIn (accIn s pin)).reg = Bridge.AccB.absReg (accIn s pin) from rfl]
    rw [show Bridge.AccB.absReg (accIn s pin) = Vector.ofFn (fun i : Fin 4 =>
        if Metronome.Units.bitAt (accIn s pin).rWe i.val then
          some (Bridge.AccB.rbyte (accIn s pin).rD i.val).toNat else none) from rfl]
    rw [show (Vector.ofFn (fun i : Fin 4 =>
        if Metronome.Units.bitAt (accIn s pin).rWe i.val then
          some (Bridge.AccB.rbyte (accIn s pin).rD i.val).toNat else none))[k] =
        (if Metronome.Units.bitAt (accIn s pin).rWe k then
          some (Bridge.AccB.rbyte (accIn s pin).rD k).toNat else none) from by
      show (Vector.ofFn (fun i : Fin 4 =>
        if Metronome.Units.bitAt (accIn s pin).rWe i.val then
          some (Bridge.AccB.rbyte (accIn s pin).rD i.val).toNat else none)).get ⟨k, hk⟩ = _
      exact Discharge.vec_get_ofFn' _ ⟨k, hk⟩, hb, hr]
  rw [show (mUnitsIn m pin).reg[k] = (mWs m pin).findSome? (fun mv =>
      match Machine.dstOp mv.dst with
      | .reg j => if j == k then some mv.v else none
      | _ => none) from by
    show (Vector.ofFn (fun i : Fin 4 => (mWs m pin).findSome? (fun mv =>
      match Machine.dstOp mv.dst with
      | .reg j => if j == i.val then some mv.v else none
      | _ => none))).get ⟨k, hk⟩ = _
    exact Discharge.vec_get_ofFn' _ ⟨k, hk⟩, hcut]
  exact hscan k hk



/-- **A group pick that fires has a first contender**: the pick's `we` gives the
lowest slot in the group, with every earlier slot a non-contender.  (Reusable by
the keyed/group discharge files.) -/
theorem pickWord_we_exists (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (dst : BitVec 36) (dat : BitVec 48)
    (hw : (Moves.pickWord (Moves.hitsMask en grp G) dst dat).we = true) :
    ∃ k, k < 6 ∧ Moves.hitAt en grp G k = true ∧
      ∀ j, j < k → Moves.hitAt en grp G j = false := by
  classical
  have hne : Moves.hitsMask en grp G ≠ 0 := by
    intro h0
    rw [Moves.pickWord_we, h0] at hw
    exact absurd hw (by decide)
  have hex : ∃ j, j < 6 ∧ Moves.hitAt en grp G j = true := by
    by_cases h : ∃ j, j < 6 ∧ Moves.hitAt en grp G j = true
    · exact h
    · exfalso
      apply hne
      apply hitsMask_eq_zero
      intro j hj
      cases hb : Moves.hitAt en grp G j with
      | false => rfl
      | true => exact absurd ⟨j, hj, hb⟩ h
  have hsome : ((List.range 6).find?
      (fun k => Moves.hitAt en grp G k)).isSome := by
    obtain ⟨j, hj, hhit⟩ := hex
    cases h : (List.range 6).find? (fun k => Moves.hitAt en grp G k) with
    | none => exact absurd hhit ((List.find?_eq_none.mp h) j (List.mem_range.mpr hj))
    | some k => rfl
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨k, List.mem_range.mp (List.mem_of_find?_eq_some hk), List.find?_some hk,
    range_find?_before (fun j => Moves.hitAt en grp G j) 6 k hk⟩



/-- `truncate 5`'s value is the low five bits. -/
theorem truncate_five_toNat (d : BitVec 8) : (BitVec.truncate 5 d).toNat = d.toNat % 32 := by
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]

/-- The machine's `SHk.CFG` data byte is not the cut's 5-bit `cfgD`: the exact
`UnitInputs.shCfg` form fails for a winning `SHk.CFG` move whose data byte has high
bits set (the cut keeps `truncate 5`). -/
theorem shCfg_data_witness : (1023 : Nat) ≠ (BitVec.truncate 5 (1023 : BitVec 8)).toNat := by
  decide


/-- **The one-hot mask of the first contender.**  (Spliced verbatim from the
orchestrator's `scratch_onehot_orch.lean`.) -/
theorem hitsMask_onehot_first (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5) (k : Nat)
    (hk : k < 6) (hh : Moves.hitAt en grp G k = true)
    (hb : ∀ j, j < k → Moves.hitAt en grp G j = false) :
    Moves.hitsMask en grp G = (1 : BitVec 6) <<< k := by
  unfold Moves.hitsMask Moves.bits6
  match k, hk with
  | 0, _ => simp [hh]
  | 1, _ =>
    have h0 := hb 0 (by decide)
    simp [hh, h0]
  | 2, _ =>
    have h0 := hb 0 (by decide); have h1 := hb 1 (by decide)
    simp [hh, h0, h1]
  | 3, _ =>
    have h0 := hb 0 (by decide); have h1 := hb 1 (by decide); have h2 := hb 2 (by decide)
    simp [hh, h0, h1, h2]
  | 4, _ =>
    have h0 := hb 0 (by decide); have h1 := hb 1 (by decide); have h2 := hb 2 (by decide)
    have h3 := hb 3 (by decide)
    simp [hh, h0, h1, h2, h3]
  | 5, _ =>
    have h0 := hb 0 (by decide); have h1 := hb 1 (by decide); have h2 := hb 2 (by decide)
    have h3 := hb 3 (by decide); have h4 := hb 4 (by decide)
    simp [hh, h0, h1, h2, h3, h4]

/-- The ISA accumulator op code of a code `7 + j` (`j < 7`) is `j`. -/
theorem opCodeOf_add (j : Nat) (hj : j < 7) :
    (Units.Acc.opCodeOf (BitVec.ofNat 6 (7 + j))).toNat = j := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **`UnitInputs.acc`: the machine's accumulator write is the cut's `ACC` group
pick**, op code included.  No projection: both sides carry the full data byte. -/
theorem unitInputs_acc (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable) (hT : DstPayloadTable) :
    (mUnitsIn m pin).acc = (Bridge.AccB.absIn (accIn s pin)).acc := by
  have hpq := hPQ_of_payload (famIn .acc)
    (fun o => match o with | .acc op => some op | _ => none)
    (fun dst => some (Units.Acc.opCodeOf dst).toNat) (famG .acc) (hT.payload .acc)
    (by
      intro d hd hp
      simp only [famIn] at hp
      cases h : Machine.dstOp d with
      | acc j =>
        rw [h] at hp
        have hlt : j < 7 := of_decide_eq_true hp
        have hd7 : d = 7 + j := (hT.codeOf d hd j).2.2 h
        rw [hd7, opCodeOf_add j hlt]
      | _ => rw [h] at hp; simp at hp)
    (by
      intro d hd hp
      simp only [famIn] at hp
      cases h : Machine.dstOp d with
      | acc j =>
        rw [h] at hp
        have hlt : j < 7 := hT.accRange d hd j h
        simp [hlt] at hp
      | _ => simp [h] at *)
  have hpt : ∀ mv : Machine.Move,
      (match Machine.dstOp mv.dst with | .acc op => some (op, mv.v) | _ => none) =
      ((match Machine.dstOp mv.dst with | .acc op => some op | _ => none).map
        (fun a => (a, mv.v))) := by
    intro mv
    cases h : Machine.dstOp mv.dst <;> simp
  have hscan : (mWs m pin).findSome? (fun mv => match Machine.dstOp mv.dst with
      | .acc op => some (op, mv.v) | _ => none) =
      (if (gw s pin 7).we then some ((Units.Acc.opCodeOf (gw s pin 7).dst).toNat,
        (gw s pin 7).data.toNat) else none) := by
    rw [show gw s pin 7 = Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin)
        (famG .acc)) (mvDst s pin) (mvDat s pin) from rfl]
    rw [findSome?_congr (fun mv => hpt mv)]
    exact pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
      (fun o => match o with | .acc op => some op | _ => none)
      (fun dst => some (Units.Acc.opCodeOf dst).toNat) (fun v => v) (famG .acc)
      (famG_nonkeyed hT).1 (famG_nonkeyed hT).2.1 (famG_nonkeyed hT).2.2 hpq
  rw [show (mUnitsIn m pin).acc = (mWs m pin).findSome? (fun mv =>
      match Machine.dstOp mv.dst with | .acc op => some (op, mv.v) | _ => none) from rfl,
    hscan]
  have hcut : (Bridge.AccB.absIn (accIn s pin)).acc =
      (if (gw s pin 7).we then some ((Units.Acc.opCodeOf (gw s pin 7).dst).toNat,
        (gw s pin 7).data.toNat) else none) := by
    by_cases hz : (accIn s pin).hit = 0
    · have hwe : (gw s pin 7).we = false := by
        rw [show (gw s pin 7).we = !((accIn s pin).hit == 0) from rfl, hz]
        rfl
      rw [Bridge.AccB.absIn_none _ hz, hwe]
      rfl
    · have hne : ((accIn s pin).hit == 0) = false := by
        by_cases h : ((accIn s pin).hit == 0) = true
        · exact absurd (by simpa using h) hz
        · simpa using h
      have hwe : (gw s pin 7).we = true := by
        rw [show (gw s pin 7).we = !((accIn s pin).hit == 0) from rfl, hne]
        rfl
      obtain ⟨k, hk, hhit, hfirst⟩ := pickWord_we_exists (mvEn s pin) (mvGrp s pin)
        (Moves.dgTable 7) (mvDst s pin) (mvDat s pin) hwe
      have hone : (accIn s pin).hit = (1 : BitVec 6) <<< k :=
        hitsMask_onehot_first (mvEn s pin) (mvGrp s pin) (Moves.dgTable 7) k hk hhit hfirst
      rw [Bridge.AccB.absIn_slot (accIn s pin) k hk hone, hwe]
      have hpw := Bridge.Moves.pickWord_eq_word (mvEn s pin) (mvGrp s pin) (mvDst s pin)
        (mvDat s pin) (mvXl s) (mvXt s) (Moves.dgTable 7) k hk hhit hfirst
      have hsel : Units.Acc.opSel (accIn s pin) k =
          Units.Acc.opCodeOf (Core.slice (mvDst s pin) (6 * k) 6) := by
        simp only [Units.Acc.opSel, accIn]
        exact Discharge.packNs_slice 3 6
          (fun j => Units.Acc.opCodeOf (Core.slice (mvDst s pin) (6 * j) 6)) k hk
      have hdat : Units.Acc.opData (accIn s pin) k = Core.slice (mvDat s pin) (8 * k) 8 := rfl
      show some ((Units.Acc.opSel (accIn s pin) k).toNat,
          (Units.Acc.opData (accIn s pin) k).toNat) = _
      rw [hsel, hdat, show gw s pin 7 = Moves.pickWord (Moves.hitsMask (mvEn s pin)
          (mvGrp s pin) (Moves.dgTable 7)) (mvDst s pin) (mvDat s pin) from rfl, hpw,
        movBundle_dst s pin k hk, movBundle_data s pin k hk]
      rfl
  rw [hcut]

/-- `findSome?` commutes with a **value** projection (as opposed to
`findSome?_pair_ext`/`findSome?_map_ext`, which project a pair component): the
form the truncated-value fields (`shCfg` `% 32`, `sym` `% 16`, `ctl` `% 8`) need. -/
theorem findSome?_map_value {α : Type} {β : Type} {γ : Type} (l : List α)
    (f : α → Option β) (T : β → γ) :
    (l.findSome? f).map T = l.findSome? (fun x => (f x).map T) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.findSome?_cons, List.findSome?_cons]
    cases h : f a with
    | none => simpa only [h, Option.map_none] using ih
    | some b => rfl

/-- `UnitInputs.shCfg` in the low-five-bit projection (the cut keeps `cfgD = truncate 5 data`;
the exact 8-bit form is false, `shCfg_data_witness`).  Spliced by the orchestrator from
W1's round-h draft (two fixes: explicit `dat` in `opg_eq_pick`, `gw` unfolded in both branches). -/
theorem unitInputs_shCfg_low5 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size =
      Core.JG_TABLE.getD n 62)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : ∀ q, q < 6 →
      ((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
        (mvXl s) (mvXt s)).get q).group =
        Moves.dgTable (((Moves.bundleOf (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
          (mvXl s) (mvXt s)).get q).dst))
    (hkind : Bridge.Moves.DstKindTable) (hT : DstPayloadTable) :
    ∀ k : Fin 2, ((mUnitsIn m pin).shCfg[k]).map (fun v => v % 32) =
      Bridge.ShifterB.absCfg (shIn s pin k.val) := by
  intro k
  have huniq : (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.shCfg k.val)))
        (mvDst s pin) (mvDat s pin)).we = true →
      ((Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.shCfg k.val)))
        (mvDst s pin) (mvDat s pin)).dst == BitVec.ofNat 6 (22 + k.val)) = true := by
    intro hw
    obtain ⟨j, hj, hhit, hfirst⟩ := pickWord_we_exists (mvEn s pin) (mvGrp s pin)
      (famG (.shCfg k.val)) (mvDst s pin) (mvDat s pin) hw
    have hpw := Bridge.Moves.pickWord_eq_word (mvEn s pin) (mvGrp s pin) (mvDst s pin)
      (mvDat s pin) (mvXl s) (mvXt s) (famG (.shCfg k.val)) j hj hhit hfirst
    rw [show (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.shCfg k.val)))
        (mvDst s pin) (mvDat s pin)).dst = ((movBundle s pin).get j).dst from
      congrArg CoreCtl.GroupWord.dst hpw]
    have hbusM := moveBus_of_chipRel s m pin hrel hinv hJGTab hbus hgrp
    have hgrp' : (Moves.dgTable ((movBundle s pin).get j).dst == famG (.shCfg k.val)) = true := by
      have h2 := hhit
      rw [hitAt_bundle s pin (famG (.shCfg k.val)) (famG_nonkeyed hT).1 j hj,
        Bool.and_eq_true] at h2
      rw [hbusM.grp j hj] at h2
      exact h2.2
    have hlt : ((movBundle s pin).get j).dst.toNat < 64 := by
      simpa using ((movBundle s pin).get j).dst.isLt
    have hfam : famIn (.shCfg k.val) (Machine.dstOp ((movBundle s pin).get j).dst.toNat)
        = true := by
      rw [← hT.payload (.shCfg k.val) _ hlt, Bridge.Moves.ofNat_toNat_6]
      exact hgrp'
    have hcode : ((movBundle s pin).get j).dst = BitVec.ofNat 6 (22 + k.val) := by
      cases h : Machine.dstOp ((movBundle s pin).get j).dst.toNat with
      | shCfg j' =>
        rw [h] at hfam
        have h' : j' = k.val := by simpa [famIn] using hfam
        rw [← Bridge.Moves.ofNat_toNat_6 ((movBundle s pin).get j).dst,
          (hT.codeOf _ hlt j').2.1 h, h']
      | _ => rw [h] at hfam; exact absurd hfam (by simp [famIn])
    rw [hcode, beq_iff_eq]
  have hpq := hPQ_of_payload (famIn (.shCfg k.val))
    (fun o => match o with | .shCfg j => if j == k.val then some () else none | _ => none)
    (fun _ => some ()) (famG (.shCfg k.val)) (hT.payload (.shCfg k.val))
    (by
      intro d hd hp
      simp only [famIn] at hp
      cases h : Machine.dstOp d with
      | shCfg j =>
        rw [h] at hp
        have h' : (j == k.val) = true := by simpa using hp
        rw [beq_iff_eq] at h'
        subst h'
        simp
      | _ => rw [h] at hp; simp at hp)
    (by
      intro d hd hp
      simp only [famIn] at hp
      cases h : Machine.dstOp d with
      | shCfg j =>
        rw [h] at hp
        have h' : (j == k.val) = false := by simpa using hp
        simp [h']
      | _ => simp [h] at *)
  have hpack : (mWs m pin).findSome? (fun mv => match Machine.dstOp mv.dst with
      | .shCfg j => if j == k.val then some mv.v else none
      | _ => none) =
      (if (gw s pin (BitVec.ofNat 6 (22 + k.val))).we then
        some (gw s pin (BitVec.ofNat 6 (22 + k.val))).data.toNat else none) := by
    have hpt : ∀ mv : Machine.Move,
        (match Machine.dstOp mv.dst with
          | .shCfg j => if j == k.val then some mv.v else none
          | _ => none) =
        ((match Machine.dstOp mv.dst with
          | .shCfg j => if j == k.val then some () else none
          | _ => none).map (fun a => (a, mv.v))).map (fun p : Unit × Nat => p.2) := by
      intro mv
      cases Machine.dstOp mv.dst <;> simp
    rw [findSome?_congr (fun mv => hpt mv),
      findSome?_snd_map (mWs m pin)
        (fun mv => match Machine.dstOp mv.dst with
          | .shCfg j => if j == k.val then some () else none | _ => none)
        (fun mv => mv.v),
      pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
        (fun o => match o with | .shCfg j => if j == k.val then some () else none | _ => none)
        (fun _ => some ()) (fun v => v) (famG (.shCfg k.val))
        (famG_nonkeyed hT).1 (famG_nonkeyed hT).2.1 (famG_nonkeyed hT).2.2 hpq]
    rw [show gw s pin (BitVec.ofNat 6 (22 + k.val)) =
        Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.shCfg k.val)))
          (mvDst s pin) (mvDat s pin) from rfl]
    cases (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.shCfg k.val)))
      (mvDst s pin) (mvDat s pin)).we <;> rfl
  rw [show (mUnitsIn m pin).shCfg[k] = (mWs m pin).findSome? (fun mv =>
      match Machine.dstOp mv.dst with
      | .shCfg j => if (j == k.val) = true then some mv.v else none
      | _ => none) from Discharge.vec_get_ofFn' _ k,
    findSome?_map_value (mWs m pin)
      (fun mv => match Machine.dstOp mv.dst with
        | .shCfg j => if (j == k.val) = true then some mv.v else none
        | _ => none) (fun v => v % 32)]
  have hstep : ∀ mv : Machine.Move,
      ((match Machine.dstOp mv.dst with
          | .shCfg j => if j == k.val then some mv.v else none
          | _ => none).map (fun v => v % 32)) =
      ((match Machine.dstOp mv.dst with
          | .shCfg j => if j == k.val then some () else none
          | _ => none).map (fun a => (a, mv.v % 32))).map (fun p : Unit × Nat => p.2) := by
    intro mv
    cases Machine.dstOp mv.dst <;> simp
  rw [findSome?_congr (fun mv => hstep mv),
    findSome?_snd_map (mWs m pin)
      (fun mv => match Machine.dstOp mv.dst with
        | .shCfg j => if j == k.val then some () else none | _ => none)
      (fun mv => mv.v % 32),
    pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
      (fun o => match o with | .shCfg j => if j == k.val then some () else none | _ => none)
      (fun _ => some ()) (fun v => v % 32) (famG (.shCfg k.val))
      (famG_nonkeyed hT).1 (famG_nonkeyed hT).2.1 (famG_nonkeyed hT).2.2 hpq]
  have hcut : Bridge.ShifterB.absCfg (shIn s pin k.val) =
      (if (gw s pin (BitVec.ofNat 6 (22 + k.val))).we then
        some ((gw s pin (BitVec.ofNat 6 (22 + k.val))).data.toNat % 32) else none) := by
    have hstr : strobe s pin (BitVec.ofNat 6 (22 + k.val)) =
        (gw s pin (BitVec.ofNat 6 (22 + k.val))).we := by
      rw [show strobe s pin (BitVec.ofNat 6 (22 + k.val)) = Strobes.opg (mvEn s pin)
          (mvGrp s pin) (mvDst s pin) (Moves.dgTable (BitVec.ofNat 6 (22 + k.val)))
          (BitVec.ofNat 6 (22 + k.val)) from rfl,
        Strobes.opg_eq_pick (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)]
      rw [show Moves.dgTable (BitVec.ofNat 6 (22 + k.val)) = famG (.shCfg k.val) from rfl] at *
      by_cases hw : (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin)
          (famG (.shCfg k.val))) (mvDst s pin) (mvDat s pin)).we = true
      · rw [show gw s pin (BitVec.ofNat 6 (22 + k.val)) = Moves.pickWord
            (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.shCfg k.val)))
            (mvDst s pin) (mvDat s pin) from rfl]
        simp [hw, huniq hw]
      · have hf : (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin)
            (famG (.shCfg k.val))) (mvDst s pin) (mvDat s pin)).we = false := by
          simpa using hw
        rw [show gw s pin (BitVec.ofNat 6 (22 + k.val)) = Moves.pickWord
            (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.shCfg k.val)))
            (mvDst s pin) (mvDat s pin) from rfl, hf]
        simp
    rw [show Bridge.ShifterB.absCfg (shIn s pin k.val) =
        (if (shIn s pin k.val).cfgWe then some ((shIn s pin k.val).cfgD).toNat else none)
        from rfl,
      show (shIn s pin k.val).cfgWe = strobe s pin (BitVec.ofNat 6 (22 + k.val)) from rfl,
      hstr,
      show (shIn s pin k.val).cfgD =
        BitVec.truncate 5 (gw s pin (BitVec.ofNat 6 (22 + k.val))).data from rfl,
      truncate_five_toNat]
  rw [hcut, show gw s pin (BitVec.ofNat 6 (22 + k.val)) = Moves.pickWord
      (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.shCfg k.val)))
      (mvDst s pin) (mvDat s pin) from rfl]
  cases (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.shCfg k.val)))
    (mvDst s pin) (mvDat s pin)).we <;> rfl


end Metronome.ChipCut.Discharge.MoveFabric
