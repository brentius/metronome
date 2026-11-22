import Metronome.Machine
import Metronome.Core

/-!
# Bridge: the core cut (`Metronome.Core`) refines `Machine.coreComb` / `Machine.coreNext`

`Metronome/Core.lean` states SPEC_V2 §5/§6/§7/§12.3 for one `md2_core` instance as an
independent cut; `core_check.py` proves the elaborated RTL equal to it register by
register and output by output.  `Metronome.Machine` states the same sections as a
whole-chip executable machine (`Machine.coreComb`, `Machine.coreNext`).  This file
proves that the cut's transition and outputs *are* the machine's per-core functions
under an explicit abstraction map, so "RTL = cut" composes with "cut = machine".

## Abstraction map

The cut is parameterised by a core index `c : Bool` and takes the thread file, the
guard vector, the source vector, the line inputs, the program word and the freeze flag
as *free* inputs (§5 reads them from ports).  The machine reads them from its
whole-chip state, so the map is relational on the inputs:

* `absCore mout s` is the machine's `CoreSt` of the cut state `s`: the seven registers
  are copied one for one, and the machine's program-memory output register `mout` is
  the caller's value (for the cut: `Input.rdata`, the word at the memory output).
* `coreNat c` is the machine's core index (`false ↦ 0`, `true ↦ 1`).
* `Rel c ms cv p s i` collects the readings the machine takes from chip state:
  * `core`: `vget ms.cores (coreNat c) = absCore i.rdata s`;
  * `guards`: for every line `ln < 4` and every code `k`, bit `k` of the cut's
    effective guard vector `guardVec i.guards i.gLine ln` is the machine's
    `guardVal ms cv p ln (guardOp k)` (§7).  Past the 62-entry table both sides read
    false, so the equation is stated for every code.  The chip's global guard builder
    lies outside the core cut (README "Gaps");
  * `srcs`: for every code `k`, the cut's source byte `slice (srcVec s i) (8k) 8` is
    the machine's `srcVal ms cv p s.xl.toNat imm (srcOp k)` (§6.1); past the 39-entry
    table both sides read zero, likewise the global source builder;
  * `ready`, `coreOf`, `lineOf`, `pcOf`, `w0cOf`, `w1cOf`, `w0hOf`, `w1hOf`: the
    thread file of §4 as the machine decodes it (used by the dispatch scan and the
    watcher address, §5);
  * `run`: `ms.ctrl.run = i.runG`;
  * `rrOk`: the cut's cursor invariant `RR < 6` (`Core.rr_next_lt_six`).

Every value crossing the map is `BitVec.toNat` on the cut side and the machine's `Nat`
(or `bv n x`, which is `x` on the cut's fields: `bv_toNat`).

## `IR` and the memory output

SPEC §5 writes `XV' = load; if load: IR' = the word at the memory output`.  The
machine's `coreNext` follows §5 literally (`ir' = if load then mout else ir`); the cut
(like `md2_core.v`) captures the memory output in *every* unfrozen cycle.  That is the
one reading difference, and it is unobservable: `XV' = load`, so a word captured
without `load` is never decoded.  `step_bridge` carries the side condition
`load ∨ frozen`; `ir_no_load_diverges` states the difference with a witness.

## What is not bridged

* the move *effects* (§6 execution: arming, `LATE`, line/stream/unit writes) — the
  moves/units/line cuts' business.  The move *bus* itself is bridged slot by slot:
  `moves_bridge` shows the cut's `mv_en` bit, `mv_src`/`mv_dst` 6-bit slices and
  `mv_data` byte are the machine's `moveAt`/`mvSrcOf`/`mvDstOf`/`mvDataOf` entry of the
  slot (present exactly when the slot is enabled, see `coreComb_moves`);
* the program-memory contract (`rdata` = the word at the previous fetch address):
  `step_bridge` states the fetch address the machine presents and leaves the next
  cycle's `mout` to the caller;
* the machine's decoded source/guard/jump tables are built at definition time from
  string names (`Array.idxOf?`), which the kernel does not reduce; the one numeric
  table fact is the hypothesis `hJGTab` of `jc_bridge` (see the notes).

No `sorry`, no `native_decide`: `simp`, `omega`, kernel `decide` and `bv_decide` only.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace Metronome.Bridge.Core

open Metronome

/-! ## Bit plumbing -/

/-- The cut's field `slice v lo n` has the `Nat` value of the machine's `nbits`. -/
theorem slice_toNat {w : Nat} (v : BitVec w) (lo n : Nat) :
    (Core.slice v lo n).toNat = Machine.Util.nbits v.toNat lo n := by
  simp [Core.slice, Machine.Util.nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

/-- The cut's `bitOf` is the machine's `nbit`. -/
theorem bitOf_eq_nbit {w : Nat} (v : BitVec w) (k : Nat) :
    Core.bitOf v k = Machine.Util.nbit v.toNat k := by
  unfold Core.bitOf Machine.Util.nbit
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, beq_iff_eq, ne_eq, BitVec.toNat_eq]
  rw [show (BitVec.toNat (0 : BitVec 1)) = 0 from rfl]
  rw [show (BitVec.truncate 1 (BitVec.ushiftRight v k)).toNat = (v.toNat >>> k) % 2 from by
    rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
      show BitVec.ushiftRight v k = (v >>> k) from rfl, BitVec.toNat_ushiftRight]]
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-- `(x == 1)` is `decide (x = 1)`. -/
theorem beq_one_eq_decide (x : Nat) : (x == 1) = decide (x = 1) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]

/-- A one-bit part-select is the bit itself. -/
theorem bitOf_eq_getLsbD {w : Nat} (v : BitVec w) (k : Nat) : Core.bitOf v k = v.getLsbD k := by
  by_cases hk : k < w
  · rw [bitOf_eq_nbit, Machine.Util.nbit, BitVec.getLsbD_eq_getElem hk]
    show ((v.toNat >>> k) % 2 == 1) = v.toNat.testBit k
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, beq_one_eq_decide]
  · rw [bitOf_eq_nbit, Machine.Util.nbit, BitVec.getLsbD_of_ge v k (by omega)]
    have h2 : v.toNat < 2 ^ k := by
      have := v.isLt
      exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h2]
    simp

/-- Bit `k` of a conjunction. -/
theorem bitOf_and {w : Nat} (a b : BitVec w) (k : Nat) :
    Core.bitOf (a &&& b) k = (Core.bitOf a k && Core.bitOf b k) := by
  rw [bitOf_eq_getLsbD, bitOf_eq_getLsbD, bitOf_eq_getLsbD]
  simp

/-- Bit `k` of a disjunction. -/
theorem bitOf_or {w : Nat} (a b : BitVec w) (k : Nat) :
    Core.bitOf (a ||| b) k = (Core.bitOf a k || Core.bitOf b k) := by
  rw [bitOf_eq_getLsbD, bitOf_eq_getLsbD, bitOf_eq_getLsbD]
  simp

/-- Bit `k < w` of `allOnes`. -/
theorem bitOf_allOnes {w : Nat} (k : Nat) (hk : k < w) :
    Core.bitOf (BitVec.allOnes w) k = true := by
  rw [bitOf_eq_getLsbD]
  simp [hk]

/-- Every bit of zero is false. -/
theorem bitOf_zero {w : Nat} (k : Nat) : Core.bitOf (0 : BitVec w) k = false := by
  rw [bitOf_eq_getLsbD]
  simp

/-- The machine's `bv n x.toNat` is the cut's field. -/
theorem bv_toNat {n : Nat} (x : BitVec n) : Machine.Util.bv n x.toNat = x := by
  simp [Machine.Util.bv]

/-- `BitVec.ofNat n x.toNat` is `x`. -/
theorem ofNat_toNat_self {n : Nat} (x : BitVec n) : BitVec.ofNat n x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

/-- A `BitVec 2` is its `Nat` value when that value fits. -/
theorem bv2_eq_of_toNat (x : BitVec 2) (y : Nat) (hy : y < 4) (h : x.toNat = y) :
    x = BitVec.ofNat 2 y := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- A `BitVec 3` is its `Nat` value when that value fits. -/
theorem bv3_eq_of_toNat (x : BitVec 3) (y : Nat) (hy : y < 8) (h : x.toNat = y) :
    x = BitVec.ofNat 3 y := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- `x != 0` on `BitVec` is `x.toNat != 0`. -/
theorem bne_zero_toNat {w : Nat} (x : BitVec w) : (x != 0) = (x.toNat != 0) := by
  rw [Bool.eq_iff_iff]
  simp [BitVec.toNat_eq]

/-- `==` on same-width bit vectors is `==` on their `Nat` values. -/
theorem beq_toNat {w : Nat} (x y : BitVec w) : (x == y) = (x.toNat == y.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, BitVec.toNat_eq, beq_iff_eq]

/-- `toNat` of an `if` on bit vectors distributes. -/
theorem toNat_ite {w : Nat} (cond : Prop) [Decidable cond] (a b : BitVec w) :
    (if cond then a else b).toNat = if cond then a.toNat else b.toNat := by
  split <;> rfl

/-! ## Instruction fields (`wiki/ISA_TABLES_V2.md`, `Machine.Tables.FIELD_*`) -/

theorem i_jmode_eq (s : Core.State) :
    (Core.i_jmode s).toNat = Machine.insnField s.ir Machine.Tables.FIELD_jmode := by
  simp [Core.i_jmode, Machine.insnField, Machine.Tables.FIELD_jmode, Core.slice,
    Machine.Util.nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

theorem i_imm_eq (s : Core.State) :
    (Core.i_imm s).toNat = Machine.insnField s.ir Machine.Tables.FIELD_imm := by
  simp [Core.i_imm, Machine.insnField, Machine.Tables.FIELD_imm, Core.slice,
    Machine.Util.nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

theorem i_cond_eq (s : Core.State) :
    (Core.i_cond s).toNat = Machine.insnField s.ir Machine.Tables.FIELD_cond := by
  simp [Core.i_cond, Machine.insnField, Machine.Tables.FIELD_cond, Core.slice,
    Machine.Util.nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

theorem i_jcond_eq (s : Core.State) :
    Core.i_jcond s = BitVec.ofNat 5 (Machine.insnField s.ir Machine.Tables.FIELD_jcond) := by
  apply BitVec.eq_of_toNat_eq
  simp [Core.i_jcond, Machine.insnField, Machine.Tables.FIELD_jcond, Core.slice,
    Machine.Util.nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, BitVec.isLt]

theorem i_g_eq_0 (s : Core.State) :
    (Core.i_g s 0).toNat = Machine.insnField s.ir Machine.Tables.FIELD_m0_guard := by
  simp [Core.i_g, Machine.insnField, Machine.Tables.FIELD_m0_guard, Core.slice,
    Machine.Util.nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

theorem i_g_eq_1 (s : Core.State) :
    (Core.i_g s 1).toNat = Machine.insnField s.ir Machine.Tables.FIELD_m1_guard := by
  simp [Core.i_g, Machine.insnField, Machine.Tables.FIELD_m1_guard, Core.slice,
    Machine.Util.nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

theorem i_g_eq_2 (s : Core.State) :
    (Core.i_g s 2).toNat = Machine.insnField s.ir Machine.Tables.FIELD_m2_guard := by
  simp [Core.i_g, Machine.insnField, Machine.Tables.FIELD_m2_guard, Core.slice,
    Machine.Util.nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

theorem i_s_eq_0 (s : Core.State) :
    (Core.i_s s 0).toNat = Machine.insnField s.ir Machine.Tables.FIELD_m0_src := by
  simp [Core.i_s, Machine.insnField, Machine.Tables.FIELD_m0_src, Core.slice,
    Machine.Util.nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

theorem i_s_eq_1 (s : Core.State) :
    (Core.i_s s 1).toNat = Machine.insnField s.ir Machine.Tables.FIELD_m1_src := by
  simp [Core.i_s, Machine.insnField, Machine.Tables.FIELD_m1_src, Core.slice,
    Machine.Util.nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

theorem i_s_eq_2 (s : Core.State) :
    (Core.i_s s 2).toNat = Machine.insnField s.ir Machine.Tables.FIELD_m2_src := by
  simp [Core.i_s, Machine.insnField, Machine.Tables.FIELD_m2_src, Core.slice,
    Machine.Util.nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

theorem i_d_eq_0 (s : Core.State) :
    (Core.i_d s 0).toNat = Machine.insnField s.ir Machine.Tables.FIELD_m0_dst := by
  simp [Core.i_d, Machine.insnField, Machine.Tables.FIELD_m0_dst, Core.slice,
    Machine.Util.nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

theorem i_d_eq_1 (s : Core.State) :
    (Core.i_d s 1).toNat = Machine.insnField s.ir Machine.Tables.FIELD_m1_dst := by
  simp [Core.i_d, Machine.insnField, Machine.Tables.FIELD_m1_dst, Core.slice,
    Machine.Util.nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

theorem i_d_eq_2 (s : Core.State) :
    (Core.i_d s 2).toNat = Machine.insnField s.ir Machine.Tables.FIELD_m2_dst := by
  simp [Core.i_d, Machine.insnField, Machine.Tables.FIELD_m2_dst, Core.slice,
    Machine.Util.nbits, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight]

/-- A field of an instruction word is below `2 ^ width`. -/
theorem insnField_lt (ir : BitVec 64) (f : Nat × Nat) : Machine.insnField ir f < 2 ^ f.2 := by
  unfold Machine.insnField Machine.Util.nbits
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-! ## The §7 jump table

`Core.jumpGuardBit` is a flat `if` chain over the 5-bit `jcond`; `Machine.jumpGuard`
indexes a decoded table.  `jumpGuardBit_eq` proves that the chain selects bit
`JG_TABLE[jcond]` (the §7 list, also `wiki/ISA_TABLES_V2.md`), and `pickIdx_eq`
identifies the chain's index with the list.  The machine's *generated* table is not
kernel-reducible (`Array.idxOf?`), so `jc_bridge` takes the numeric agreement
`hJGTab` as an explicit hypothesis (the notes call it out). -/

/-- The jump table as `(test, guard bit)` pairs, in the cut's chain order. -/
def jgTab : List (BitVec 5 × Nat) :=
  [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 17),
   (10, 18), (11, 21), (12, 22), (13, 23), (14, 24), (15, 25), (16, 26), (17, 27),
   (18, 28), (19, 29), (20, 30), (21, 34), (22, 35), (23, 36), (24, 37), (25, 39),
   (26, 41), (27, 43), (28, 38), (29, 40), (30, 42), (31, 44)]

/-- A chain walker over `(test, bit)` pairs: the bit reading. -/
def pickBit (g : BitVec 64) (j : BitVec 5) : List (BitVec 5 × Nat) → Bool
  | [] => false
  | (t, k) :: rest => if j == t then Core.bitOf g k else pickBit g j rest

/-- A chain walker over `(test, bit)` pairs: the selected index (`62` = past the table). -/
def pickIdx (j : BitVec 5) : List (BitVec 5 × Nat) → Nat
  | [] => 62
  | (t, k) :: rest => if j == t then k else pickIdx j rest

/-- The cut's jump chain is the chain walker (the two definitions unfold alike). -/
theorem jumpGuardBit_eq_pick (g : BitVec 64) (j : BitVec 5) :
    Core.jumpGuardBit g j = pickBit g j jgTab := rfl

/-- A bit chain over a list is the index chain read through `bitOf`, when bit 62 is
clear (the cut masks the guard vector to `MD_N_GUARD = 62` bits). -/
theorem pick_eq (g : BitVec 64) (j : BitVec 5) (h62 : Core.bitOf g 62 = false) :
    ∀ xs : List (BitVec 5 × Nat), pickBit g j xs = Core.bitOf g (pickIdx j xs)
  | [] => by simp [pickBit, pickIdx, h62]
  | (t, k) :: rest => by
    simp only [pickBit, pickIdx]
    by_cases h : (j == t) = true <;> simp [h, pick_eq g j h62 rest]

/-- The chain walker's index is the §7 table entry. -/
theorem pickIdx_eq (j : BitVec 5) : pickIdx j jgTab = Core.JG_TABLE.getD j.toNat 62 := by
  revert j
  simp only [pickIdx, jgTab, Core.JG_TABLE]
  decide

/-- The cut's jump chain selects the §7 table entry. -/
theorem jumpGuardBit_eq (g : BitVec 64) (j : BitVec 5) (h62 : Core.bitOf g 62 = false) :
    Core.jumpGuardBit g j = Core.bitOf g (Core.JG_TABLE.getD j.toNat 62) := by
  rw [jumpGuardBit_eq_pick, pick_eq g j h62, pickIdx_eq]

/-! ## The effective guard vector -/

/-- Bit 62 of the effective guard vector is clear (the `lowMask 64 MD_N_GUARD`). -/
theorem guardVec_bit62 (g : BitVec 64) (gl : BitVec 20) (ln : BitVec 2) :
    Core.bitOf (Core.guardVec g gl ln) 62 = false := by
  rw [bitOf_eq_getLsbD]
  simp [Core.guardVec, Core.lowMask, Core.MD_N_GUARD]

/-- Bit 63 of the effective guard vector is clear. -/
theorem guardVec_bit63 (g : BitVec 64) (gl : BitVec 20) (ln : BitVec 2) :
    Core.bitOf (Core.guardVec g gl ln) 63 = false := by
  rw [bitOf_eq_getLsbD]
  simp [Core.guardVec, Core.lowMask, Core.MD_N_GUARD]

/-! ## The abstraction map -/

/-- The machine's core index of the cut's variant flag. -/
def coreNat (c : Bool) : Nat := if c then 1 else 0

/-- The cut's core registers as the machine's `CoreSt`; `mout` is the program-memory
output register (for the cut: `Input.rdata`). -/
def absCore (mout : BitVec 64) (s : Core.State) : Machine.CoreSt :=
  { xv := s.xv, ir := s.ir, rv := s.rv, fpc := s.fpc, xt := s.xt, xl := s.xl, rr := s.rr,
    mout := mout }

/-- The readings the machine takes from chip state, as a relation on the cut's free
inputs.  Every field is a §4/§5/§6/§7 reading the cut takes from a port. -/
structure Rel (c : Bool) (ms : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (s : Core.State) (i : Core.Input) : Prop where
  /-- the register file and the memory output word -/
  core : Machine.Util.vget ms.cores (coreNat c) = absCore i.rdata s
  /-- §7: the effective guard vector at every line and every code -/
  guards : ∀ (ln : Nat), ln < 4 → ∀ k : Nat,
    Core.bitOf (Core.guardVec i.guards i.gLine (BitVec.ofNat 2 ln)) k =
      Machine.guardVal ms cv p ln (Machine.guardOp k)
  /-- §6.1: the source vector at every code -/
  srcs : ∀ k : Nat,
    (Core.slice (Core.srcVec s i) (8 * k) 8).toNat =
      Machine.srcVal ms cv p s.xl.toNat
        (Machine.insnField s.ir Machine.Tables.FIELD_imm) (Machine.srcOp k)
  /-- §4: `READY` -/
  ready : ∀ e : Nat, e < 6 → (Machine.Util.vget ms.threads e).ready = Core.bitOf i.tReady e
  /-- §4: `CORE` (thread `e` bound to this core) -/
  coreOf : ∀ e : Nat, e < 6 →
    ((Machine.Util.vget cv.threads e).core == coreNat c) = Core.bitOf (Core.mine c i) e
  /-- §4: `LINE` -/
  lineOf : ∀ e : Nat, e < 6 →
    (Machine.Util.vget cv.threads e).line = (Core.slice i.tLine (2 * e) 2).toNat
  /-- §4: `PC` -/
  pcOf : ∀ e : Nat, e < 6 →
    (Machine.Util.vget ms.threads e).pc.toNat = (Core.slice i.tPc (8 * e) 8).toNat
  /-- §4: watcher code `W0C` -/
  w0cOf : ∀ e : Nat, e < 6 →
    (Machine.Util.vget cv.threads e).w0c = (Core.slice i.tW0c (6 * e) 6).toNat
  /-- §4: watcher code `W1C` -/
  w1cOf : ∀ e : Nat, e < 6 →
    (Machine.Util.vget cv.threads e).w1c = (Core.slice i.tW1c (6 * e) 6).toNat
  /-- §4: watcher handler `W0H` -/
  w0hOf : ∀ e : Nat, e < 6 →
    (Machine.Util.vget cv.threads e).w0h = (Core.slice i.tW0h (8 * e) 8).toNat
  /-- §4: watcher handler `W1H` -/
  w1hOf : ∀ e : Nat, e < 6 →
    (Machine.Util.vget cv.threads e).w1h = (Core.slice i.tW1h (8 * e) 8).toNat
  /-- §5/§6: `RUN_global` -/
  run : ms.ctrl.run = i.runG
  /-- §5: the round-robin cursor is a thread index -/
  rrOk : s.rr.toNat < 6

/-- A thread's line is a line index (a 2-bit field of the cut). -/
theorem Rel.lineLt {c ms cv p s i} (h : Rel c ms cv p s i) (e : Nat) (he : e < 6) :
    (Machine.Util.vget cv.threads e).line < 4 := by
  rw [h.lineOf e he]
  exact (Core.slice i.tLine (2 * e) 2).isLt

/-- A watcher code is below 64 (a 6-bit field of the cut). -/
theorem Rel.w0cLt {c ms cv p s i} (h : Rel c ms cv p s i) (e : Nat) (he : e < 6) :
    (Machine.Util.vget cv.threads e).w0c < 64 := by
  rw [h.w0cOf e he]
  exact (Core.slice i.tW0c (6 * e) 6).isLt

/-- A watcher code is below 64 (a 6-bit field of the cut). -/
theorem Rel.w1cLt {c ms cv p s i} (h : Rel c ms cv p s i) (e : Nat) (he : e < 6) :
    (Machine.Util.vget cv.threads e).w1c < 64 := by
  rw [h.w1cOf e he]
  exact (Core.slice i.tW1c (6 * e) 6).isLt

/-! ## §7 guards: `cc` and `jc` -/

/-- §7: the move guard `C = G[IR.cond]` is the machine's guard read at `cond`. -/
theorem cc_bridge {c ms cv p s i} (h : Rel c ms cv p s i) :
    Core.cc s i = Machine.guardVal ms cv p s.xl.toNat
      (Machine.guardOp (Machine.insnField s.ir Machine.Tables.FIELD_cond)) := by
  rw [Core.cc, i_cond_eq s]
  simpa [ofNat_toNat_self] using h.guards s.xl.toNat s.xl.isLt _

/-- §7: the jump guard `JC` is the machine's jump guard, given that the machine's
generated table is the §7 list (`hJGTab`; see the notes). -/
theorem jc_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62) :
    Core.jc s i = Machine.guardVal ms cv p s.xl.toNat
      (Machine.jumpGuard (Machine.insnField s.ir Machine.Tables.FIELD_jcond)) := by
  rw [Core.jc, i_jcond_eq s, jumpGuardBit_eq _ _ (guardVec_bit62 i.guards i.gLine s.xl)]
  rw [show (BitVec.ofNat 5 (Machine.insnField s.ir Machine.Tables.FIELD_jcond)).toNat =
      Machine.insnField s.ir Machine.Tables.FIELD_jcond from by
    rw [BitVec.toNat_ofNat]
    have h5 : Machine.insnField s.ir Machine.Tables.FIELD_jcond < 2 ^ 5 :=
      insnField_lt s.ir Machine.Tables.FIELD_jcond
    simpa [Machine.Tables.FIELD_jcond] using Nat.mod_eq_of_lt h5]
  rw [Machine.jumpGuard, hJGTab]
  simpa [ofNat_toNat_self] using h.guards s.xl.toNat s.xl.isLt _

/-! ## §4/§5 dispatch: the circular scan -/

/-- `List.find?` only looks at the list's elements. -/
theorem find?_congr {α : Type} (l : List α) {p q : α → Bool}
    (h : ∀ a, a ∈ l → p a = q a) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha : p a = q a := h a (List.mem_cons_self ..)
    have has : ∀ b, b ∈ as → p b = q b := fun b hb => h b (List.mem_cons_of_mem _ hb)
    rw [List.find?_cons, List.find?_cons, ha]
    by_cases hq : q a = true
    · simp [hq]
    · simp [hq, ih has]

/-- The machine's dispatch scan is the cut's §5 circular scan: the first ready thread
bound to the core, from `RR` in circular order. -/
theorem pickThread_spec (candv : BitVec 6) (rr : BitVec 3) (hrr : rr.toNat < 6) :
    ((List.range 6).map (fun i => (rr.toNat + i) % 6)).find? (fun e => Core.bitOf candv e) =
      (if Core.winOf candv rr = 0 then none else some (Core.selIdx (Core.winOf candv rr)).toNat) := by
  revert hrr
  revert rr candv
  decide

/-- A non-zero candidate vector has a non-zero priority chain (and conversely). -/
theorem winOf_ne_zero (candv : BitVec 6) (rr : BitVec 3) :
    (Core.winOf candv rr = 0) = (candv = 0) := by
  revert candv rr
  decide

/-- The machine's `pickThread` is the cut's `dispThread` (as an `Option Nat`). -/
theorem pickThread_bridge {c ms cv p s i} (h : Rel c ms cv p s i) (hrun : i.runG = true) :
    Machine.pickThread ms cv (coreNat c) =
      (if Core.winOf (Core.cand c i) s.rr = 0 then none
       else some (Core.dispE c s i).toNat) := by
  unfold Machine.pickThread
  have hrr : (Machine.Util.vget ms.cores (coreNat c)).rr = s.rr := by
    rw [h.core]
    rfl
  rw [hrr]
  refine Eq.trans (find?_congr _ (fun e he => ?_)) (pickThread_spec _ _ h.rrOk)
  have he6 : e < 6 := by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    exact Nat.mod_lt _ (by decide)
  rw [h.coreOf e he6, h.ready e he6]
  simp only [Core.cand, hrun, ite_true]
  rw [bitOf_and, bitOf_and, bitOf_allOnes e he6]
  simp [Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

/-! ## §5 control: `taken`, `jmp`, `pse`, `load`, `free`, `disp`, `dispE` -/

/-- §5: `pause = IR[0]` is the machine's `pause` test. -/
theorem pause_bridge (s : Core.State) :
    Core.i_pause s = (Machine.insnField s.ir Machine.Tables.FIELD_pause == 1) := by
  rw [Core.i_pause, bitOf_eq_nbit]
  simp [Machine.Util.nbit, Machine.insnField, Machine.Tables.FIELD_pause, Machine.Util.nbits,
    Nat.shiftRight_eq_div_pow]

/-- §5: `taken` per `jmode` is the machine's `taken`. -/
theorem taken_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62) :
    Core.taken s i = (Machine.coreComb ms cv p (coreNat c) i.frz).taken := by
  simp only [Core.taken, Machine.coreComb, h.core]
  rw [beq_toNat, beq_toNat, beq_toNat, i_jmode_eq s]
  rw [jc_bridge h hJGTab]
  rfl

/-- §5: `jmp = XV && !pause && taken`. -/
theorem jmp_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62) :
    Core.jmp s i = (Machine.coreComb ms cv p (coreNat c) i.frz).jmp := by
  simp only [Core.jmp, Core.xa, Machine.coreComb, h.core, absCore, pause_bridge s,
    taken_bridge h hJGTab]

/-- §5: `pse = XV && pause`. -/
theorem pse_bridge {c ms cv p s i} (h : Rel c ms cv p s i) :
    Core.pse s i = (Machine.coreComb ms cv p (coreNat c) i.frz).pse := by
  simp only [Core.pse, Core.xa, Machine.coreComb, h.core, absCore, pause_bridge s]

/-- §5: `load = RV && !jmp && !pse`. -/
theorem load_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62) :
    Core.load s i = (Machine.coreComb ms cv p (coreNat c) i.frz).load := by
  simp only [Core.load, Core.ra, Machine.coreComb, h.core, absCore, jmp_bridge h hJGTab,
    pse_bridge h]
  simp [Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

/-- §5/§12.3: `free = pse || (!XV && !RV && !frz)`. -/
theorem free_bridge {c ms cv p s i} (h : Rel c ms cv p s i) :
    Core.free s i = (Machine.coreComb ms cv p (coreNat c) i.frz).free := by
  by_cases hf : i.frz = true
  · simp [Core.free, Core.pse, Core.xa, Machine.coreComb, h.core, absCore, pause_bridge s, hf]
  · have hf' : i.frz = false := by simpa using hf
    simp [Core.free, Core.pse, Core.xa, Machine.coreComb, h.core, absCore, pause_bridge s, hf']

/-- The priority chain of a zero candidate vector is zero. -/
theorem winOf_zero (rr : BitVec 3) : Core.winOf (0 : BitVec 6) rr = 0 := by
  simp [Core.winOf]

/-- Selecting from the zero chain gives thread 0. -/
theorem selIdx_zero : Core.selIdx (0 : BitVec 6) = 0 := by
  simp [Core.selIdx, Core.bitOf]

/-- The machine's dispatch `Option` is present exactly when the cut's candidate vector
is non-zero. -/
theorem pick_isSome (candv : BitVec 6) (rr : BitVec 3) (hrr : rr.toNat < 6) :
    (if Core.winOf candv rr = 0 then none
     else some (Core.selIdx (Core.winOf candv rr)).toNat).isSome = (candv != 0) := by
  revert hrr
  revert rr candv
  decide

/-- The machine's dispatch index is the cut's chain index (0 when the chain is zero). -/
theorem pick_getD (candv : BitVec 6) (rr : BitVec 3) (hrr : rr.toNat < 6) :
    (if Core.winOf candv rr = 0 then none
     else some (Core.selIdx (Core.winOf candv rr)).toNat).getD 0 =
      (Core.selIdx (Core.winOf candv rr)).toNat := by
  revert hrr
  revert rr candv
  decide

/-- §5: `disp` is "free, `RUN_global`, and a candidate". -/
theorem disp_bridge {c ms cv p s i} (h : Rel c ms cv p s i) :
    Core.disp c s i = (Machine.coreComb ms cv p (coreNat c) i.frz).disp := by
  have hdisp : (Machine.coreComb ms cv p (coreNat c) i.frz).disp =
      (if Core.free s i && i.runG then Machine.pickThread ms cv (coreNat c) else none).isSome := by
    simp [Machine.coreComb, h.core, absCore, h.run, free_bridge h]
  rw [hdisp, Core.disp]
  by_cases hf : Core.free s i = true
  · by_cases hrun : i.runG = true
    · rw [hf, hrun]
      simp only [Bool.and_true, ite_true]
      rw [pickThread_bridge (s := s) h hrun]
      have hg := (pick_isSome (Core.cand c i) s.rr h.rrOk).symm
      simp only [Core.dispE] at hg ⊢
      exact hg
    · have hrun' : i.runG = false := by simpa using hrun
      simp [hf, hrun', Core.cand, Core.winOf]
  · simp [hf]

/-- §5: with `disp` high, `disp_e` is the machine's `dispThread`.  (With `disp` low the
cut still shows the first candidate while the machine shows 0; `disp_e` is read only
under `disp`, see the notes.) -/
theorem dispE_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hd : Core.disp c s i = true) :
    Core.dispE c s i = Machine.Util.bv 3
      (Machine.coreComb ms cv p (coreNat c) i.frz).dispThread := by
  have hfree : Core.free s i = true := by
    by_cases hfx : Core.free s i = true
    · exact hfx
    · have hfx' : Core.free s i = false := by simpa using hfx
      rw [Core.disp, hfx'] at hd
      simp at hd
  have hcand : (Core.cand c i != 0) = true := by
    by_cases hcx : (Core.cand c i != 0) = true
    · exact hcx
    · have hcx' : (Core.cand c i != 0) = false := by simpa using hcx
      rw [Core.disp, hfree, hcx'] at hd
      simp at hd
  have hrun : i.runG = true := by
    by_cases hr : i.runG = true
    · exact hr
    · have hr' : i.runG = false := by simpa using hr
      simp [Core.cand, hr'] at hcand
  have hdisp : (Machine.coreComb ms cv p (coreNat c) i.frz).dispThread =
      (if Core.free s i && i.runG then Machine.pickThread ms cv (coreNat c) else none).getD 0 := by
    simp [Machine.coreComb, h.core, absCore, h.run, free_bridge h]
  rw [hdisp, Core.dispE, hfree, hrun]
  simp only [Bool.and_true, ite_true]
  rw [pickThread_bridge (s := s) h hrun]
  have hg := pick_getD (Core.cand c i) s.rr h.rrOk
  simp only [Core.dispE] at hg ⊢
  rw [hg]
  exact (bv_toNat _).symm

/-! ## §5 thread slots and the watcher address

`dLine`, `dPc`, `dW0c` … select the dispatched thread's slot from the cut's input
vectors; the machine reads the same fields from its thread file through `Rel`.  These
equalities are used only under `disp`, which is where §5 reads them. -/

/-- The one-hot chain selects the slot of its own index. -/
theorem selSlot_of_onehot {w : Nat} (v : BitVec (6 * w)) (win : BitVec 6) (j : Nat) (hj : j < 6)
    (hb : ∀ k : Nat, k < 6 → Core.bitOf win k = (k == j)) :
    Core.selSlot v win = Core.slice v (j * w) w := by
  have h0 : Core.bitOf win 0 = (0 == j) := hb 0 (by omega)
  have h1 : Core.bitOf win 1 = (1 == j) := hb 1 (by omega)
  have h2 : Core.bitOf win 2 = (2 == j) := hb 2 (by omega)
  have h3 : Core.bitOf win 3 = (3 == j) := hb 3 (by omega)
  have h4 : Core.bitOf win 4 = (4 == j) := hb 4 (by omega)
  have h5 : Core.bitOf win 5 = (5 == j) := hb 5 (by omega)
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Core.selSlot, h0, h1, h2, h3, h4, h5, Core.slice]

/-- The priority chain is one-hot at its own index (`Fin` form for `decide`). -/
theorem winOf_onehot_fin (candv : BitVec 6) (rr : BitVec 3) (hrr : rr.toNat < 6)
    (hc : candv ≠ 0) :
    ∀ k : Fin 6, Core.bitOf (Core.winOf candv rr) k.val =
      (k.val == (Core.selIdx (Core.winOf candv rr)).toNat) := by
  revert hrr
  revert candv rr
  decide

/-- The priority chain is one-hot at its own index. -/
theorem winOf_onehot (candv : BitVec 6) (rr : BitVec 3) (hrr : rr.toNat < 6) (hc : candv ≠ 0) :
    ∀ k : Nat, k < 6 →
      Core.bitOf (Core.winOf candv rr) k = (k == (Core.selIdx (Core.winOf candv rr)).toNat) := by
  intro k hk
  have h := winOf_onehot_fin candv rr hrr hc ⟨k, hk⟩
  simpa using h

/-- `selSlot` at the priority chain is the slot of the dispatched thread. -/
theorem selSlot_bridge {w : Nat} (v : BitVec (6 * w)) (candv : BitVec 6) (rr : BitVec 3)
    (hrr : rr.toNat < 6) (hc : candv ≠ 0) :
    Core.selSlot v (Core.winOf candv rr) =
      Core.slice v ((Core.selIdx (Core.winOf candv rr)).toNat * w) w :=
  selSlot_of_onehot v _ _ (Core.selIdx_toNat_lt_six _ (Core.winOf_atmost _ _))
    (winOf_onehot candv rr hrr hc)

/-- The `disp` decision supplies a non-zero candidate vector. -/
theorem cand_ne_zero_of_disp {c ms cv p s i} (h : Rel c ms cv p s i)
    (hd : Core.disp c s i = true) : Core.cand c i ≠ 0 := by
  by_cases hc : Core.cand c i = 0
  · have hc' : (Core.cand c i != 0) = false := by simp [hc]
    rw [Core.disp, hc'] at hd
    simp at hd
  · exact hc

/-- §5: the executing line `XL'` on dispatch is the dispatched thread's `LINE`. -/
theorem dLine_bridge {c ms cv p s i} (h : Rel c ms cv p s i) (hd : Core.disp c s i = true) :
    Core.dLine c s i = BitVec.ofNat 2
      (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).line := by
  have hc := cand_ne_zero_of_disp h hd
  have he : (Core.dispE c s i).toNat < 6 := Core.dispE_toNat_le_five c s i
  rw [Core.dLine, selSlot_bridge _ _ _ h.rrOk hc]
  rw [show (Core.selIdx (Core.winOf (Core.cand c i) s.rr)).toNat * 2 =
      2 * (Core.dispE c s i).toNat from by
    rw [Core.dispE, Nat.mul_comm]]
  exact bv2_eq_of_toNat _ _ (h.lineLt _ he) (h.lineOf _ he).symm

/-- §5: the dispatched thread's `PC`. -/
theorem dPc_bridge {c ms cv p s i} (h : Rel c ms cv p s i) (hd : Core.disp c s i = true) :
    (Core.dPc c s i).toNat = (Machine.Util.vget ms.threads (Core.dispE c s i).toNat).pc.toNat := by
  have hc := cand_ne_zero_of_disp h hd
  have he : (Core.dispE c s i).toNat < 6 := Core.dispE_toNat_le_five c s i
  rw [Core.dPc, selSlot_bridge _ _ _ h.rrOk hc,
    show (Core.selIdx (Core.winOf (Core.cand c i) s.rr)).toNat * 8 =
      8 * (Core.dispE c s i).toNat from by
      rw [Core.dispE, Nat.mul_comm]]
  exact (h.pcOf _ he).symm

/-- §5: the dispatched thread's `W0C`. -/
theorem dW0c_bridge {c ms cv p s i} (h : Rel c ms cv p s i) (hd : Core.disp c s i = true) :
    (Core.dW0c c s i).toNat = (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w0c := by
  have hc := cand_ne_zero_of_disp h hd
  have he : (Core.dispE c s i).toNat < 6 := Core.dispE_toNat_le_five c s i
  rw [Core.dW0c, selSlot_bridge _ _ _ h.rrOk hc,
    show (Core.selIdx (Core.winOf (Core.cand c i) s.rr)).toNat * 6 =
      6 * (Core.dispE c s i).toNat from by
      rw [Core.dispE, Nat.mul_comm]]
  exact (h.w0cOf _ he).symm

/-- §5: the dispatched thread's `W1C`. -/
theorem dW1c_bridge {c ms cv p s i} (h : Rel c ms cv p s i) (hd : Core.disp c s i = true) :
    (Core.dW1c c s i).toNat = (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w1c := by
  have hc := cand_ne_zero_of_disp h hd
  have he : (Core.dispE c s i).toNat < 6 := Core.dispE_toNat_le_five c s i
  rw [Core.dW1c, selSlot_bridge _ _ _ h.rrOk hc,
    show (Core.selIdx (Core.winOf (Core.cand c i) s.rr)).toNat * 6 =
      6 * (Core.dispE c s i).toNat from by
      rw [Core.dispE, Nat.mul_comm]]
  exact (h.w1cOf _ he).symm

/-- §5: the dispatched thread's `W0H`. -/
theorem dW0h_bridge {c ms cv p s i} (h : Rel c ms cv p s i) (hd : Core.disp c s i = true) :
    (Core.dW0h c s i).toNat = (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w0h := by
  have hc := cand_ne_zero_of_disp h hd
  have he : (Core.dispE c s i).toNat < 6 := Core.dispE_toNat_le_five c s i
  rw [Core.dW0h, selSlot_bridge _ _ _ h.rrOk hc,
    show (Core.selIdx (Core.winOf (Core.cand c i) s.rr)).toNat * 8 =
      8 * (Core.dispE c s i).toNat from by
      rw [Core.dispE, Nat.mul_comm]]
  exact (h.w0hOf _ he).symm

/-- §5: the dispatched thread's `W1H`. -/
theorem dW1h_bridge {c ms cv p s i} (h : Rel c ms cv p s i) (hd : Core.disp c s i = true) :
    (Core.dW1h c s i).toNat = (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w1h := by
  have hc := cand_ne_zero_of_disp h hd
  have he : (Core.dispE c s i).toNat < 6 := Core.dispE_toNat_le_five c s i
  rw [Core.dW1h, selSlot_bridge _ _ _ h.rrOk hc,
    show (Core.selIdx (Core.winOf (Core.cand c i) s.rr)).toNat * 8 =
      8 * (Core.dispE c s i).toNat from by
      rw [Core.dispE, Nat.mul_comm]]
  exact (h.w1hOf _ he).symm

/-- §7: watcher 0 fires as the machine's `W0C[e] != 0 && G_e[W0C[e]]`. -/
theorem watcher0_bridge {c ms cv p s i} (h : Rel c ms cv p s i) (hd : Core.disp c s i = true) :
    Core.watcher0 c s i =
      ((Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w0c != 0 &&
        Machine.guardVal ms cv p (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).line
          (Machine.guardOp (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w0c)) := by
  have he : (Core.dispE c s i).toNat < 6 := Core.dispE_toNat_le_five c s i
  rw [Core.watcher0, bne_zero_toNat, dW0c_bridge h hd]
  rw [show Core.bitOf (Core.guardVec i.guards i.gLine (Core.dLine c s i))
        (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w0c =
      Machine.guardVal ms cv p (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).line
        (Machine.guardOp (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w0c) from by
    rw [dLine_bridge h hd]
    exact h.guards _ (h.lineLt _ he) _]

/-- §7: watcher 1 fires as the machine's `W1C[e] != 0 && G_e[W1C[e]]`. -/
theorem watcher1_bridge {c ms cv p s i} (h : Rel c ms cv p s i) (hd : Core.disp c s i = true) :
    Core.watcher1 c s i =
      ((Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w1c != 0 &&
        Machine.guardVal ms cv p (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).line
          (Machine.guardOp (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w1c)) := by
  have he : (Core.dispE c s i).toNat < 6 := Core.dispE_toNat_le_five c s i
  rw [Core.watcher1, bne_zero_toNat, dW1c_bridge h hd]
  rw [show Core.bitOf (Core.guardVec i.guards i.gLine (Core.dLine c s i))
        (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w1c =
      Machine.guardVal ms cv p (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).line
        (Machine.guardOp (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w1c) from by
    rw [dLine_bridge h hd]
    exact h.guards _ (h.lineLt _ he) _]

/-- §5: the watcher address `d` is the machine's `watcherAddr` of the dispatched thread. -/
theorem dpc_bridge {c ms cv p s i} (h : Rel c ms cv p s i) (hd : Core.disp c s i = true) :
    (Core.dpc c s i).toNat = Machine.watcherAddr ms cv p (Core.dispE c s i).toNat := by
  rw [Core.dpc, Machine.watcherAddr, watcher0_bridge h hd, watcher1_bridge h hd]
  simp only [toNat_ite]
  by_cases hw0 : ((Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w0c != 0 &&
      Machine.guardVal ms cv p (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).line
        (Machine.guardOp (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w0c)) = true
  · simp only [hw0, ite_true, dW0h_bridge h hd]
  · simp only [hw0, Bool.false_eq_true, ite_false]
    by_cases hw1 : ((Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w1c != 0 &&
        Machine.guardVal ms cv p (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).line
          (Machine.guardOp (Machine.Util.vget cv.threads (Core.dispE c s i).toNat).w1c)) = true
    · simp only [hw1, ite_true, dW1h_bridge h hd]
    · simp only [hw1, Bool.false_eq_true, ite_false, dPc_bridge h hd]

/-- `dispThread` is a thread index (the scan's elements are `(RR + i) mod 6`). -/
theorem pickThread_lt (ms : Machine.State) (cv : Machine.CfgView) (c : Nat) :
    ∀ e, Machine.pickThread ms cv c = some e → e < 6 := by
  intro e he
  simp only [Machine.pickThread] at he
  have hmem : e ∈ (List.range 6).map
      (fun i => ((Machine.Util.vget ms.cores c).rr.toNat + i) % 6) :=
    List.mem_of_find?_eq_some he
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hmem
  exact Nat.mod_lt _ (by decide)

/-- The machine's dispatched thread index is below 6. -/
theorem dispThread_lt (ms : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (c : Nat) (frozen : Bool) : (Machine.coreComb ms cv p c frozen).dispThread < 6 := by
  simp only [Machine.coreComb]
  split
  · cases hpt : Machine.pickThread ms cv c with
    | none => simp [hpt]
    | some e => simpa [hpt] using pickThread_lt ms cv c e hpt
  · exact Nat.zero_lt_succ 5

/-- The machine's `dispAddr` is the watcher address of `dispThread` when it dispatches. -/
theorem comb_dispAddr (ms : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (c : Nat) (frozen : Bool) :
    (Machine.coreComb ms cv p c frozen).dispAddr =
      (if (Machine.coreComb ms cv p c frozen).disp then
        Machine.watcherAddr ms cv p (Machine.coreComb ms cv p c frozen).dispThread else 0) := by
  simp [Machine.coreComb]

/-- With `disp` high, the machine's `dispThread` is the cut's `disp_e` as a `Nat`. -/
theorem dispThread_bridge {c ms cv p s i} (h : Rel c ms cv p s i) (hd : Core.disp c s i = true) :
    (Machine.coreComb ms cv p (coreNat c) i.frz).dispThread = (Core.dispE c s i).toNat := by
  have hb := dispE_bridge h hd
  have ht : (Machine.coreComb ms cv p (coreNat c) i.frz).dispThread < 8 := by
    have := dispThread_lt ms cv p (coreNat c) i.frz
    omega
  have hbv : (Machine.Util.bv 3 (Machine.coreComb ms cv p (coreNat c) i.frz).dispThread).toNat =
      (Machine.coreComb ms cv p (coreNat c) i.frz).dispThread := by
    simp [Machine.Util.bv, Nat.mod_eq_of_lt ht]
  rw [hb, hbv]

/-- §5: `npc = taken ? IR.imm : FPC`. -/
theorem npc_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62) :
    (Core.npc s i).toNat = (Machine.coreComb ms cv p (coreNat c) i.frz).npc := by
  rw [Core.npc, toNat_ite]
  simp only [Machine.coreComb, h.core, absCore, taken_bridge h hJGTab, i_imm_eq s]

/-! ## §5 fetch -/

/-- §5: `fetch = some address` exactly when a fetch is enabled, and the address is
`fetch_addr`. -/
theorem fetch_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62) :
    (Machine.coreComb ms cv p (coreNat c) i.frz).fetch =
      (if Core.fetchEn c s i = true then some (Core.fetchAddr c s i).toNat else none) := by
  have hfetch : (Machine.coreComb ms cv p (coreNat c) i.frz).fetch =
      (if (Machine.coreComb ms cv p (coreNat c) i.frz).jmp then
        some (Machine.insnField s.ir Machine.Tables.FIELD_imm)
       else if (Machine.coreComb ms cv p (coreNat c) i.frz).load then
        some ((s.fpc.toNat + 1) % 256)
       else if (Machine.coreComb ms cv p (coreNat c) i.frz).disp then
        some (Machine.coreComb ms cv p (coreNat c) i.frz).dispAddr else none) := by
    simp [Machine.coreComb, h.core, absCore]
  rw [hfetch, ← jmp_bridge h hJGTab, ← load_bridge h hJGTab, ← disp_bridge h]
  by_cases hj : Core.jmp s i = true
  · have hfe : Core.fetchEn c s i = true := by simp [Core.fetchEn, hj]
    simp only [hfe, ite_true]
    simp [Core.fetchAddr, hj, toNat_ite, i_imm_eq s]
  · by_cases hl : Core.load s i = true
    · have hfe : Core.fetchEn c s i = true := by simp [Core.fetchEn, hj, hl]
      simp only [hfe, ite_true]
      simp [Core.fetchAddr, hj, hl, toNat_ite, BitVec.toNat_add, Nat.reducePow]
    · by_cases hd : Core.disp c s i = true
      · have hfe : Core.fetchEn c s i = true := by simp [Core.fetchEn, hj, hl, hd]
        simp only [hfe, ite_true]
        simp only [Core.fetchAddr, hj, hl, hd, Bool.false_eq_true, ite_false]
        rw [comb_dispAddr, ← disp_bridge h, hd, dispThread_bridge h hd, dpc_bridge h hd]
        simp
      · have hfe : Core.fetchEn c s i = false := by simp [Core.fetchEn, hj, hl, hd]
        simp only [hfe, Bool.false_eq_true, ite_false]
        simp [Core.fetchAddr, hj, hl, hd]

/-- §5: `fetch_en = jmp || load || disp`. -/
theorem fetchEn_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62) :
    Core.fetchEn c s i = (Machine.coreComb ms cv p (coreNat c) i.frz).fetch.isSome := by
  rw [fetch_bridge h hJGTab]
  by_cases hf : Core.fetchEn c s i = true <;> simp [hf]

/-! ## §6 the move bus (bridge-side encoding)

The machine's enabled moves are a `List.filterMap`; its `Option.match` is a generated
auxiliary (`List.foldl_filterMap.match_1`) that the kernel does not rewrite, so the
machine's bus words are encoded here from the list's projections.  `moveAt`/`mvEnOf`/
`mvSrcOf`/`mvDstOf`/`mvDataOf` are those encodings; the section "the move bus: the
packed words" below proves the machine's `moves` is the cut's three bus slots
(`coreComb_moves`) and compares the packed words slot by slot (`moves_bridge`). -/

/-- The machine's enabled move of index `m`, when there is one. -/
def moveAt (cb : Machine.CoreComb) (m : Nat) : Option Machine.Move :=
  cb.moves.find? (fun mv => mv.idx == m)

/-- The machine's `mv_en` word. -/
def mvEnOf (cb : Machine.CoreComb) : BitVec 3 :=
  Core.boolMask 0 (cb.moves.any (fun mv => mv.idx == 0)) |||
    Core.boolMask 1 (cb.moves.any (fun mv => mv.idx == 1)) |||
    Core.boolMask 2 (cb.moves.any (fun mv => mv.idx == 2))

/-- The source code of the machine's move `m` (0 when there is no move). -/
def mvSrcOf (cb : Machine.CoreComb) (m : Nat) : Nat :=
  (moveAt cb m).map (fun mv => mv.src) |>.getD 0

/-- The destination code of the machine's move `m` (0 when there is no move). -/
def mvDstOf (cb : Machine.CoreComb) (m : Nat) : Nat :=
  (moveAt cb m).map (fun mv => mv.dst) |>.getD 0

/-- The data byte of the machine's move `m` (0 when there is no move). -/
def mvDataOf (cb : Machine.CoreComb) (m : Nat) : Nat :=
  (moveAt cb m).map (fun mv => mv.v) |>.getD 0

/-- §5/§6: the cut's move guard test is the machine's enable test. -/
theorem moveGuardOk_bridge {c ms cv p s i} (h : Rel c ms cv p s i) (m : Nat) (gm : Nat)
    (hg : (Core.i_g s m).toNat = gm) :
    Core.moveGuardOk (Core.i_g s m) (Core.cc s i) =
      (gm == Machine.Tables.MGUARD_always ||
        (gm == Machine.Tables.MGUARD_if && Machine.guardVal ms cv p s.xl.toNat
          (Machine.guardOp (Machine.insnField s.ir Machine.Tables.FIELD_cond))) ||
        (gm == Machine.Tables.MGUARD_ifnot && !Machine.guardVal ms cv p s.xl.toNat
          (Machine.guardOp (Machine.insnField s.ir Machine.Tables.FIELD_cond)))) := by
  rw [Core.moveGuardOk, cc_bridge h, beq_toNat, beq_toNat, beq_toNat, hg]
  simp [Core.GD_ALWAYS, Core.GD_IF, Core.GD_IFNOT, Machine.Tables.MGUARD_always,
    Machine.Tables.MGUARD_if, Machine.Tables.MGUARD_ifnot]

/-! ## §6 the move bus: the packed `mv_en`/`mv_src`/`mv_dst`/`mv_data` words -/

/-- The guard field of move slot `m`. -/
def slotGuard (m : Nat) : Nat × Nat :=
  match m with
  | 0 => Machine.Tables.FIELD_m0_guard
  | 1 => Machine.Tables.FIELD_m1_guard
  | _ => Machine.Tables.FIELD_m2_guard

/-- The source field of move slot `m`. -/
def slotSrc (m : Nat) : Nat × Nat :=
  match m with
  | 0 => Machine.Tables.FIELD_m0_src
  | 1 => Machine.Tables.FIELD_m1_src
  | _ => Machine.Tables.FIELD_m2_src

/-- The destination field of move slot `m`. -/
def slotDst (m : Nat) : Nat × Nat :=
  match m with
  | 0 => Machine.Tables.FIELD_m0_dst
  | 1 => Machine.Tables.FIELD_m1_dst
  | _ => Machine.Tables.FIELD_m2_dst

/-- The machine's move-enable test of slot `m`: the §5 guard code of the slot. -/
def moveEn (ms : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (s : Core.State) (m : Nat) : Bool :=
  let gm := Machine.insnField s.ir (slotGuard m)
  let cnd := Machine.guardVal ms cv p s.xl.toNat
    (Machine.guardOp (Machine.insnField s.ir Machine.Tables.FIELD_cond))
  gm == Machine.Tables.MGUARD_always || (gm == Machine.Tables.MGUARD_if && cnd) ||
    (gm == Machine.Tables.MGUARD_ifnot && !cnd)

/-- The machine's move of slot `m` (its fields, whether enabled or not). -/
def moveVal (ms : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (s : Core.State) (c : Nat) (m : Nat) : Machine.Move :=
  let ir := s.ir
  let xl := s.xl.toNat
  let xt := s.xt.toNat
  let si := Machine.insnField ir (slotSrc m)
  { core := c, idx := m, src := si, dst := Machine.insnField ir (slotDst m),
    v := Machine.srcVal ms cv p xl (Machine.insnField ir Machine.Tables.FIELD_imm)
      (Machine.srcOp si),
    thread := xt, line := xl, armed := (Machine.Util.vget ms.threads xt).armed }

/-- The machine's candidate move of slot `m`, as `coreComb` builds it before the
`filterMap`. -/
def moveCand (ms : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (s : Core.State) (c : Nat) (m : Nat) : Option Machine.Move :=
  if moveEn ms cv p s m then some (moveVal ms cv p s c m) else none

theorem range3 : List.range 3 = [0, 1, 2] := by decide

/-- The machine's `moves` list is the three candidates of slots `0, 1, 2` filtered. -/
theorem coreComb_moves {c : Bool} {ms : Machine.State} {cv : Machine.CfgView} {p : Machine.PinView}
    {s : Core.State} {i : Core.Input} (h : Rel c ms cv p s i) :
    (Machine.coreComb ms cv p (coreNat c) i.frz).moves =
      (if (!(Core.xa s i)) = true then []
       else (List.range 3).filterMap (moveCand ms cv p s (coreNat c))) := by
  simp only [Machine.coreComb]
  rw [show Machine.Tables.N_MOVES = 3 from rfl, range3, h.core]
  dsimp only [absCore]
  rfl

/-- On an active cycle the machine's `moves` is exactly the cut's three bus slots. -/
theorem coreComb_moves_of_xa {c : Bool} {ms : Machine.State} {cv : Machine.CfgView}
    {p : Machine.PinView} {s : Core.State} {i : Core.Input} (h : Rel c ms cv p s i)
    (hxa : Core.xa s i = true) :
    (Machine.coreComb ms cv p (coreNat c) i.frz).moves =
      (List.range 3).filterMap (moveCand ms cv p s (coreNat c)) := by
  rw [coreComb_moves h, ite_eq_right (by simp [hxa])]

/-- On an idle cycle the machine has no moves (the cut's `mv_en` is 0 too). -/
theorem coreComb_moves_of_idle {c : Bool} {ms : Machine.State} {cv : Machine.CfgView}
    {p : Machine.PinView} {s : Core.State} {i : Core.Input} (h : Rel c ms cv p s i)
    (hxa : Core.xa s i = false) :
    (Machine.coreComb ms cv p (coreNat c) i.frz).moves = [] := by
  rw [coreComb_moves h, ite_eq_left (by simp [hxa])]

/-- The cut's guard code of slot `m` is the machine's guard field of the slot. -/
theorem i_g_slot (s : Core.State) (m : Nat) (hm : m < 3) :
    (Core.i_g s m).toNat = Machine.insnField s.ir (slotGuard m) := by
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
  · exact i_g_eq_0 s
  · exact i_g_eq_1 s
  · exact i_g_eq_2 s

/-- The cut's source code of slot `m` is the machine's source field of the slot. -/
theorem i_s_slot (s : Core.State) (m : Nat) (hm : m < 3) :
    (Core.i_s s m).toNat = Machine.insnField s.ir (slotSrc m) := by
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
  · exact i_s_eq_0 s
  · exact i_s_eq_1 s
  · exact i_s_eq_2 s

/-- The cut's destination code of slot `m` is the machine's destination field. -/
theorem i_d_slot (s : Core.State) (m : Nat) (hm : m < 3) :
    (Core.i_d s m).toNat = Machine.insnField s.ir (slotDst m) := by
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
  · exact i_d_eq_0 s
  · exact i_d_eq_1 s
  · exact i_d_eq_2 s

/-- §5: the cut's per-move enable of slot `m` is `xa` and the machine's enable test. -/
theorem mvEnAt_bridge {c : Bool} {ms : Machine.State} {cv : Machine.CfgView} {p : Machine.PinView}
    {s : Core.State} {i : Core.Input} (h : Rel c ms cv p s i) (m : Nat) (hm : m < 3) :
    Core.mvEnAt c s i m = (Core.xa s i && moveEn ms cv p s m) := by
  unfold Core.mvEnAt
  rw [moveGuardOk_bridge h m (Machine.insnField s.ir (slotGuard m)) (i_g_slot s m hm)]
  rfl

theorem moveCand_isSome {ms : Machine.State} {cv : Machine.CfgView} {p : Machine.PinView}
    {s : Core.State} {c m : Nat} :
    (moveCand ms cv p s c m).isSome = moveEn ms cv p s m := by
  unfold moveCand
  cases moveEn ms cv p s m <;> rfl

theorem moveVal_idx {ms : Machine.State} {cv : Machine.CfgView} {p : Machine.PinView}
    {s : Core.State} {c m : Nat} : (moveVal ms cv p s c m).idx = m := rfl

theorem moveVal_src {ms : Machine.State} {cv : Machine.CfgView} {p : Machine.PinView}
    {s : Core.State} {c m : Nat} :
    (moveVal ms cv p s c m).src = Machine.insnField s.ir (slotSrc m) := rfl

theorem moveVal_dst {ms : Machine.State} {cv : Machine.CfgView} {p : Machine.PinView}
    {s : Core.State} {c m : Nat} :
    (moveVal ms cv p s c m).dst = Machine.insnField s.ir (slotDst m) := rfl

theorem moveVal_v {ms : Machine.State} {cv : Machine.CfgView} {p : Machine.PinView}
    {s : Core.State} {c m : Nat} :
    (moveVal ms cv p s c m).v = Machine.srcVal ms cv p s.xl.toNat
      (Machine.insnField s.ir Machine.Tables.FIELD_imm)
      (Machine.srcOp (Machine.insnField s.ir (slotSrc m))) := rfl

theorem moveCand_eq_some {ms : Machine.State} {cv : Machine.CfgView} {p : Machine.PinView}
    {s : Core.State} {c m : Nat} {mv : Machine.Move}
    (h : moveCand ms cv p s c m = some mv) : mv = moveVal ms cv p s c m := by
  unfold moveCand at h
  by_cases he : moveEn ms cv p s m = true
  · simp [he] at h
    exact h.symm
  · simp [he] at h

theorem moveCand_map_src {ms : Machine.State} {cv : Machine.CfgView} {p : Machine.PinView}
    {s : Core.State} {c m : Nat} :
    ((moveCand ms cv p s c m).map (fun mv => mv.src)).getD 0 =
      if moveEn ms cv p s m then (moveVal ms cv p s c m).src else 0 := by
  unfold moveCand
  cases moveEn ms cv p s m <;> rfl

theorem moveCand_map_dst {ms : Machine.State} {cv : Machine.CfgView} {p : Machine.PinView}
    {s : Core.State} {c m : Nat} :
    ((moveCand ms cv p s c m).map (fun mv => mv.dst)).getD 0 =
      if moveEn ms cv p s m then (moveVal ms cv p s c m).dst else 0 := by
  unfold moveCand
  cases moveEn ms cv p s m <;> rfl

theorem moveCand_map_v {ms : Machine.State} {cv : Machine.CfgView} {p : Machine.PinView}
    {s : Core.State} {c m : Nat} :
    ((moveCand ms cv p s c m).map (fun mv => mv.v)).getD 0 =
      if moveEn ms cv p s m then (moveVal ms cv p s c m).v else 0 := by
  unfold moveCand
  cases moveEn ms cv p s m <;> rfl

/-- The machine's enabled entry of slot `m` is the slot's candidate. -/
theorem moveAt_eq_cand {c : Bool} {ms : Machine.State} {cv : Machine.CfgView} {p : Machine.PinView}
    {s : Core.State} {i : Core.Input} (h : Rel c ms cv p s i) (hxa : Core.xa s i = true)
    (m : Nat) (hm : m < 3) :
    moveAt (Machine.coreComb ms cv p (coreNat c) i.frz) m = moveCand ms cv p s (coreNat c) m := by
  unfold moveAt
  rw [coreComb_moves_of_xa h hxa, range3]
  have h3 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases h3 with rfl | rfl | rfl <;>
    (cases e0 : moveEn ms cv p s 0 <;> cases e1 : moveEn ms cv p s 1 <;>
      cases e2 : moveEn ms cv p s 2 <;>
      simp [moveCand, moveVal, e0, e1, e2, List.filterMap_cons, List.filterMap_nil])

/-- `any` is the `isSome` of `find?`. -/
theorem any_eq_find?_isSome {α : Type} (l : List α) (p : α → Bool) :
    l.any p = (l.find? p).isSome := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.any_cons, List.find?_cons]
    cases hp : p a <;> simp [hp, ih]

/-- Bit `k < 3` of the packed enable word. -/
theorem bitOf_boolMask3 (b0 b1 b2 : Bool) (k : Nat) (hk : k < 3) :
    Core.bitOf (Core.boolMask (w := 3) 0 b0 ||| Core.boolMask (w := 3) 1 b1 |||
      Core.boolMask (w := 3) 2 b2) k =
      (match k with | 0 => b0 | 1 => b1 | _ => b2) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
    (cases b0 <;> cases b1 <;> cases b2 <;> rfl)

/-- The cut's `mv_en` bit `m` is the cut's per-move enable of slot `m`. -/
theorem mvEn_bit {c : Bool} {s : Core.State} {i : Core.Input} (m : Nat) (hm : m < 3) :
    Core.bitOf (Core.out c s i).mvEn m = Core.mvEnAt c s i m := by
  simp only [Core.out]
  rw [bitOf_boolMask3 (Core.mvEnAt c s i 0) (Core.mvEnAt c s i 1) (Core.mvEnAt c s i 2) m hm]
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl <;> rfl

/-- The machine's `mv_en` word bit `m` is "slot `m` is in the move list". -/
theorem mvEnOf_bit {cb : Machine.CoreComb} (m : Nat) (hm : m < 3) :
    Core.bitOf (mvEnOf cb) m = cb.moves.any (fun mv => mv.idx == m) := by
  unfold mvEnOf
  rw [bitOf_boolMask3 _ _ _ m hm]
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl <;> rfl

/-! ## Packing three fields into one word -/

theorem decide_and_if {p : Prop} [Decidable p] (t : Bool) :
    (decide p && t) = (if p then t else false) := by
  by_cases h : p <;> simp [h]

theorem decide_and_not_decide_and_if {p q : Prop} [Decidable p] [Decidable q] (t : Bool) :
    (decide p && !decide q && t) = (if p ∧ ¬q then t else false) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem not_decide_and_if {p : Prop} [Decidable p] (t : Bool) :
    (!decide p && t) = (if p then false else t) := by
  by_cases h : p <;> simp [h]

/-- Three `w`-bit fields packed low-to-high into `3w` bits (the cut's bus words). -/
def pack3 {w : Nat} (x0 x1 x2 : BitVec w) : BitVec (3 * w) :=
  BitVec.setWidth (3 * w) x0 ||| BitVec.shiftLeft (BitVec.setWidth (3 * w) x1) w |||
    BitVec.shiftLeft (BitVec.setWidth (3 * w) x2) (2 * w)

theorem pack3_slice0 {w : Nat} (hw : 0 < w) (x0 x1 x2 : BitVec w) :
    Core.slice (pack3 x0 x1 x2) 0 w = x0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [pack3, Core.slice, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  simp only [decide_and_not_decide_and_if, decide_and_if, not_decide_and_if]
  by_cases hk : k < w
  · have hk3 : k < 3 * w := by omega
    have hk2 : k < 2 * w := by omega
    simp [hk, hk3, hk2]
  · exact fun hc => absurd hc hk

theorem pack3_slice1 {w : Nat} (hw : 0 < w) (x0 x1 x2 : BitVec w) :
    Core.slice (pack3 x0 x1 x2) w w = x1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [pack3, Core.slice, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  simp only [decide_and_not_decide_and_if, decide_and_if, not_decide_and_if]
  by_cases hk : k < w
  · have hk3 : k < 3 * w := by omega
    have hk2 : k < 2 * w := by omega
    have hwk3 : w + k < 3 * w := by omega
    have hwk2 : w + k < 2 * w := by omega
    have hwk1 : ¬ (w + k < w) := by omega
    have h0 : x0.getLsbD (w + k) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp [hk, hk3, hk2, hwk3, hwk2, hwk1, h0]
  · exact fun hc => absurd hc hk

theorem pack3_slice2 {w : Nat} (hw : 0 < w) (x0 x1 x2 : BitVec w) :
    Core.slice (pack3 x0 x1 x2) (2 * w) w = x2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [pack3, Core.slice, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  simp only [decide_and_not_decide_and_if, decide_and_if, not_decide_and_if]
  by_cases hk : k < w
  · have h1 : 2 * w + k < 3 * w := by omega
    have h2 : ¬ (2 * w + k < w) := by omega
    have h3 : ¬ (2 * w + k < 2 * w) := by omega
    have h4 : 2 * w + k - w = w + k := by omega
    have h5 : 2 * w + k - 2 * w = k := by omega
    have h6 : x0.getLsbD (2 * w + k) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    have h7 : x1.getLsbD (w + k) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp [hk, h1, h2, h3, h4, h5, h6, h7]
  · exact fun hc => absurd hc hk

theorem mvSrc_field {c : Bool} {s : Core.State} {i : Core.Input} (m : Nat) (hm : m < 3) :
    (Core.slice (Core.out c s i).mvSrc (6 * m) 6).toNat = (Core.i_s s m).toNat := by
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
  · simp only [Core.out]
    exact congrArg BitVec.toNat (pack3_slice0 (by decide : 0 < 6) _ _ _)
  · simp only [Core.out]
    exact congrArg BitVec.toNat (pack3_slice1 (by decide : 0 < 6) _ _ _)
  · simp only [Core.out]
    exact congrArg BitVec.toNat (pack3_slice2 (by decide : 0 < 6) _ _ _)

theorem mvDst_field {c : Bool} {s : Core.State} {i : Core.Input} (m : Nat) (hm : m < 3) :
    (Core.slice (Core.out c s i).mvDst (6 * m) 6).toNat = (Core.i_d s m).toNat := by
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
  · simp only [Core.out]
    exact congrArg BitVec.toNat (pack3_slice0 (by decide : 0 < 6) _ _ _)
  · simp only [Core.out]
    exact congrArg BitVec.toNat (pack3_slice1 (by decide : 0 < 6) _ _ _)
  · simp only [Core.out]
    exact congrArg BitVec.toNat (pack3_slice2 (by decide : 0 < 6) _ _ _)

theorem mvData_field {c : Bool} {s : Core.State} {i : Core.Input} (m : Nat) (hm : m < 3) :
    (Core.slice (Core.out c s i).mvData (8 * m) 8).toNat = (Core.srcByte s i m).toNat := by
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
  · simp only [Core.out]
    exact congrArg BitVec.toNat (pack3_slice0 (by decide : 0 < 8) _ _ _)
  · simp only [Core.out]
    exact congrArg BitVec.toNat (pack3_slice1 (by decide : 0 < 8) _ _ _)
  · simp only [Core.out]
    exact congrArg BitVec.toNat (pack3_slice2 (by decide : 0 < 8) _ _ _)

/-- The cut's data byte of slot `m` is the source byte at the slot's source code. -/
theorem srcByte_index {s : Core.State} {i : Core.Input} (m : Nat) :
    (Core.srcByte s i m).toNat =
      (Core.slice (Core.srcVec s i) (8 * (Core.i_s s m).toNat) 8).toNat := by
  simp only [Core.srcByte]
  have h1 : (BitVec.setWidth 32 (Core.i_s s m)).toNat = (Core.i_s s m).toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by have := (Core.i_s s m).isLt; omega)
  have hmul : BitVec.toNat (8 * BitVec.setWidth 32 (Core.i_s s m)) = 8 * (Core.i_s s m).toNat := by
    rw [BitVec.toNat_mul, h1]
    have h8 : (8 : BitVec 32).toNat = 8 := rfl
    rw [h8]
    exact Nat.mod_eq_of_lt (by have := (Core.i_s s m).isLt; omega)
  rw [hmul]

/-! ## The move-bus bridge -/

/-- §6: the cut's packed move bus is the machine's enabled move list, slot by slot. -/
theorem moves_bridge {c : Bool} {ms : Machine.State} {cv : Machine.CfgView}
    {p : Machine.PinView} {s : Core.State} {i : Core.Input} (h : Rel c ms cv p s i)
    (m : Nat) (hm : m < 3) :
    (Core.bitOf (Core.out c s i).mvEn m =
        (moveAt (Machine.coreComb ms cv p (coreNat c) i.frz) m).isSome) ∧
    (Core.bitOf (mvEnOf (Machine.coreComb ms cv p (coreNat c) i.frz)) m =
        (moveAt (Machine.coreComb ms cv p (coreNat c) i.frz) m).isSome) ∧
    (∀ mv, moveAt (Machine.coreComb ms cv p (coreNat c) i.frz) m = some mv →
      mv.idx = m ∧
      mv.src = (Core.slice (Core.out c s i).mvSrc (6 * m) 6).toNat ∧
      mv.dst = (Core.slice (Core.out c s i).mvDst (6 * m) 6).toNat ∧
      mv.v = (Core.slice (Core.out c s i).mvData (8 * m) 8).toNat) ∧
    (Core.bitOf (Core.out c s i).mvEn m = true →
      mvSrcOf (Machine.coreComb ms cv p (coreNat c) i.frz) m =
          (Core.slice (Core.out c s i).mvSrc (6 * m) 6).toNat ∧
      mvDstOf (Machine.coreComb ms cv p (coreNat c) i.frz) m =
          (Core.slice (Core.out c s i).mvDst (6 * m) 6).toNat ∧
      mvDataOf (Machine.coreComb ms cv p (coreNat c) i.frz) m =
          (Core.slice (Core.out c s i).mvData (8 * m) 8).toNat) ∧
    (Core.bitOf (Core.out c s i).mvEn m = false →
      mvSrcOf (Machine.coreComb ms cv p (coreNat c) i.frz) m = 0 ∧
      mvDstOf (Machine.coreComb ms cv p (coreNat c) i.frz) m = 0 ∧
      mvDataOf (Machine.coreComb ms cv p (coreNat c) i.frz) m = 0) := by
  by_cases hxa : Core.xa s i = true
  · have hmoves : (Machine.coreComb ms cv p (coreNat c) i.frz).moves =
        (List.range 3).filterMap (moveCand ms cv p s (coreNat c)) := by
      rw [coreComb_moves h, ite_eq_right (by simp [hxa])]
    have hfind : moveAt (Machine.coreComb ms cv p (coreNat c) i.frz) m =
        moveCand ms cv p s (coreNat c) m := moveAt_eq_cand h hxa m hm
    have hbit : Core.bitOf (Core.out c s i).mvEn m = moveEn ms cv p s m := by
      rw [mvEn_bit m hm, mvEnAt_bridge h m hm, hxa]
      rfl
    have hiss : (moveAt (Machine.coreComb ms cv p (coreNat c) i.frz) m).isSome =
        moveEn ms cv p s m := by
      rw [hfind, moveCand_isSome]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hbit, ← hiss]
    · rw [mvEnOf_bit m hm, any_eq_find?_isSome]
      rfl
    · intro mv hmv
      have hc : mv = moveVal ms cv p s (coreNat c) m :=
        moveCand_eq_some (by rw [← hfind]; exact hmv)
      subst hc
      refine ⟨moveVal_idx, ?_, ?_, ?_⟩
      · rw [moveVal_src, mvSrc_field m hm]
        exact (i_s_slot s m hm).symm
      · rw [moveVal_dst, mvDst_field m hm]
        exact (i_d_slot s m hm).symm
      · rw [moveVal_v, mvData_field m hm, srcByte_index m,
          show Machine.insnField s.ir (slotSrc m) = (Core.i_s s m).toNat
            from (i_s_slot s m hm).symm]
        exact (h.srcs (Core.i_s s m).toNat).symm
    · intro hprem
      have hmv : moveEn ms cv p s m = true := by rw [← hbit]; exact hprem
      have hs1 : mvSrcOf (Machine.coreComb ms cv p (coreNat c) i.frz) m =
          (moveVal ms cv p s (coreNat c) m).src := by
        simp only [mvSrcOf, hfind, moveCand, hmv]
        rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hs1, moveVal_src, mvSrc_field m hm]
        exact (i_s_slot s m hm).symm
      · have hs2 : mvDstOf (Machine.coreComb ms cv p (coreNat c) i.frz) m =
            (moveVal ms cv p s (coreNat c) m).dst := by
          simp only [mvDstOf, hfind, moveCand, hmv]
          rfl
        rw [hs2, moveVal_dst, mvDst_field m hm]
        exact (i_d_slot s m hm).symm
      · have hs3 : mvDataOf (Machine.coreComb ms cv p (coreNat c) i.frz) m =
            (moveVal ms cv p s (coreNat c) m).v := by
          simp only [mvDataOf, hfind, moveCand, hmv]
          rfl
        rw [hs3, moveVal_v, mvData_field m hm, srcByte_index m,
          show Machine.insnField s.ir (slotSrc m) = (Core.i_s s m).toNat
            from (i_s_slot s m hm).symm]
        exact (h.srcs (Core.i_s s m).toNat).symm
    · intro hprem
      have hmv : moveEn ms cv p s m = false := by rw [← hbit]; exact hprem
      have hs : moveAt (Machine.coreComb ms cv p (coreNat c) i.frz) m = none := by
        simp only [hfind, moveCand, hmv]
        rfl
      refine ⟨?_, ?_, ?_⟩ <;> simp only [mvSrcOf, mvDstOf, mvDataOf, hs] <;> rfl
  · have hmoves : (Machine.coreComb ms cv p (coreNat c) i.frz).moves = [] := by
      rw [coreComb_moves h, ite_eq_left (by simp [hxa])]
    have hbit : Core.bitOf (Core.out c s i).mvEn m = false := by
      have hxaf : Core.xa s i = false := by
        by_cases h : Core.xa s i = true
        · exact absurd h hxa
        · simpa using h
      rw [mvEn_bit m hm, mvEnAt_bridge h m hm, hxaf]
      rfl
    have hfind : moveAt (Machine.coreComb ms cv p (coreNat c) i.frz) m = none := by
      unfold moveAt
      rw [hmoves]
      rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hbit, hfind]
      rfl
    · rw [mvEnOf_bit m hm, hmoves]
      unfold moveAt
      rw [hmoves]
      rfl
    · intro mv hmv
      rw [hfind] at hmv
      exact absurd hmv (by simp)
    · intro hprem
      rw [hbit] at hprem
      exact absurd hprem (by simp)
    · intro _
      refine ⟨?_, ?_, ?_⟩ <;> simp only [mvSrcOf, mvDstOf, mvDataOf, hfind] <;> rfl

/-! ## The next state (§5, §12.3) -/

/-- `RR' = (e + 1) mod 6` in the machine's form. -/
theorem rrNext_eq (e : BitVec 3) (he : e.toNat < 6) :
    Core.rrNext e = BitVec.ofNat 3 ((e.toNat + 1) % 6) := by
  revert he
  revert e
  decide

/-- §5: `XV' = reset ? 0 : frozen ? XV : load`. -/
theorem xv_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (hreset : i.resetN = true) (word : Option Nat) :
    (Core.next c s i).xv = (Machine.coreNext (absCore i.rdata s) cv
      (Machine.coreComb ms cv p (coreNat c) i.frz) word i.frz).xv := by
  cases hfz : i.frz
  · have hlb := load_bridge (i := i) h hJGTab
    rw [hfz] at hlb
    simp [Core.next, Machine.coreNext, hreset, hfz, absCore, hlb]
  · simp [Core.next, Machine.coreNext, hreset, hfz, absCore]

/-- §5: `RV' = reset ? 0 : frozen ? RV : fetch_en`. -/
theorem rv_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (hreset : i.resetN = true) (word : Option Nat) :
    (Core.next c s i).rv = (Machine.coreNext (absCore i.rdata s) cv
      (Machine.coreComb ms cv p (coreNat c) i.frz) word i.frz).rv := by
  cases hfz : i.frz
  · have hjb := jmp_bridge (i := i) h hJGTab
    have hlb := load_bridge (i := i) h hJGTab
    have hdb := disp_bridge (i := i) h
    rw [hfz] at hjb hlb hdb
    simp [Core.next, Machine.coreNext, hreset, hfz, absCore, Core.fetchEn, hjb, hlb, hdb]
  · simp [Core.next, Machine.coreNext, hreset, hfz, absCore]

/-- A `match` on an `Option` is `map` and `getD`. -/
theorem match_some_getD {α β : Type} (x : Option α) (f : α → β) (d : β) :
    (match x with | some a => f a | none => d) = (x.map f).getD d := by
  cases x <;> rfl

/-- §5: `FPC' = reset ? 0 : frozen ? FPC : fetch address`. -/
theorem fpc_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (hreset : i.resetN = true) (word : Option Nat) :
    (Core.next c s i).fpc = (Machine.coreNext (absCore i.rdata s) cv
      (Machine.coreComb ms cv p (coreNat c) i.frz) word i.frz).fpc := by
  cases hfz : i.frz
  · have hfb := fetch_bridge (i := i) h hJGTab
    rw [hfz] at hfb
    simp only [Core.next, Machine.coreNext, hreset, absCore, Bool.false_eq_true, ite_false,
      ite_true, Bool.true_and, hfb]
    by_cases he : Core.fetchEn c s i = true <;> simp [he, bv_toNat] <;> simp_all
  · simp [Core.next, Machine.coreNext, hreset, hfz, absCore]

/-- §5: `XT' = reset ? 0 : frozen ? XT : disp ? disp_e : XT`. -/
theorem xt_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (hreset : i.resetN = true) (word : Option Nat) :
    (Core.next c s i).xt = (Machine.coreNext (absCore i.rdata s) cv
      (Machine.coreComb ms cv p (coreNat c) i.frz) word i.frz).xt := by
  cases hfz : i.frz
  · have hdb := disp_bridge (i := i) h
    rw [hfz] at hdb
    simp only [Core.next, Machine.coreNext, hreset, absCore, Bool.false_eq_true, ite_false,
      ite_true, Bool.true_and]
    rw [← hdb]
    by_cases hd : Core.disp c s i = true
    · have hde := dispE_bridge (i := i) h hd
      rw [hfz] at hde
      simp [hd, hde] <;> simp_all
    · simp [hd]
  · simp [Core.next, Machine.coreNext, hreset, hfz, absCore]

/-- §5: `XL' = reset ? 0 : frozen ? XL : disp ? LINE[e] : XL`. -/
theorem xl_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (hreset : i.resetN = true) (word : Option Nat) :
    (Core.next c s i).xl = (Machine.coreNext (absCore i.rdata s) cv
      (Machine.coreComb ms cv p (coreNat c) i.frz) word i.frz).xl := by
  cases hfz : i.frz
  · have hdb := disp_bridge (i := i) h
    rw [hfz] at hdb
    simp only [Core.next, Machine.coreNext, hreset, absCore, Bool.false_eq_true, ite_false,
      ite_true, Bool.true_and]
    rw [← hdb]
    by_cases hd : Core.disp c s i = true
    · have hdt := dispThread_bridge (i := i) h hd
      have hdl := dLine_bridge (i := i) h hd
      rw [hfz] at hdt
      simp [hd, hdt, hdl, Machine.Util.bv] <;> simp_all
    · simp [hd]
  · simp [Core.next, Machine.coreNext, hreset, hfz, absCore]

/-- §5: `RR' = reset ? 0 : frozen ? RR : disp ? (e + 1) mod 6 : RR`. -/
theorem rr_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (hreset : i.resetN = true) (word : Option Nat) :
    (Core.next c s i).rr = (Machine.coreNext (absCore i.rdata s) cv
      (Machine.coreComb ms cv p (coreNat c) i.frz) word i.frz).rr := by
  cases hfz : i.frz
  · have hdb := disp_bridge (i := i) h
    rw [hfz] at hdb
    simp only [Core.next, Machine.coreNext, hreset, absCore, Bool.false_eq_true, ite_false,
      ite_true, Bool.true_and]
    rw [← hdb]
    by_cases hd : Core.disp c s i = true
    · have hdt := dispThread_bridge (i := i) h hd
      rw [hfz] at hdt
      simp [hd, hdt, rrNext_eq (Core.dispE c s i) (Core.dispE_toNat_le_five c s i),
        Machine.Tables.N_THREADS, Machine.Util.bv] <;> simp_all
    · simp [hd]
  · simp [Core.next, Machine.coreNext, hreset, hfz, absCore]

/-- §5/§12.3: `IR' = frozen ? IR : rdata` on a load (or a frozen) cycle; the cut also
captures without a load (the one reading difference). -/
theorem ir_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (hreset : i.resetN = true) (word : Option Nat)
    (hld : Core.load s i = true ∨ i.frz = true) :
    (Core.next c s i).ir = (Machine.coreNext (absCore i.rdata s) cv
      (Machine.coreComb ms cv p (coreNat c) i.frz) word i.frz).ir := by
  cases hfz : i.frz
  · have hl : Core.load s i = true := by
      rcases hld with hl | hf'
      · exact hl
      · rw [hfz] at hf'; exact absurd hf' (by decide)
    have hlb := load_bridge (i := i) h hJGTab
    rw [hfz] at hlb
    simp only [Core.next, Machine.coreNext, hreset, hfz, absCore, Bool.false_eq_true,
      ite_false, ite_true, Bool.true_and, ← hlb, hl]
  · simp [Core.next, Machine.coreNext, hreset, hfz, absCore]

/-! ## The assembled bridges -/

/-- The whole cut transition is the machine's `coreNext`, on an active cycle, when the
machine reloads `IR` (or holds on a frozen cycle).  `mout` after the step is the word
the machine presented (`word`), which the caller relates to the next cycle's `rdata`
(the program-memory contract); the `absCore` argument records that. -/
theorem step_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62)
    (hreset : i.resetN = true) (hld : Core.load s i = true ∨ i.frz = true)
    (word : Option Nat) :
    ((Machine.coreNext (absCore i.rdata s) cv
        (Machine.coreComb ms cv p (coreNat c) i.frz) word i.frz).xv = (Core.next c s i).xv) ∧
    ((Machine.coreNext (absCore i.rdata s) cv
        (Machine.coreComb ms cv p (coreNat c) i.frz) word i.frz).ir = (Core.next c s i).ir) ∧
    ((Machine.coreNext (absCore i.rdata s) cv
        (Machine.coreComb ms cv p (coreNat c) i.frz) word i.frz).rv = (Core.next c s i).rv) ∧
    ((Machine.coreNext (absCore i.rdata s) cv
        (Machine.coreComb ms cv p (coreNat c) i.frz) word i.frz).fpc = (Core.next c s i).fpc) ∧
    ((Machine.coreNext (absCore i.rdata s) cv
        (Machine.coreComb ms cv p (coreNat c) i.frz) word i.frz).xt = (Core.next c s i).xt) ∧
    ((Machine.coreNext (absCore i.rdata s) cv
        (Machine.coreComb ms cv p (coreNat c) i.frz) word i.frz).xl = (Core.next c s i).xl) ∧
    ((Machine.coreNext (absCore i.rdata s) cv
        (Machine.coreComb ms cv p (coreNat c) i.frz) word i.frz).rr = (Core.next c s i).rr) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (xv_bridge h hJGTab hreset word).symm
  · exact (ir_bridge h hJGTab hreset word hld).symm
  · exact (rv_bridge h hJGTab hreset word).symm
  · exact (fpc_bridge h hJGTab hreset word).symm
  · exact (xt_bridge h hJGTab hreset word).symm
  · exact (xl_bridge h hJGTab hreset word).symm
  · exact (rr_bridge h hJGTab hreset word).symm

/-- §12.3: a frozen cycle holds the machine's core state (its `coreNext` frozen
branch). -/
theorem frz_hold_bridge {c ms cv p s i} (h : Rel c ms cv p s i) (word : Option Nat) :
    Machine.coreNext (absCore i.rdata s) cv
        (Machine.coreComb ms cv p (coreNat c) true) word true =
      absCore i.rdata s := rfl

/-- Reset: the cut clears the five reset registers and still captures `rdata` into
`IR` (the RTL's unconditional capture); the machine has no per-core reset input (the
chip's `Chip.resetStep` clears the register file). -/
theorem reset_bridge {c ms cv p s i} (h : Rel c ms cv p s i) (hreset : i.resetN = false) :
    (Core.next c s i).xv = false ∧ (Core.next c s i).rv = false ∧
      (Core.next c s i).fpc = 0 ∧ (Core.next c s i).xt = 0 ∧ (Core.next c s i).xl = 0 ∧
      (Core.next c s i).rr = 0 ∧
      (Core.next c s i).ir = (if i.frz then s.ir else i.rdata) := by
  simp [Core.next, hreset]

/-- The outputs of the cut are the machine's `CoreComb` readings.  `fetch_addr` is
meaningful only when `fetch_en` is high (the machine then has `some` address);
`disp_e` only when `disp_o` is high. -/
theorem out_bridge {c ms cv p s i} (h : Rel c ms cv p s i)
    (hJGTab : ∀ n : Nat, Machine.Util.jumpGuardIdx.getD n
        Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62) :
    (Core.out c s i).fetchEn = (Machine.coreComb ms cv p (coreNat c) i.frz).fetch.isSome ∧
    (Core.out c s i).pauseO = (Machine.coreComb ms cv p (coreNat c) i.frz).pse ∧
    (Core.out c s i).npcO.toNat = (Machine.coreComb ms cv p (coreNat c) i.frz).npc ∧
    (Core.out c s i).dispO = (Machine.coreComb ms cv p (coreNat c) i.frz).disp ∧
    (Core.out c s i).xtO = s.xt ∧
    (Core.out c s i).xlO = s.xl ∧
    (Core.out c s i).dbgXv = s.xv ∧
    (Core.out c s i).dbgRv = s.rv ∧
    (Core.out c s i).dbgFpc = s.fpc ∧
    (∀ a, (Machine.coreComb ms cv p (coreNat c) i.frz).fetch = some a →
      (Core.out c s i).fetchAddr.toNat = a) ∧
    (Core.disp c s i = true →
      (Core.out c s i).dispE = Machine.Util.bv 3
        (Machine.coreComb ms cv p (coreNat c) i.frz).dispThread) := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact fetchEn_bridge h hJGTab
  · exact pse_bridge h
  · exact npc_bridge h hJGTab
  · exact disp_bridge h
  · intro a ha
    rw [fetch_bridge h hJGTab] at ha
    by_cases he : Core.fetchEn c s i = true
    · simp only [he, ite_true, Option.some.injEq] at ha
      exact ha
    · simp [he] at ha
  · exact fun hd => dispE_bridge h hd

/-! ## Reading differences (witnesses) -/

/-- SPEC §5 captures `IR` only on `load`; the cut (like `md2_core.v`) captures it on
every unfrozen cycle.  This is the divergence, with explicit hypotheses. -/
theorem ir_no_load_diverges (c : Bool) (s : Core.State) (i : Core.Input)
    (cs : Machine.CoreSt) (cv : Machine.CfgView) (cb : Machine.CoreComb) (word : Option Nat)
    (hload : cb.load = false) (hir : cs.ir = s.ir) (hrd : i.rdata ≠ s.ir) (hfrz : i.frz = false) :
    (Core.next c s i).ir ≠ (Machine.coreNext cs cv cb word false).ir := by
  simp only [Core.next, Machine.coreNext, hfrz, Bool.false_eq_true, ite_false, hload, hir]
  exact hrd

/-- A non-dispatching core has `dispThread = 0` in the machine (`pick = none`). -/
theorem dispThread_zero_of_not_disp (ms : Machine.State) (cv : Machine.CfgView)
    (p : Machine.PinView) (c : Nat) (frozen : Bool)
    (hd : (Machine.coreComb ms cv p c frozen).disp = false) :
    (Machine.coreComb ms cv p c frozen).dispThread = 0 := by
  simp only [Machine.coreComb] at hd ⊢
  by_cases hp : ((!frozen && ((Machine.Util.vget ms.cores c).xv && !frozen &&
      Machine.insnField (Machine.Util.vget ms.cores c).ir Machine.Tables.FIELD_pause == 1 ||
      !(Machine.Util.vget ms.cores c).xv && !(Machine.Util.vget ms.cores c).rv)) &&
      ms.ctrl.run) = true
  · rw [if_pos hp] at hd
    cases hpt : Machine.pickThread ms cv c with
    | none => simp [hpt]
    | some e => rw [hpt] at hd; simp at hd
  · simp only [hp, Bool.false_eq_true, ite_false, Option.getD_none]

/-- A concrete busy cycle with a ready thread bound to the core. -/
def wState : Core.State :=
  { xv := true, rv := true, fpc := 0, xt := 0, xl := 0, rr := 0, ir := 0 }

/-- The witness's input bundle: thread 1 is ready and bound to core 0. -/
def wInput : Core.Input :=
  { resetN := true, frz := false, runG := true, rdata := 0, tReady := 2, tCore := 0,
    tLine := 0, tPc := 0, tW0c := 0, tW1c := 0, tW0h := 0, tW1h := 0, guards := 0,
    gLine := 0, srcs := 0, lIn := 0, lCap := 0 }

/-- The cut's `disp_e` is the first candidate even when `disp_o` is low, while the
machine's `dispThread` is 0 then (`dispThread_zero_of_not_disp`): a don't-care
difference outside dispatch (§5 reads `disp_e` only on `disp`). -/
theorem dispE_no_disp_witness :
    Core.disp false wState wInput = false ∧ Core.dispE false wState wInput = 1 := by
  decide

end Metronome.Bridge.Core