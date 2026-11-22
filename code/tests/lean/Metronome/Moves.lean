import Metronome.CoreCtl

/-!
# Move resolution: write groups, conflicts, the pick and the source side effects

This module is the independent specification of the chip-top move resolution in
[project.v](../../../../src/project.v) (the `write groups` block, the series of
`pick(...)` uses and the two sticky flags), written from SPEC_V2 §6 (write
groups and conflicts), §6.3 (the streams' source side effects), §9 (`CTRL`) and
the destination and source tables of `code/md2/machine.json`.

The RTL side lives in `MovesEquivalence.lean.in`, which `moves_check.py` fills
from the elaborated netlist.  Every definition here is stated over the six move
slots, `slot k = 3 * core + move`, so "lowest (core, move index)" is "lowest
slot index".

What the specification says (SPEC_V2 §6):

* the destination ports are partitioned into write groups
  (`machine.WRITE_GROUPS`); `L.SYM` covers the three symbol ports of one line,
  `T.STOP` is per thread, and `NULL` has no group;
* if two or more enabled moves target one group in a cycle, sticky `CONFLICT`
  becomes set and only the write with the lowest `(core, move index)` takes
  effect;
* source side effects happen only for enabled moves: reading `HOST.IN` clears
  `INV`, and reading `P0.D` while `P0.RDY == 0` sets sticky `MEMHAZ`.

## Cycle boundary

Everything here is combinational, plus the two sticky registers (`CONFLICT`,
`MEMHAZ`), whose next state is `stickyNext`.  Register values are free
parameters of the step theorems, as in `Metronome.CoreCtl`.  `CONFLICT` is the
`CTRL.STICKY` bit 0 and is cleared by a host write of that byte with bit 0 set;
the address decode is the host-map cut's and is re-established here from the
elaborated strobe.
-/

set_option autoImplicit false
set_option exponentiation.threshold 1024

namespace Metronome.Moves

open Metronome.CoreCtl (bitAt slice chain GroupWord makeWord)

/-! ## Destination codes, source codes and the group table -/

/-- `DG_NONE`: the group code of a destination with no write group (`NULL`). -/
def dgNone : BitVec 5 := 31

/-- `DG_L_SYM`: the line symbol group; its key also holds the executing line. -/
def dgLSym : BitVec 5 := 0

/-- `DG_T_STOP`: the thread stop group; its key also holds the thread. -/
def dgTStop : BitVec 5 := 1

/-- `S_P0_D` (`md2_defs.vh`): the pointer data source. -/
def srcP0D : BitVec 6 := 33

/-- `S_HOST_IN` (`md2_defs.vh`): the host mailbox source. -/
def srcHostIn : BitVec 6 := 38

/-- The 64-code destination → write-group table of `machine.WRITE_GROUPS`,
transcribed from `code/md2/machine.json` (`dst` order, `write_groups` order).
Entry `d` is bits `5*d +: 5`; codes 61..63 are unused and map to `DG_NONE`.
`moves_check.py --check` regenerates the table from `machine.json` and fails if
this literal drifts. -/
def dgMapLiteral : BitVec 320 :=
  0xffff9ce717b569394e53946318c21083def7c1ee6b1cd639ac5a9284a0e62906318c63188410001f

/-- One 5-bit table entry, `tab[5*d +: 5]`, in the shift form the RTL's
`$shiftx` has. -/
def dgLookupAt (tab : BitVec 320) (d : BitVec 6) : BitVec 5 :=
  BitVec.truncate 5 (BitVec.ushiftRight tab (5 * d.toNat))

/-- The write group of destination code `d` (`DG_MAP[5*d +: 5]`). -/
def dgTable (d : BitVec 6) : BitVec 5 := dgLookupAt dgMapLiteral d

/-- `NULL` has no group (SPEC_V2 §6). -/
theorem dgTable_null : dgTable 0 = dgNone := by decide

/-- The unused destination codes have no group either. -/
theorem dgTable_61 : dgTable 61 = dgNone := by decide

theorem dgTable_62 : dgTable 62 = dgNone := by decide

theorem dgTable_63 : dgTable 63 = dgNone := by decide

/-- The six group lookups of a 320-bit table, packed as the RTL's
`grp_v = {grp[5], …, grp[0]}` in the shift-and-OR form the assembled bus has. -/
def mapOfWith (tab : BitVec 320) (dst : BitVec 36) : BitVec 30 :=
  (BitVec.setWidth 30 (dgLookupAt tab (slice dst 0 6))) |||
  (BitVec.shiftLeft (BitVec.setWidth 30 (dgLookupAt tab (slice dst 6 6))) 5) |||
  (BitVec.shiftLeft (BitVec.setWidth 30 (dgLookupAt tab (slice dst 12 6))) 10) |||
  (BitVec.shiftLeft (BitVec.setWidth 30 (dgLookupAt tab (slice dst 18 6))) 15) |||
  (BitVec.shiftLeft (BitVec.setWidth 30 (dgLookupAt tab (slice dst 24 6))) 20) |||
  (BitVec.shiftLeft (BitVec.setWidth 30 (dgLookupAt tab (slice dst 30 6))) 25)

/-- The six group lookups `grp[k] = DG_MAP[5*c_dst[6k +: 6] +: 5]`, packed as the
RTL's `grp_v = {grp[5], …, grp[0]}`. -/
def mapOf (dst : BitVec 36) : BitVec 30 := mapOfWith dgMapLiteral dst

/-! ## The six move slots -/

/-- One move at the write-group arbiter, as the core pipeline presents it and as
SPEC_V2 §6 keys it.  `line` is the executing core's `xl` and `thread` its `xt`;
both key only the `L.SYM` and `T.STOP` groups. -/
structure Slot where
  /-- `mv_en`: the move's guard held this cycle. -/
  enabled : Bool
  /-- The move's write group, from `DG_MAP`. -/
  group : BitVec 5
  /-- `c_dst`: the destination code. -/
  dst : BitVec 6
  /-- `c_dat`: the write data. -/
  data : BitVec 8
  /-- The executing core's line (`xl` of that core). -/
  line : BitVec 2
  /-- The executing core's thread (`xt` of that core). -/
  thread : BitVec 3
  deriving DecidableEq, Repr

/-- The six moves of a cycle, in priority order: core 0 moves 0..2 then core 1.
A structure, like `CoreCtl.Bundle`, so each slot is an ordinary projection. -/
structure Bundle where
  m0 : Slot
  m1 : Slot
  m2 : Slot
  m3 : Slot
  m4 : Slot
  m5 : Slot

/-- Slot `k` of the bundle. -/
def Bundle.get (b : Bundle) : Nat → Slot
  | 0 => b.m0
  | 1 => b.m1
  | 2 => b.m2
  | 3 => b.m3
  | 4 => b.m4
  | _ => b.m5

/-- The bundle carried by the elaborated nets `mv_en`, `grp_v`, `c_dst`,
`c_dat`, `xl` and `xt`.  Slot `k` is core `k / 3`, move `k % 3`; its line and
thread are that core's `xl` and `xt`, exactly the RTL's `xl[2*(k/3) +: 2]` and
`xt[3*(k/3) +: 3]`. -/
def bundleOf (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) (dat : BitVec 48)
    (xl : BitVec 4) (xt : BitVec 6) : Bundle where
  m0 := ⟨bitAt en 0, slice grp 0 5, slice dst 0 6, slice dat 0 8, slice xl 0 2, slice xt 0 3⟩
  m1 := ⟨bitAt en 1, slice grp 5 5, slice dst 6 6, slice dat 8 8, slice xl 0 2, slice xt 0 3⟩
  m2 := ⟨bitAt en 2, slice grp 10 5, slice dst 12 6, slice dat 16 8, slice xl 0 2, slice xt 0 3⟩
  m3 := ⟨bitAt en 3, slice grp 15 5, slice dst 18 6, slice dat 24 8, slice xl 2 2, slice xt 3 3⟩
  m4 := ⟨bitAt en 4, slice grp 20 5, slice dst 24 6, slice dat 32 8, slice xl 2 2, slice xt 3 3⟩
  m5 := ⟨bitAt en 5, slice grp 25 5, slice dst 30 6, slice dat 40 8, slice xl 2 2, slice xt 3 3⟩

/-- The bundle built from the buses, without destination or data: the arbitration
result does not depend on them. -/
def arbBundle (en : BitVec 6) (grp : BitVec 30) (xl : BitVec 4) (xt : BitVec 6) : Bundle :=
  bundleOf en grp 0 0 xl xt

/-- Slot order is `(core, move index)` order: core `k / 3`, move `k % 3`. -/
theorem slot_order (k : Nat) (hk : k < 6) :
    k / 3 = (if k < 3 then 0 else 1) ∧ k % 3 = (if k < 3 then k else k - 3) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## Validity, keys and blocking

SPEC_V2 §6: `NULL` has no group, so an enabled move whose destination is `NULL`
is not a move at all.  A move's *key* is its group, except that `L.SYM` is keyed
by the executing line and `T.STOP` by the thread ("`T.STOP` (per thread)",
"`L.SYM` (the three symbol ports of one line, resolved to the executing
thread's line)"). -/

/-- The move is enabled and has a write group. -/
def validAt (m : Slot) : Bool := m.enabled && !(m.group == dgNone)

/-- Two moves contend for the same write port: same group, and for the keyed
groups the same line (`L.SYM`) or thread (`T.STOP`). -/
def sameKey (a b : Slot) : Bool :=
  (a.group == b.group) && (!(a.group == dgLSym) || (a.line == b.line)) &&
    (!(a.group == dgTStop) || (a.thread == b.thread))

theorem beq_comm_5 (a b : BitVec 5) : (a == b) = (b == a) := by bv_decide

theorem beq_comm_2 (a b : BitVec 2) : (a == b) = (b == a) := by bv_decide

theorem beq_comm_3 (a b : BitVec 3) : (a == b) = (b == a) := by bv_decide

/-- `sameKey` is symmetric. -/
theorem sameKey_comm (a b : Slot) : sameKey a b = sameKey b a := by
  simp only [sameKey]
  bv_decide

/-- A move contends with itself. -/
theorem sameKey_self (a : Slot) : sameKey a a = true := by
  simp [sameKey]

/-- Some earlier slot is a valid move with the same key: the RTL's `|blk`. -/
def blocked (b : Bundle) (k : Nat) : Bool :=
  (List.range k).any (fun j => validAt (b.get j) && sameKey (b.get j) (b.get k))

/-- The move wins its key: it is valid and no earlier slot is a valid move with
the same key.  SPEC_V2 §6's "only the write with the lowest (core, move index)
takes effect". -/
def winAt (b : Bundle) (k : Nat) : Bool := validAt (b.get k) && !blocked b k

/-- The conflict event `|(mv_valid & ~mv_win)`: some valid move did not win. -/
def conflictEv (b : Bundle) : Bool :=
  (List.range 6).any (fun k => validAt (b.get k) && !winAt b k)

/-- Two valid moves in one cycle with the same key. -/
def pairSameKey (b : Bundle) : Bool :=
  (List.range 6).any (fun k =>
    validAt (b.get k) && (List.range k).any (fun j =>
      validAt (b.get j) && sameKey (b.get j) (b.get k)))

/-! ### The winner is exactly "valid and no earlier valid same-key slot" -/

/-- `!b = true` is `b = false`. -/
theorem not_eq_true_eq_false (b : Bool) : ((!b) = true) = (b = false) := by
  cases b <;> simp

/-- `!b = false` is `b = true`. -/
theorem not_eq_false_eq_true (b : Bool) : ((!b) = false) = (b = true) := by
  cases b <;> simp

/-- From `p j` being false, `p j = true` is impossible. -/
theorem eq_false_of_not_eq_true {b : Bool} (h : ¬(b = true)) : b = false := by
  cases b <;> simp_all

/-- `winAt` is exactly the SPEC_V2 §6 rule. -/
theorem winAt_spec (b : Bundle) (k : Nat) :
    winAt b k = true ↔
      validAt (b.get k) = true ∧
        ∀ j, j < k → (validAt (b.get j) && sameKey (b.get j) (b.get k)) = false := by
  unfold winAt blocked
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hv, hany⟩
    have hany' : ((List.range k).any
        (fun j => validAt (b.get j) && sameKey (b.get j) (b.get k))) = false := by
      have := hany
      rwa [not_eq_true_eq_false] at this
    refine ⟨hv, fun j hj => ?_⟩
    exact eq_false_of_not_eq_true
      ((List.any_eq_false.1 hany') j (by simpa [List.mem_range] using hj))
  · rintro ⟨hv, h⟩
    refine ⟨hv, ?_⟩
    rw [not_eq_true_eq_false]
    refine List.any_eq_false.2 (fun j hj => ?_)
    have := h j (by simpa [List.mem_range] using hj)
    simp [this]

/-- A winner is valid. -/
theorem winAt_valid {b : Bundle} {k : Nat} (h : winAt b k = true) :
    validAt (b.get k) = true :=
  ((winAt_spec b k).1 h).1

/-- A winner has no earlier valid move with the same key. -/
theorem winAt_no_earlier {b : Bundle} {k : Nat} (h : winAt b k = true)
    {j : Nat} (hj : j < k) : (validAt (b.get j) && sameKey (b.get j) (b.get k)) = false :=
  ((winAt_spec b k).1 h).2 j hj

/-- A valid move that is blocked is not a winner. -/
theorem winAt_false_of_blocked {b : Bundle} {k : Nat}
    (hb : blocked b k = true) : winAt b k = false := by
  unfold winAt
  rw [hb, Bool.not_true, Bool.and_false]

/-- A valid move that nothing earlier blocks wins. -/
theorem winAt_true_of_unblocked {b : Bundle} {k : Nat} (hv : validAt (b.get k) = true)
    (hb : blocked b k = false) : winAt b k = true := by
  unfold winAt
  rw [hv, hb, Bool.not_false, Bool.and_true]

/-- `blocked` is exactly "some earlier slot is a valid move with this key". -/
theorem blocked_spec (b : Bundle) (k : Nat) :
    blocked b k = true ↔ ∃ j, j < k ∧ validAt (b.get j) = true ∧
      sameKey (b.get j) (b.get k) = true := by
  unfold blocked
  rw [List.any_eq_true]
  simp only [List.mem_range, Bool.and_eq_true]

/-! ### At most one winner per key -/

/-- Two distinct winners never share a key. -/
theorem winners_unique (b : Bundle) {i j : Nat}
    (hne : i ≠ j) (hwi : winAt b i = true) (hwj : winAt b j = true) :
    sameKey (b.get i) (b.get j) = false := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hvalid : validAt (b.get i) = true := winAt_valid hwi
    have hnot := winAt_no_earlier hwj hlt
    rw [hvalid, Bool.true_and] at hnot
    exact hnot
  · have hvalid : validAt (b.get j) = true := winAt_valid hwj
    have hnot := winAt_no_earlier hwi hgt
    rw [hvalid, Bool.true_and] at hnot
    rwa [sameKey_comm]

/-! ### The conflict event

SPEC_V2 §6: `CONFLICT` is raised exactly when two or more enabled moves target one
group in a cycle.  The RTL computes it as "some valid move did not win"; that is
the same event, because a valid move fails to win exactly when an earlier valid
move shares its key. -/

theorem and_not_and_not (a b : Bool) : (a && !(a && !b)) = (a && b) := by
  cases a <;> cases b <;> rfl

/-- The elaborated form and the pairwise form are the same event. -/
theorem conflictEv_eq_pairSameKey (b : Bundle) : conflictEv b = pairSameKey b := by
  simp only [conflictEv, pairSameKey, blocked, winAt, and_not_and_not]

/-- `CONFLICT` is raised exactly when two valid moves share a key. -/
theorem conflictEv_iff_pairs (b : Bundle) :
    conflictEv b = true ↔ ∃ i j, i < j ∧ j < 6 ∧ validAt (b.get i) = true ∧
      validAt (b.get j) = true ∧ sameKey (b.get i) (b.get j) = true := by
  rw [conflictEv_eq_pairSameKey]
  unfold pairSameKey
  rw [List.any_eq_true]
  constructor
  · rintro ⟨k, hk, hinner⟩
    rw [List.mem_range] at hk
    rw [Bool.and_eq_true] at hinner
    obtain ⟨hvk, hany⟩ := hinner
    rw [List.any_eq_true] at hany
    obtain ⟨j, hj, hpair⟩ := hany
    rw [List.mem_range] at hj
    rw [Bool.and_eq_true] at hpair
    exact ⟨j, k, hj, hk, hpair.1, hvk, hpair.2⟩
  · rintro ⟨i, j, hij, hj, hvi, hvj, hsk⟩
    refine ⟨j, by simpa [List.mem_range] using hj, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨hvj, ?_⟩
    rw [List.any_eq_true]
    exact ⟨i, by simpa [List.mem_range] using hij, by simp [hvi, hsk]⟩

/-- Two valid moves with the same key raise `CONFLICT` in that cycle. -/
theorem conflict_of_two (b : Bundle) {i j : Nat} (hij : i < j) (hj : j < 6)
    (hvi : validAt (b.get i) = true) (hvj : validAt (b.get j) = true)
    (hkey : sameKey (b.get i) (b.get j) = true) : conflictEv b = true :=
  (conflictEv_iff_pairs b).2 ⟨i, j, hij, hj, hvi, hvj, hkey⟩

/-- A raised `CONFLICT` gives two valid moves with the same key. -/
theorem conflict_witness (b : Bundle) (h : conflictEv b = true) :
    ∃ i j, i < j ∧ j < 6 ∧ validAt (b.get i) = true ∧ validAt (b.get j) = true ∧
      sameKey (b.get i) (b.get j) = true :=
  (conflictEv_iff_pairs b).1 h

/-! ## The group pick

`pick(hits(mv_en, grp_v, G), c_dst, c_dat)` selects, among the enabled moves
whose destination is in group `G`, the one with the lowest index (the RTL's
`hits` prefix mask), and packs its `{1, dst, data}`.  A group with no contender
writes zero.
-/

/-- Move `q` contends for group `G`: enabled and its group is `G`. -/
def hitAt (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5) (q : Nat) : Bool :=
  bitAt en q && (slice grp (5 * q) 5 == G)

/-- A function of the six slots as a six-bit mask, bit `q` at position `q`. -/
def bits6 (v : Nat → Bool) : BitVec 6 :=
  (if v 0 then 1 else 0) ||| (if v 1 then 2 else 0) ||| (if v 2 then 4 else 0) |||
    (if v 3 then 8 else 0) ||| (if v 4 then 16 else 0) ||| (if v 5 then 32 else 0)

/-- The RTL's `hits` mask: contender `q` survives only if no lower slot
contends for the same group.  Written out slot by slot (the RTL's
`v[q] & ~|(v & ((1<<q)-1))`), so the mask is plain Boolean algebra. -/
def hitsMask (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5) : BitVec 6 :=
  bits6 (fun q =>
    match q with
    | 0 => hitAt en grp G 0
    | 1 => hitAt en grp G 1 && !(hitAt en grp G 0)
    | 2 => hitAt en grp G 2 && !(hitAt en grp G 0 || hitAt en grp G 1)
    | 3 => hitAt en grp G 3 && !(hitAt en grp G 0 || hitAt en grp G 1 || hitAt en grp G 2)
    | 4 => hitAt en grp G 4 && !(hitAt en grp G 0 || hitAt en grp G 1 || hitAt en grp G 2 ||
        hitAt en grp G 3)
    | _ => hitAt en grp G 5 && !(hitAt en grp G 0 || hitAt en grp G 1 || hitAt en grp G 2 ||
        hitAt en grp G 3 || hitAt en grp G 4))

/-- The six valid bits as a bus, for the RTL equality. -/
def validBits (en : BitVec 6) (grp : BitVec 30) : BitVec 6 :=
  bits6 (fun q => validAt ((arbBundle en grp 0 0).get q))

/-- The six winner bits as a bus, for the RTL equality. -/
def winBits (en : BitVec 6) (grp : BitVec 30) (xl : BitVec 4) (xt : BitVec 6) : BitVec 6 :=
  bits6 (fun q => winAt (arbBundle en grp xl xt) q)

/-- The elaborated conflict event, as a specification-level function. -/
def conflictOf (en : BitVec 6) (grp : BitVec 30) (xl : BitVec 4) (xt : BitVec 6) : Bool :=
  conflictEv (arbBundle en grp xl xt)

/-- The per-line `L.SYM` mask: the winners of the group that ran on `line` — the
RTL's `sh[j] = mv_win[j] & (grp[j] == DG_L_SYM) & (xl[j] == line)`. -/
def symMask (win : BitVec 6) (grp : BitVec 30) (xl : BitVec 4) (line : BitVec 2) : BitVec 6 :=
  bits6 (fun q => bitAt win q && (slice grp (5 * q) 5 == dgLSym) &&
    (slice xl (2 * (q / 3)) 2 == line))

/-- The mask's bit `q` is the winner's bit of that slot for that line. -/
theorem symMask_bit (win : BitVec 6) (grp : BitVec 30) (xl : BitVec 4) (line : BitVec 2)
    (q : Nat) (hq : q < 6) :
    bitAt (symMask win grp xl line) q =
      (bitAt win q && (slice grp (5 * q) 5 == dgLSym) &&
        (slice xl (2 * (q / 3)) 2 == line)) := by
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [symMask, bits6, bitAt] <;> bv_decide)

/-- The RTL pick's OR-of-masked-words form: bit `q` of `hit` selects slot `q`'s
`{1, dst, data}` word.  With a one-hot (or zero) mask this is the same word the
priority `pickWord` returns; the `L.SYM` picks use it directly. -/
def hitOr (hit : BitVec 6) (dst : BitVec 36) (dat : BitVec 48) : BitVec 15 :=
  (if bitAt hit 0 then makeWord true (slice dst 0 6) (slice dat 0 8) else 0) |||
  (if bitAt hit 1 then makeWord true (slice dst 6 6) (slice dat 8 8) else 0) |||
  (if bitAt hit 2 then makeWord true (slice dst 12 6) (slice dat 16 8) else 0) |||
  (if bitAt hit 3 then makeWord true (slice dst 18 6) (slice dat 24 8) else 0) |||
  (if bitAt hit 4 then makeWord true (slice dst 24 6) (slice dat 32 8) else 0) |||
  (if bitAt hit 5 then makeWord true (slice dst 30 6) (slice dat 40 8) else 0)

/-- At most one bit of a six-bit mask is set. -/
def atMostOne (hit : BitVec 6) : Bool :=
  !(bitAt hit 0 && bitAt hit 1) && !(bitAt hit 0 && bitAt hit 2) &&
  !(bitAt hit 0 && bitAt hit 3) && !(bitAt hit 0 && bitAt hit 4) &&
  !(bitAt hit 0 && bitAt hit 5) && !(bitAt hit 1 && bitAt hit 2) &&
  !(bitAt hit 1 && bitAt hit 3) && !(bitAt hit 1 && bitAt hit 4) &&
  !(bitAt hit 1 && bitAt hit 5) && !(bitAt hit 2 && bitAt hit 3) &&
  !(bitAt hit 2 && bitAt hit 4) && !(bitAt hit 2 && bitAt hit 5) &&
  !(bitAt hit 3 && bitAt hit 4) && !(bitAt hit 3 && bitAt hit 5) &&
  !(bitAt hit 4 && bitAt hit 5)

/-- The group word `{we, dst, data}`: the first set hit supplies `dst` and
`data`; `we` says whether any hit is set. -/
def pickWord (hit : BitVec 6) (dst : BitVec 36) (dat : BitVec 48) : GroupWord where
  we := !(hit == 0)
  dst := chain (bitAt hit 0) (bitAt hit 1) (bitAt hit 2) (bitAt hit 3) (bitAt hit 4)
    (bitAt hit 5) (slice dst 0 6) (slice dst 6 6) (slice dst 12 6) (slice dst 18 6)
    (slice dst 24 6) (slice dst 30 6)
  data := chain (bitAt hit 0) (bitAt hit 1) (bitAt hit 2) (bitAt hit 3) (bitAt hit 4)
    (bitAt hit 5) (slice dat 0 8) (slice dat 8 8) (slice dat 16 8) (slice dat 24 8)
    (slice dat 32 8) (slice dat 40 8)

/-- The `we` bit of the pick: any contender at all. -/
theorem pickWord_we (hit : BitVec 6) (dst : BitVec 36) (dat : BitVec 48) :
    (pickWord hit dst dat).we = !(hit == 0) := rfl

/-- No contender: the group writes zero. -/
theorem pickWord_none (hit : BitVec 6) (dst : BitVec 36) (dat : BitVec 48)
    (h : hit = 0) : pickWord hit dst dat = ⟨false, 0, 0⟩ := by
  subst h
  apply GroupWord.ext <;> simp [pickWord, chain, bitAt]

/-! ### The mask of the first contender -/

theorem hitsMask_bit_0 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5) :
    bitAt (hitsMask en grp G) 0 = hitAt en grp G 0 := by
  simp only [hitsMask, bits6, hitAt, bitAt]
  bv_decide

theorem hitsMask_bit_1 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5) :
    bitAt (hitsMask en grp G) 1 = (hitAt en grp G 1 && !(hitAt en grp G 0)) := by
  simp only [hitsMask, bits6, hitAt, bitAt]
  bv_decide

theorem hitsMask_bit_2 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5) :
    bitAt (hitsMask en grp G) 2 =
      (hitAt en grp G 2 && !(hitAt en grp G 0 || hitAt en grp G 1)) := by
  simp only [hitsMask, bits6, hitAt, bitAt]
  bv_decide

theorem hitsMask_bit_3 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5) :
    bitAt (hitsMask en grp G) 3 =
      (hitAt en grp G 3 && !(hitAt en grp G 0 || hitAt en grp G 1 || hitAt en grp G 2)) := by
  simp only [hitsMask, bits6, hitAt, bitAt]
  bv_decide

theorem hitsMask_bit_4 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5) :
    bitAt (hitsMask en grp G) 4 =
      (hitAt en grp G 4 && !(hitAt en grp G 0 || hitAt en grp G 1 || hitAt en grp G 2 ||
        hitAt en grp G 3)) := by
  simp only [hitsMask, bits6, hitAt, bitAt]
  bv_decide

theorem hitsMask_bit_5 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5) :
    bitAt (hitsMask en grp G) 5 =
      (hitAt en grp G 5 && !(hitAt en grp G 0 || hitAt en grp G 1 || hitAt en grp G 2 ||
        hitAt en grp G 3 || hitAt en grp G 4)) := by
  simp only [hitsMask, bits6, hitAt, bitAt]
  bv_decide

/-- The mask has a set bit exactly when some slot contends. -/
theorem hitsMask_ne_zero (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5) :
    (!(hitsMask en grp G == 0)) =
      (hitAt en grp G 0 || hitAt en grp G 1 || hitAt en grp G 2 || hitAt en grp G 3 ||
        hitAt en grp G 4 || hitAt en grp G 5) := by
  simp only [hitsMask, bits6, hitAt, bitAt]
  bv_decide

/-- The first contender's word: a group with a contender writes that move's
`{1, dst, data}`.  The six lemmas cover every position of the first contender. -/
theorem pick_first_0 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (dst : BitVec 36) (dat : BitVec 48) (h : hitAt en grp G 0 = true) :
    pickWord (hitsMask en grp G) dst dat = ⟨true, slice dst 0 6, slice dat 0 8⟩ := by
  have hm : hitsMask en grp G = bits6 (fun q => q = 0) := by
    simp [hitsMask, h, bits6]
  rw [hm]
  apply GroupWord.ext <;> simp [pickWord, chain, bits6, bitAt]

theorem pick_first_1 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (dst : BitVec 36) (dat : BitVec 48)
    (h0 : hitAt en grp G 0 = false) (h1 : hitAt en grp G 1 = true) :
    pickWord (hitsMask en grp G) dst dat = ⟨true, slice dst 6 6, slice dat 8 8⟩ := by
  have hm : hitsMask en grp G = bits6 (fun q => q = 1) := by
    simp [hitsMask, h0, h1, bits6]
  rw [hm]
  apply GroupWord.ext <;> simp [pickWord, chain, bits6, bitAt]

theorem pick_first_2 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (dst : BitVec 36) (dat : BitVec 48)
    (h0 : hitAt en grp G 0 = false) (h1 : hitAt en grp G 1 = false)
    (h2 : hitAt en grp G 2 = true) :
    pickWord (hitsMask en grp G) dst dat = ⟨true, slice dst 12 6, slice dat 16 8⟩ := by
  have hm : hitsMask en grp G = bits6 (fun q => q = 2) := by
    simp [hitsMask, h0, h1, h2, bits6]
  rw [hm]
  apply GroupWord.ext <;> simp [pickWord, chain, bits6, bitAt]

theorem pick_first_3 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (dst : BitVec 36) (dat : BitVec 48)
    (h0 : hitAt en grp G 0 = false) (h1 : hitAt en grp G 1 = false)
    (h2 : hitAt en grp G 2 = false) (h3 : hitAt en grp G 3 = true) :
    pickWord (hitsMask en grp G) dst dat = ⟨true, slice dst 18 6, slice dat 24 8⟩ := by
  have hm : hitsMask en grp G = bits6 (fun q => q = 3) := by
    simp [hitsMask, h0, h1, h2, h3, bits6]
  rw [hm]
  apply GroupWord.ext <;> simp [pickWord, chain, bits6, bitAt]

theorem pick_first_4 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (dst : BitVec 36) (dat : BitVec 48)
    (h0 : hitAt en grp G 0 = false) (h1 : hitAt en grp G 1 = false)
    (h2 : hitAt en grp G 2 = false) (h3 : hitAt en grp G 3 = false)
    (h4 : hitAt en grp G 4 = true) :
    pickWord (hitsMask en grp G) dst dat = ⟨true, slice dst 24 6, slice dat 32 8⟩ := by
  have hm : hitsMask en grp G = bits6 (fun q => q = 4) := by
    simp [hitsMask, h0, h1, h2, h3, h4, bits6]
  rw [hm]
  apply GroupWord.ext <;> simp [pickWord, chain, bits6, bitAt]

theorem pick_first_5 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (dst : BitVec 36) (dat : BitVec 48)
    (h0 : hitAt en grp G 0 = false) (h1 : hitAt en grp G 1 = false)
    (h2 : hitAt en grp G 2 = false) (h3 : hitAt en grp G 3 = false)
    (h4 : hitAt en grp G 4 = false) (h5 : hitAt en grp G 5 = true) :
    pickWord (hitsMask en grp G) dst dat = ⟨true, slice dst 30 6, slice dat 40 8⟩ := by
  have hm : hitsMask en grp G = bits6 (fun q => q = 5) := by
    simp [hitsMask, h0, h1, h2, h3, h4, h5, bits6]
  rw [hm]
  apply GroupWord.ext <;> simp [pickWord, chain, bits6, bitAt]

/-- A group with no contender writes zero. -/
theorem pick_none (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (dst : BitVec 36) (dat : BitVec 48)
    (h : (hitAt en grp G 0 || hitAt en grp G 1 || hitAt en grp G 2 || hitAt en grp G 3 ||
      hitAt en grp G 4 || hitAt en grp G 5) = false) :
    pickWord (hitsMask en grp G) dst dat = ⟨false, 0, 0⟩ := by
  have hz : hitsMask en grp G = 0 := by
    have hz0 : ((!(hitsMask en grp G == 0)) = false) := by
      rw [hitsMask_ne_zero]
      exact h
    rw [not_eq_false_eq_true] at hz0
    rwa [beq_iff_eq] at hz0
  exact pickWord_none _ _ _ hz

/-- The pick's `we` is set exactly when some move contends for the group. -/
theorem pick_we_iff (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (dst : BitVec 36) (dat : BitVec 48) :
    (pickWord (hitsMask en grp G) dst dat).we = true ↔
      (hitAt en grp G 0 = true ∨ hitAt en grp G 1 = true ∨ hitAt en grp G 2 = true ∨
        hitAt en grp G 3 = true ∨ hitAt en grp G 4 = true ∨ hitAt en grp G 5 = true) := by
  rw [pickWord_we, hitsMask_ne_zero]
  simp only [Bool.or_eq_true, or_assoc]

/-- A slot contends for group `G`: enabled and its group is `G` — the RTL's
`hits` bit before the prefix mask. -/
def contender (m : Slot) (G : BitVec 5) : Bool := m.enabled && (m.group == G)

/-- The bus-level hit of a slot is the bundle slot's contender flag. -/
theorem hitAt_contender (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36)
    (dat : BitVec 48) (xl : BitVec 4) (xt : BitVec 6) (G : BitVec 5) (q : Nat)
    (hq : q < 6) :
    hitAt en grp G q = contender ((bundleOf en grp dst dat xl xt).get q) G := by
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The arbitration bundle's contender flag is the bus-level hit. -/
theorem contender_arb (en : BitVec 6) (grp : BitVec 30) (xl : BitVec 4) (xt : BitVec 6)
    (G : BitVec 5) (q : Nat) (hq : q < 6) :
    contender ((arbBundle en grp xl xt).get q) G = hitAt en grp G q := by
  rw [arbBundle, ← (hitAt_contender en grp 0 0 xl xt G q hq)]

/-- A contender of a real group is a valid move of that group. -/
theorem hitAt_valid (en : BitVec 6) (grp : BitVec 30) (xl : BitVec 4) (xt : BitVec 6)
    (G : BitVec 5) (q : Nat) (hq : q < 6) :
    (validAt ((arbBundle en grp xl xt).get q) && ((arbBundle en grp xl xt).get q).group == G) =
      ((!(G == dgNone)) && hitAt en grp G q) := by
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [hitAt, validAt, arbBundle, bundleOf, Bundle.get, dgNone, bitAt, slice] <;>
      bv_decide)

theorem beq_trans_5 (a b c : BitVec 5) (h1 : (a == b) = true) (h2 : (b == c) = true) :
    (a == c) = true := by
  rw [beq_iff_eq] at *
  exact h1.trans h2

/-- A move whose group is `G` is valid exactly when it is enabled, for a real
group code. -/
theorem valid_of_group {m : Slot} {G : BitVec 5} (hG : (!(G == dgNone)) = true)
    (hen : m.enabled = true) (hgrp : (m.group == G) = true) : validAt m = true := by
  have hne : (m.group == dgNone) = false := by
    by_cases h : (m.group == dgNone) = true
    · have h1 : (G == dgNone) = true := by
        rw [beq_iff_eq] at h hgrp ⊢
        exact hgrp.symm.trans h
      have h2 : (!(G == dgNone)) = true := hG
      rw [h1] at h2
      exact absurd h2 (by decide)
    · simpa using h
  simp [validAt, hen, hne]

/-- The first move of a real group is that group's winner: nothing earlier
contends for the group, and a valid earlier move with the same key would have to
contend for it. -/
theorem win_of_first (b : Bundle) (G : BitVec 5) (k : Nat)
    (hG : (!(G == dgNone)) = true)
    (hgrp : ((b.get k).group == G) = true) (hen : (b.get k).enabled = true)
    (hfirst : ∀ j, j < k → contender (b.get j) G = false) :
    winAt b k = true := by
  have hvalid : validAt (b.get k) = true := valid_of_group hG hen hgrp
  have hblocked : blocked b k = false := by
    unfold blocked
    rw [List.any_eq_false]
    intro j hj
    rw [Bool.and_eq_true]
    rintro ⟨hv, hkey⟩
    have hkj : ((b.get j).group == (b.get k).group) = true := by
      have := hkey
      unfold sameKey at this
      rw [Bool.and_eq_true, Bool.and_eq_true] at this
      exact this.1.1
    have hgj : ((b.get j).group == G) = true := beq_trans_5 _ _ _ hkj hgrp
    have henj : (b.get j).enabled = true := by
      have := hv
      unfold validAt at this
      rw [Bool.and_eq_true] at this
      exact this.1
    have : contender (b.get j) G = true := by
      simp [contender, henj, hgj]
    rw [hfirst j (by simpa [List.mem_range] using hj)] at this
    exact absurd this (by decide)
  exact winAt_true_of_unblocked hvalid hblocked

/-! ### The first contender of a real group is the pick's winner

The six lemmas below are the cut's central statement: if slot `k` is the lowest
contender for group `G` (and `G` is a real group code), the pick returns that
slot's `{1, dst, data}` and that slot is the group's winner. -/

theorem pick_is_winner_0 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (dst : BitVec 36) (dat : BitVec 48) (xl : BitVec 4) (xt : BitVec 6)
    (hG : (!(G == dgNone)) = true) (h : hitAt en grp G 0 = true) :
    pickWord (hitsMask en grp G) dst dat = ⟨true, slice dst 0 6, slice dat 0 8⟩ ∧
      winAt (arbBundle en grp xl xt) 0 = true := by
  have hc : contender ((arbBundle en grp xl xt).get 0) G = true := by
    rw [contender_arb en grp xl xt G 0 (by omega)]
    exact h
  rw [contender, Bool.and_eq_true] at hc
  exact ⟨pick_first_0 en grp G dst dat h,
    win_of_first _ G 0 hG hc.2 hc.1 (fun j hj => absurd hj (by omega))⟩

theorem pick_is_winner_1 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (dst : BitVec 36) (dat : BitVec 48) (xl : BitVec 4) (xt : BitVec 6)
    (hG : (!(G == dgNone)) = true)
    (h0 : hitAt en grp G 0 = false) (h1 : hitAt en grp G 1 = true) :
    pickWord (hitsMask en grp G) dst dat = ⟨true, slice dst 6 6, slice dat 8 8⟩ ∧
      winAt (arbBundle en grp xl xt) 1 = true := by
  have hc : contender ((arbBundle en grp xl xt).get 1) G = true := by
    rw [contender_arb en grp xl xt G 1 (by omega)]
    exact h1
  rw [contender, Bool.and_eq_true] at hc
  refine ⟨pick_first_1 en grp G dst dat h0 h1, win_of_first _ G 1 hG hc.2 hc.1 ?_⟩
  intro j hj
  have hj0 : j = 0 := by omega
  rw [hj0, contender_arb en grp xl xt G 0 (by omega)]
  exact h0

theorem pick_is_winner_2 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (dst : BitVec 36) (dat : BitVec 48) (xl : BitVec 4) (xt : BitVec 6)
    (hG : (!(G == dgNone)) = true)
    (h0 : hitAt en grp G 0 = false) (h1 : hitAt en grp G 1 = false)
    (h2 : hitAt en grp G 2 = true) :
    pickWord (hitsMask en grp G) dst dat = ⟨true, slice dst 12 6, slice dat 16 8⟩ ∧
      winAt (arbBundle en grp xl xt) 2 = true := by
  have hc : contender ((arbBundle en grp xl xt).get 2) G = true := by
    rw [contender_arb en grp xl xt G 2 (by omega)]
    exact h2
  rw [contender, Bool.and_eq_true] at hc
  refine ⟨pick_first_2 en grp G dst dat h0 h1 h2, win_of_first _ G 2 hG hc.2 hc.1 ?_⟩
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1) with hj0 | hj1
  · rw [hj0, contender_arb en grp xl xt G 0 (by omega)]; exact h0
  · rw [hj1, contender_arb en grp xl xt G 1 (by omega)]; exact h1

theorem pick_is_winner_3 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (dst : BitVec 36) (dat : BitVec 48) (xl : BitVec 4) (xt : BitVec 6)
    (hG : (!(G == dgNone)) = true)
    (h0 : hitAt en grp G 0 = false) (h1 : hitAt en grp G 1 = false)
    (h2 : hitAt en grp G 2 = false) (h3 : hitAt en grp G 3 = true) :
    pickWord (hitsMask en grp G) dst dat = ⟨true, slice dst 18 6, slice dat 24 8⟩ ∧
      winAt (arbBundle en grp xl xt) 3 = true := by
  have hc : contender ((arbBundle en grp xl xt).get 3) G = true := by
    rw [contender_arb en grp xl xt G 3 (by omega)]
    exact h3
  rw [contender, Bool.and_eq_true] at hc
  refine ⟨pick_first_3 en grp G dst dat h0 h1 h2 h3, win_of_first _ G 3 hG hc.2 hc.1 ?_⟩
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with hj0 | hj1 | hj2
  · rw [hj0, contender_arb en grp xl xt G 0 (by omega)]; exact h0
  · rw [hj1, contender_arb en grp xl xt G 1 (by omega)]; exact h1
  · rw [hj2, contender_arb en grp xl xt G 2 (by omega)]; exact h2

theorem pick_is_winner_4 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (dst : BitVec 36) (dat : BitVec 48) (xl : BitVec 4) (xt : BitVec 6)
    (hG : (!(G == dgNone)) = true)
    (h0 : hitAt en grp G 0 = false) (h1 : hitAt en grp G 1 = false)
    (h2 : hitAt en grp G 2 = false) (h3 : hitAt en grp G 3 = false)
    (h4 : hitAt en grp G 4 = true) :
    pickWord (hitsMask en grp G) dst dat = ⟨true, slice dst 24 6, slice dat 32 8⟩ ∧
      winAt (arbBundle en grp xl xt) 4 = true := by
  have hc : contender ((arbBundle en grp xl xt).get 4) G = true := by
    rw [contender_arb en grp xl xt G 4 (by omega)]
    exact h4
  rw [contender, Bool.and_eq_true] at hc
  refine ⟨pick_first_4 en grp G dst dat h0 h1 h2 h3 h4, win_of_first _ G 4 hG hc.2 hc.1 ?_⟩
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with hj0 | hj1 | hj2 | hj3
  · rw [hj0, contender_arb en grp xl xt G 0 (by omega)]; exact h0
  · rw [hj1, contender_arb en grp xl xt G 1 (by omega)]; exact h1
  · rw [hj2, contender_arb en grp xl xt G 2 (by omega)]; exact h2
  · rw [hj3, contender_arb en grp xl xt G 3 (by omega)]; exact h3

theorem pick_is_winner_5 (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5)
    (dst : BitVec 36) (dat : BitVec 48) (xl : BitVec 4) (xt : BitVec 6)
    (hG : (!(G == dgNone)) = true)
    (h0 : hitAt en grp G 0 = false) (h1 : hitAt en grp G 1 = false)
    (h2 : hitAt en grp G 2 = false) (h3 : hitAt en grp G 3 = false)
    (h4 : hitAt en grp G 4 = false) (h5 : hitAt en grp G 5 = true) :
    pickWord (hitsMask en grp G) dst dat = ⟨true, slice dst 30 6, slice dat 40 8⟩ ∧
      winAt (arbBundle en grp xl xt) 5 = true := by
  have hc : contender ((arbBundle en grp xl xt).get 5) G = true := by
    rw [contender_arb en grp xl xt G 5 (by omega)]
    exact h5
  rw [contender, Bool.and_eq_true] at hc
  refine ⟨pick_first_5 en grp G dst dat h0 h1 h2 h3 h4 h5,
    win_of_first _ G 5 hG hc.2 hc.1 ?_⟩
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with
    hj0 | hj1 | hj2 | hj3 | hj4
  · rw [hj0, contender_arb en grp xl xt G 0 (by omega)]; exact h0
  · rw [hj1, contender_arb en grp xl xt G 1 (by omega)]; exact h1
  · rw [hj2, contender_arb en grp xl xt G 2 (by omega)]; exact h2
  · rw [hj3, contender_arb en grp xl xt G 3 (by omega)]; exact h3
  · rw [hj4, contender_arb en grp xl xt G 4 (by omega)]; exact h4


/-! ## The sticky flags (SPEC_V2 §6 and §10)

`CONFLICT` and `MEMHAZ` are write-one-to-clear sticky bits in `CTRL.STICKY`
(bit 0 and bit 1).  In a cycle with an event the bit becomes set; a host write
of `CTRL.STICKY` with the bit set clears it *unless* the same cycle has an
event. -/

/-- The three inputs of a sticky step. -/
structure StickyInput where
  /-- `rst_q`: reset released. -/
  resetN : Bool
  /-- The event term (`conflict_ev` / `memhaz_ev`). -/
  event : Bool
  /-- The host's write-one-to-clear bit. -/
  clear : Bool
  deriving DecidableEq, Repr

/-- The sticky next state: reset clears, an event sets, a clear-only cycle
clears, an event beats a simultaneous clear. -/
def stickyNext (state : Bool) (i : StickyInput) : Bool :=
  if i.resetN then (i.event || (state && !i.clear)) else false

theorem sticky_reset (state ev clear : Bool) :
    stickyNext state ⟨false, ev, clear⟩ = false := rfl

/-- An event sets the flag, whatever the clear bit does in that cycle. -/
theorem sticky_event (state clear : Bool) :
    stickyNext state ⟨true, true, clear⟩ = true := by
  simp [stickyNext]

/-- A clear-only cycle clears the flag. -/
theorem sticky_clear (state : Bool) :
    stickyNext state ⟨true, false, true⟩ = false := by
  simp [stickyNext]

/-- Away from an event and a clear, the flag holds. -/
theorem sticky_hold (state : Bool) :
    stickyNext state ⟨true, false, false⟩ = state := by
  simp [stickyNext]

/-- The event beats a simultaneous clear. -/
theorem sticky_event_beats_clear (state : Bool) :
    stickyNext state ⟨true, true, true⟩ = true := by
  simp [stickyNext]

/-- Only a clear cycle with no event lowers a set flag. -/
theorem sticky_stays_set (state : Bool) (i : StickyInput)
    (hi : i.resetN = true) (hstate : state = true) (hnoEvent : i.event = false)
    (hnoClear : i.clear = false) : stickyNext state i = true := by
  subst hstate
  simp [stickyNext, hi, hnoEvent, hnoClear]

/-- Once set, the flag stays set through a cycle with an event. -/
theorem trace_sticky_set (inputs : Nat → StickyInput) (m : Nat)
    (hr : (inputs m).resetN = true) (h : (inputs m).event = true) :
    run (fun s i => stickyNext s i) inputs true (m + 1) = true := by
  rw [run_succ]
  have hEq : inputs m = ⟨true, true, (inputs m).clear⟩ := by
    cases hm : inputs m with
    | mk r e c =>
      simp only [hm] at hr h ⊢
      simp [hr, h]
  rw [hEq]
  exact sticky_event _ _

/-- From reset, the flag is low in every cycle with no event. -/
theorem trace_sticky_low (inputs : Nat → StickyInput) :
    ∀ n, (∀ k, k < n → (inputs k).resetN = true) →
      (∀ k, k < n → (inputs k).event = false) →
      run (fun s i => stickyNext s i) inputs false n = false := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro hreset hevent
    rw [run_succ]
    have hlow := ih (fun k hk => hreset k (by omega)) (fun k hk => hevent k (by omega))
    rw [hlow]
    have hn : (inputs n).event = false := hevent n (by omega)
    by_cases hr : (inputs n).resetN = true
    · simp [stickyNext, hr, hn]
    · simp [stickyNext, hr]

/-! ### The prefix scans, slot by slot

The spec's scans are `List.range`-based; the RTL has six fixed slots.  These
lemmas are the bridge: at a literal slot index the scan is the explicit
conjunction of the earlier slots. -/

theorem range_one : List.range 1 = [0] := by decide

theorem range_two : List.range 2 = [0, 1] := by decide

theorem range_three : List.range 3 = [0, 1, 2] := by decide

theorem range_four : List.range 4 = [0, 1, 2, 3] := by decide

theorem range_five : List.range 5 = [0, 1, 2, 3, 4] := by decide

theorem range_six : List.range 6 = [0, 1, 2, 3, 4, 5] := by decide

@[simp] theorem blocked_zero (b : Bundle) : blocked b 0 = false := by
  simp [blocked]

@[simp] theorem blocked_one (b : Bundle) :
    blocked b 1 = (validAt (b.get 0) && sameKey (b.get 0) (b.get 1)) := by
  simp [blocked]

@[simp] theorem blocked_two (b : Bundle) :
    blocked b 2 = ((validAt (b.get 0) && sameKey (b.get 0) (b.get 2)) ||
      (validAt (b.get 1) && sameKey (b.get 1) (b.get 2))) := by
  simp [blocked, range_two]

@[simp] theorem blocked_three (b : Bundle) :
    blocked b 3 = ((validAt (b.get 0) && sameKey (b.get 0) (b.get 3)) ||
      ((validAt (b.get 1) && sameKey (b.get 1) (b.get 3)) ||
      (validAt (b.get 2) && sameKey (b.get 2) (b.get 3)))) := by
  simp [blocked, range_three]

@[simp] theorem blocked_four (b : Bundle) :
    blocked b 4 = ((validAt (b.get 0) && sameKey (b.get 0) (b.get 4)) ||
      ((validAt (b.get 1) && sameKey (b.get 1) (b.get 4)) ||
      ((validAt (b.get 2) && sameKey (b.get 2) (b.get 4)) ||
      (validAt (b.get 3) && sameKey (b.get 3) (b.get 4))))) := by
  simp [blocked, range_four]

@[simp] theorem blocked_five (b : Bundle) :
    blocked b 5 = ((validAt (b.get 0) && sameKey (b.get 0) (b.get 5)) ||
      ((validAt (b.get 1) && sameKey (b.get 1) (b.get 5)) ||
      ((validAt (b.get 2) && sameKey (b.get 2) (b.get 5)) ||
      ((validAt (b.get 3) && sameKey (b.get 3) (b.get 5)) ||
      (validAt (b.get 4) && sameKey (b.get 4) (b.get 5)))))) := by
  simp [blocked, range_five]

/-- The conflict event as the explicit six-way scan. -/
@[simp] theorem conflictEv_six (b : Bundle) :
    conflictEv b = ((validAt (b.get 0) && !winAt b 0) ||
      ((validAt (b.get 1) && !winAt b 1) ||
      ((validAt (b.get 2) && !winAt b 2) ||
      ((validAt (b.get 3) && !winAt b 3) ||
      ((validAt (b.get 4) && !winAt b 4) ||
      (validAt (b.get 5) && !winAt b 5)))))) := by
  simp [conflictEv, range_six]

/-! ## Source side effects (SPEC_V2 §6)

Reading `HOST.IN` clears `INV`; reading `P0.D` while `!P0.RDY` sets sticky
`MEMHAZ`.  Both happen only for *enabled* moves. -/

/-- Move `q` reads source code `s`: enabled and `c_src` is `s`. -/
def readAt (en : BitVec 6) (src : BitVec 36) (s : BitVec 6) (q : Nat) : Bool :=
  bitAt en q && (slice src (6 * q) 6 == s)

/-- The six move reads of one source code, as the RTL's `rd_hin` / `rd_pd`. -/
def readsOf (en : BitVec 6) (src : BitVec 36) (s : BitVec 6) : BitVec 6 :=
  bits6 (readAt en src s)

/-- Some enabled move reads source `s`. -/
def enabledRead (en : BitVec 6) (src : BitVec 36) (s : BitVec 6) : Bool :=
  !(readsOf en src s == 0)

/-- A disabled move's read can never be set. -/
theorem readAt_disabled (en : BitVec 6) (src : BitVec 36) (s : BitVec 6) (q : Nat)
    (h : bitAt en q = false) : readAt en src s q = false := by
  simp [readAt, h]

/-- Some move reads source `s` exactly when that move is enabled. -/
theorem readsOf_ne_zero (en : BitVec 6) (src : BitVec 36) (s : BitVec 6) :
    (!(readsOf en src s == 0)) =
      (readAt en src s 0 || readAt en src s 1 || readAt en src s 2 || readAt en src s 3 ||
        readAt en src s 4 || readAt en src s 5) := by
  simp only [readsOf, bits6, readAt, bitAt]
  bv_decide

/-- `INV` next state: reset clears, a host write sets, a `HOST.IN` read clears,
otherwise it holds (the host write wins, as the RTL's `if`/`else if`). -/
def invNext (state : Bool) (resetN hostWrite readHin : Bool) : Bool :=
  if !resetN then false else if hostWrite then true else if readHin then false else state

theorem inv_reset (state hw r : Bool) : invNext state false hw r = false := rfl

theorem inv_host_write (state r : Bool) : invNext state true true r = true := by
  simp [invNext]

theorem inv_read_clears (state : Bool) :
    invNext state true false true = false := by
  simp [invNext]

theorem inv_hold (state : Bool) : invNext state true false false = state := by
  simp [invNext]

/-- The `MEMHAZ` event from the six `rd_pd` bits:
`memhaz_ev = p_haz | (|rd_pd & ~p_rdy)`. -/
def memhazEventOf (rdPd : BitVec 6) (haz ready : Bool) : Bool :=
  haz || (!(rdPd == 0) && !ready)

/-- The `MEMHAZ` event: some move reads `P0.D` while the pointer data is not
ready. -/
def memhazEvent (en : BitVec 6) (src : BitVec 36) (haz ready : Bool) : Bool :=
  memhazEventOf (readsOf en src srcP0D) haz ready

/-- A set `rd_pd` bit while `!RDY` raises the `MEMHAZ` event. -/
theorem memhazEventOf_read {rdPd : BitVec 6} {haz : Bool}
    (h : (!(rdPd == 0)) = true) : memhazEventOf rdPd haz false = true := by
  unfold memhazEventOf
  rw [h]
  cases haz <;> rfl

/-- No `rd_pd` bit and no hazard: no `MEMHAZ` event. -/
theorem memhazEventOf_none {rdPd : BitVec 6} {haz : Bool}
    (hnone : rdPd = 0) (hnohaz : haz = false) : memhazEventOf rdPd haz false = false := by
  subst hnone hnohaz
  rfl

/-- A `P0.D` read while `!RDY` raises the `MEMHAZ` event. -/
theorem memhaz_of_read (en : BitVec 6) (src : BitVec 36) (haz : Bool)
    (h : enabledRead en src srcP0D = true) :
    memhazEvent en src haz false = true :=
  memhazEventOf_read (rdPd := readsOf en src srcP0D) h

/-- No `P0.D` read and no hazard: no `MEMHAZ` event. -/
theorem memhaz_none (en : BitVec 6) (src : BitVec 36) (haz : Bool)
    (hnone : enabledRead en src srcP0D = false) (hnohaz : haz = false) :
    memhazEvent en src haz false = false := by
  have hz : readsOf en src srcP0D = 0 := by
    have h0 : (!(readsOf en src srcP0D == 0)) = false := hnone
    rw [not_eq_false_eq_true] at h0
    rwa [beq_iff_eq] at h0
  exact memhazEventOf_none hz hnohaz

end Metronome.Moves
