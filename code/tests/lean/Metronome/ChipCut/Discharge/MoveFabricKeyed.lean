/-
# ChipCut discharge: the keyed move picks

`MoveFabric.lean` turns a `dstOp`-pattern scan over the machine's resolved winners
into the cut's `pickWord` of the destination's write group (`pickScan`,
`pickScan_mWs`).  That lemma deliberately excludes the two **keyed** groups —
`L.SYM` (keyed by the executing line) and `T.STOP` (keyed by the thread) — because
the cut does not read those groups through `pickWord`:

* the line symbol write reads the per-line one-hot mask `symMask` (`Wire.symWord`),
* the thread `stop`/`late` inputs read the *valid* bits `Moves.validBits`
  (`Wire.slotValid`), not the winner bits.

This file supplies the keyed counterparts and the remaining consumer fields that
reduce to the move fabric:

| field | theorem |
|---|---|
| `WireAgree.late` | `wireAgree_late` |
| `WireAgree.stop` | `wireAgree_stop` |

Every theorem is over `(s m pin)` with `ChipRel`, `Inv`, the global string tables
(`DstKindTable`, the jump-guard table) and the core-input bus, exactly the
hypotheses of `pickScan_mWs`.

## The keyed pick recipe

For a group `G` that is keyed by `K` (the line for `L.SYM`, the thread for
`T.STOP`), define the *keyed hit* of slot `q`

```
hit q := validAt (get q) && (group (get q) == G) && (key (get q) == K)
```

(the cut's `symMask` bit is `hit` with `win` in place of `valid`, and the cut's
`slotValid && dst == …` tests are `hit` read through the destination code).  Then

* the **first** keyed hit wins (`winAt_of_keyed_first_stop`): anything that blocks
  it would have to be a valid move with the same key, and `sameKey a b ⇒ slotKey a
  = slotKey b` (`Bridge.Moves.sameKey_iff_slotKey`) forces it to be a keyed hit as
  well, contradicting firstness;
* hence "some valid keyed hit" and "some winning keyed hit" are the same event
  (`any_win_stop_eq`), which is what `stop` needs (the machine scans the winners,
  the cut scans the valid bits).
-/
import Metronome.ChipCut.Discharge.MoveFabric

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 4096

namespace Metronome.ChipCut.Discharge.MoveFabricKeyed

open Metronome
open Metronome.ChipCut.Discharge.MoveFabric

/-! ## 1. Boolean list plumbing -/

/-- A `filterMap` scan is the padded scan: `some` entries are tested, `none`
entries are `false`. -/
theorem any_filterMap {α : Type} {β : Type} (l : List α) (g : α → Option β) (f : β → Bool) :
    (l.filterMap g).any f =
      l.any (fun a => match g a with | some b => f b | none => false) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.filterMap_cons]
    cases h : g a with
    | none => simpa only [h, List.any_cons, Bool.false_or] using ih
    | some b =>
      simp only [h, List.any_cons]
      rw [ih]

/-- The winner list's scan: a `filterMap` guarded by an `if` is an `any` with the
guard. -/
theorem any_filterMap_ite {α : Type} (l : List Nat) (c : Nat → Bool) (g : Nat → α)
    (f : α → Bool) :
    (l.filterMap (fun k => if c k then some (g k) else none)).any f =
      l.any (fun k => if c k then f (g k) else false) := by
  rw [any_filterMap]
  refine List.any_congr rfl (fun k => ?_)
  cases c k <;> rfl

/-- `any` over the six slots is the cut's `anySix` disjunction. -/
theorem anySix_eq_any (f : Nat → Bool) :
    anySix f = (List.range 6).any f := by
  rw [show List.range 6 = [0, 1, 2, 3, 4, 5] from by decide]
  simp only [anySix, List.any_cons, List.any_nil, Bool.or_false, ← Bool.or_assoc]

/-- A `Bool` conjunction with an implied left factor is the right factor. -/
theorem and_of_imp (v d : Bool) (h : d = true → v = true) : (v && d) = d := by
  by_cases hd : d = true
  · rw [hd, h hd]
    rfl
  · have hdf : d = false := by simpa using hd
    rw [hdf, Bool.and_false]

/-! ## 2. Bits and the cut's per-slot projections -/

/-- `Machine.Util.bit` is `CoreCtl.bitAt`. -/
theorem util_bit_eq_bitAt {n : Nat} (x : BitVec n) (i : Nat) :
    Machine.Util.bit x i = CoreCtl.bitAt x i := by
  unfold Machine.Util.bit CoreCtl.bitAt
  rw [BitVec.truncate_eq_setWidth, Bridge.Line.bne_zero_one_bit,
    Bridge.Line.setWidth_one_getLsbD, Bridge.Line.ushiftRight_getLsbD]

/-- Bit `q` of a six-bit mask built by `bits6` is the function's value. -/
theorem bits6_bit (f : Nat → Bool) (q : Nat) (hq : q < 6) :
    Machine.Util.bit (Moves.bits6 f) q = f q := by
  rw [util_bit_eq_bitAt]
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [Moves.bits6, CoreCtl.bitAt] <;> bv_decide)

/-- Slot `k`'s group is the group-bus slice. -/
theorem bundle_grp (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) (dat : BitVec 48)
    (xl : BitVec 4) (xt : BitVec 6) (k : Nat) (hk : k < 6) :
    ((Moves.bundleOf en grp dst dat xl xt).get k).group = CoreCtl.slice grp (5 * k) 5 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `validAt` reads only the enable bit and the group, so the arbitration bundle
and the real bundle agree. -/
theorem validAt_arbBundle (s : State) (pin : Machine.PinIn) (q : Nat) (hq : q < 6) :
    Moves.validAt ((Moves.arbBundle (mvEn s pin) (mvGrp s pin) 0 0).get q) =
      Moves.validAt ((movBundle s pin).get q) := by
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **The cut's valid bit is "enabled and grouped".** -/
theorem slotValid_eq (s : State) (pin : Machine.PinIn) (q : Nat) (hq : q < 6) :
    slotValid s pin q = (((movBundle s pin).get q).enabled &&
      !(((movBundle s pin).get q).group == Moves.dgNone)) := by
  rw [slotValid, Moves.validBits, bits6_bit (hq := hq), validAt_arbBundle s pin q hq]
  rfl

/-- The cut's destination slice of slot `q` is the bundle's destination word. -/
theorem movBundle_dst_slot (s : State) (pin : Machine.PinIn) (q : Nat) (hq : q < 6) :
    ((movBundle s pin).get q).dst = slotDst s pin q := by
  rw [movBundle_dst s pin q hq]
  rfl

/-- The cut's thread slice of slot `q` is the bundle's thread word. -/
theorem movBundle_thread_slot (s : State) (pin : Machine.PinIn) (q : Nat) (hq : q < 6) :
    ((movBundle s pin).get q).thread = slotThread s pin q := by
  rw [bundle_thread (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin) (mvXl s) (mvXt s)
    q hq]
  rfl

/-! ## 3. The `dgTable` classification of the two keyed groups

The cut's `dgTable` (the `DG_MAP` write-group table) puts exactly the codes
`1`/`2`/`3` (`L.SYM`/`L.DBIT`/`L.XOR`) in group `0` (`DG_L_SYM`) and exactly the
code `4` (`T.STOP`) in group `1` (`DG_T_STOP`).  These are 64-code kernel checks
of the literal table (`decide`, no `native_decide`). -/

/-- Group `DG_L_SYM` is exactly codes `1`/`2`/`3`. -/
theorem dgTable_lsym_all :
    (List.range 64).all (fun d => ((Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgLSym) ==
      ((BitVec.ofNat 6 d) <= 3 && (BitVec.ofNat 6 d) != 0))) = true := by
  decide

/-- Group `DG_T_STOP` is exactly code `4`. -/
theorem dgTable_tstop_all :
    (List.range 64).all (fun d => ((Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTStop) ==
      ((BitVec.ofNat 6 d) == 4))) = true := by
  decide

/-- The `DG_L_SYM` group membership of code `v`: `v` is `L.SYM`, `L.DBIT` or
`L.XOR`. -/
theorem dgTable_lsym_iff (v : BitVec 6) :
    (Moves.dgTable v == Moves.dgLSym) = (v <= 3 && v != 0) := by
  have hv : v.toNat < 64 := v.isLt
  have h := List.all_eq_true.1 dgTable_lsym_all v.toNat (by simpa [List.mem_range] using hv)
  rw [Bridge.Moves.ofNat_toNat_6] at h
  exact beq_iff_eq.1 h

/-- The `DG_T_STOP` group membership of code `v`: `v` is `T.STOP`. -/
theorem dgTable_tstop_iff (v : BitVec 6) :
    (Moves.dgTable v == Moves.dgTStop) = (v == 4) := by
  have hv : v.toNat < 64 := v.isLt
  have h := List.all_eq_true.1 dgTable_tstop_all v.toNat (by simpa [List.mem_range] using hv)
  rw [Bridge.Moves.ofNat_toNat_6] at h
  exact beq_iff_eq.1 h

/-! ## 4. The machine's destination decoder at the keyed groups -/

/-- The machine's `dstOp` is one of the line-symbol ports. -/
def isLsym : Machine.DstOp → Bool
  | .lsym _ => true
  | _ => false

/-- The machine's `dstOp` is the thread-stop port. -/
def isStop : Machine.DstOp → Bool
  | .stop => true
  | _ => false

/-- `isLsym` is "decoder class 1". -/
theorem isLsym_class (o : Machine.DstOp) :
    isLsym o = (Bridge.Moves.dstClassNat o == 1) := by
  cases o <;> rfl

/-- `isStop` is "decoder class 2". -/
theorem isStop_class (o : Machine.DstOp) :
    isStop o = (Bridge.Moves.dstClassNat o == 2) := by
  cases o <;> rfl

/-- Class `1` of the decoder kind table is group `DG_L_SYM`. -/
theorem class1_eq (d : Nat) :
    ((if Bridge.Moves.dgNat d == 0 then 1
      else if Bridge.Moves.dgNat d == 1 then 2
      else if Bridge.Moves.dgNat d == 31 then 0 else 3) == 1) =
      (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgLSym) := by
  have h0 := Bridge.Moves.dgNat_beq_zero d
  have h1 := Bridge.Moves.dgNat_beq_one d
  have h31 := Bridge.Moves.dgNat_beq_31 d
  by_cases hz : (Bridge.Moves.dgNat d == 0) = true
  · have hl : (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgLSym) = true := by rw [← h0]; exact hz
    rw [if_pos hz, hl]
    rfl
  · have hzf : (Bridge.Moves.dgNat d == 0) = false := by simpa using hz
    rw [if_neg (by simpa using hz)]
    have hlf : (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgLSym) = false := by
      rw [← h0]; exact hzf
    rw [hlf]
    by_cases ho : (Bridge.Moves.dgNat d == 1) = true
    · rw [if_pos ho]
      decide
    · rw [if_neg (by simpa using ho)]
      by_cases h3 : (Bridge.Moves.dgNat d == 31) = true
      · rw [if_pos h3]
        decide
      · rw [if_neg (by simpa using h3)]
        decide

/-- Class `2` of the decoder kind table is group `DG_T_STOP`. -/
theorem class2_eq (d : Nat) :
    ((if Bridge.Moves.dgNat d == 0 then 1
      else if Bridge.Moves.dgNat d == 1 then 2
      else if Bridge.Moves.dgNat d == 31 then 0 else 3) == 2) =
      (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTStop) := by
  have h0 := Bridge.Moves.dgNat_beq_zero d
  have h1 := Bridge.Moves.dgNat_beq_one d
  have h31 := Bridge.Moves.dgNat_beq_31 d
  by_cases hz : (Bridge.Moves.dgNat d == 0) = true
  · have htf : (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTStop) = false := by
      rw [← h1]
      have hd0 : Bridge.Moves.dgNat d = 0 := by simpa using hz
      rw [hd0]
      decide
    rw [if_pos hz, htf]
    decide
  · rw [if_neg (by simpa using hz)]
    by_cases ho : (Bridge.Moves.dgNat d == 1) = true
    · have ht : (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTStop) = true := by
        rw [← h1]; exact ho
      rw [if_pos ho, ht]
      rfl
    · rw [if_neg (by simpa using ho)]
      have hof : (Bridge.Moves.dgNat d == 1) = false := by simpa using ho
      have htf : (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTStop) = false := by
        rw [← h1]; exact hof
      rw [htf]
      by_cases h3 : (Bridge.Moves.dgNat d == 31) = true
      · rw [if_pos h3]
        decide
      · rw [if_neg (by simpa using h3)]
        decide

/-- **The machine's `L.SYM` decode is the cut's `DG_L_SYM` group.** -/
theorem isLsym_eq_group (hkind : Bridge.Moves.DstKindTable) {d : Nat} (hd : d < 64) :
    isLsym (Machine.dstOp d) = (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgLSym) := by
  rw [isLsym_class, hkind d hd]
  exact class1_eq d

/-- **The machine's `T.STOP` decode is the cut's `DG_T_STOP` group.** -/
theorem isStop_eq_group (hkind : Bridge.Moves.DstKindTable) {d : Nat} (hd : d < 64) :
    isStop (Machine.dstOp d) = (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTStop) := by
  rw [isStop_class, hkind d hd]
  exact class2_eq d

/-- **The `L.SYM` decode at the cut's destination code range.** -/
theorem isLsym_iff_range (hkind : Bridge.Moves.DstKindTable) (v : BitVec 6) :
    isLsym (Machine.dstOp v.toNat) = (v <= 3 && v != 0) := by
  rw [isLsym_eq_group hkind v.isLt, dgTable_lsym_iff, Bridge.Moves.ofNat_toNat_6]

/-- **The `T.STOP` decode at the cut's destination code range.** -/
theorem isStop_iff_code (hkind : Bridge.Moves.DstKindTable) (v : BitVec 6) :
    isStop (Machine.dstOp v.toNat) = (v == 4) := by
  rw [isStop_eq_group hkind v.isLt, dgTable_tstop_iff, Bridge.Moves.ofNat_toNat_6]

/-- A small-index `BitVec` equality forces the `Nat` equality. -/
theorem ofNat3_eq {x t : Nat} (hx : x < 8) (ht : t < 8)
    (h : (BitVec.ofNat 3 x == BitVec.ofNat 3 t) = true) : x = t := by
  have hh : BitVec.ofNat 3 x = BitVec.ofNat 3 t := by simpa using h
  have h' := congrArg BitVec.toNat hh
  simp only [BitVec.toNat_ofNat, show (2 : Nat) ^ 3 = 8 from by decide] at h'
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt ht] at h'
  exact h'

/-! ## 5. The machine's slot data -/

/-- The machine's enabled move list of the cycle is the cut-side `mAllMoves`. -/
theorem mAllMoves_ltAllMoves (m : Machine.State) (pin : Machine.PinIn) :
    ltAllMoves m = mAllMoves m pin := by
  show (ltCbs m)[0].moves ++ (ltCbs m)[1].moves = _
  have h0 : (ltCbs m)[0] = mCoreComb m pin 0 := by simp [ltCbs, mCoreComb]
  have h1 : (ltCbs m)[1] = mCoreComb m pin 1 := by simp [ltCbs, mCoreComb]
  rw [h0, h1]
  rfl

/-- The move at a machine slot carries the cut's thread slice. -/
theorem machMove_thread (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (q : Nat) (hq : q < 6)
    (h : ((movBundle s pin).get q).enabled = true) :
    (machMove s m pin q).thread = (slotThread s pin q).toNat := by
  rw [hbus.thread q hq]
  rfl

/-- The move at a machine slot carries the cut's destination slice. -/
theorem machMove_dstSlot (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (q : Nat) (hq : q < 6)
    (h : ((movBundle s pin).get q).enabled = true) :
    (machMove s m pin q).dst = (slotDst s pin q).toNat := by
  rw [machMove_dst s m pin hbus q hq h, movBundle_dst s pin q hq]
  rfl

/-- `moveVal`'s `armed` field is that of the executing thread. -/
theorem moveVal_armed {ms : Machine.State} {cv : Machine.CfgView} {p : Machine.PinView}
    {x : Core.State} {c mm : Nat} :
    (Bridge.Core.moveVal ms cv p x c mm).armed =
      (Machine.Util.vget ms.threads (Bridge.Core.moveVal ms cv p x c mm).thread).armed := by
  simp only [Bridge.Core.moveVal]

/-- The machine's move at a slot is the cut core's `moveVal` (so its `armed` field
is the executing thread's). -/
theorem slotArmed (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hcore : ∀ c : Fin 2, Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (sIr s m c) (coreIn s pin c.val))
    (hfrz : ∀ c : Fin 2, m.dbg.frz = (coreIn s pin c.val).frz)
    (q : Nat) (hq : q < 6) {mv : Machine.Move} (hmv : machSlot m pin q = some mv) :
    mv.armed = (Machine.Util.vget m.threads mv.thread).armed := by
  obtain ⟨c, mi, hmi, hqeq⟩ := slot_split q hq
  subst hqeq
  have hmv1 : Bridge.Core.moveAt (Machine.coreComb m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (Bridge.Core.coreNat (c.val == 1))
      (coreIn s pin c.val).frz) mi = some mv := by
    rw [← machSlot_eq s m pin c mi hmi (hfrz c)]
    exact hmv
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
  rw [hval, moveVal_armed]

/-- The machine's thread register `u` is the cut's. -/
theorem threads_armed (s : State) (m : Machine.State) (hrel : ChipRel s m) {u : Nat}
    (hu : u < 6) :
    (Machine.Util.vget m.threads u).armed = (threadAt s u).armed := by
  rw [threads_eq hrel hu]
  rfl

/-! ## 6. The keyed hit -/

/-- The keyed hit of slot `q` for group `G`, key `K`: valid, in the group, and the
key matches.  With `win` for `valid` this is the cut's `symMask` bit. -/
def keyedHit (b : Moves.Bundle) (G : BitVec 5) (key : Moves.Slot → Bool) (q : Nat) : Bool :=
  Moves.validAt (b.get q) && ((b.get q).group == G) && (key (b.get q))

/-- The cut's key of the `T.STOP` group: the slot's thread. -/
def threadKey (t : BitVec 3) : Moves.Slot → Bool := fun sl => sl.thread == t

/-- The cut's key of the `L.SYM` group: the slot's line. -/
def lineKey (l : BitVec 2) : Moves.Slot → Bool := fun sl => sl.line == l

/-- A keyed hit is valid. -/
theorem keyedHit_valid {b : Moves.Bundle} {G : BitVec 5} {key : Moves.Slot → Bool} {q : Nat}
    (h : keyedHit b G key q = true) : Moves.validAt (b.get q) = true := by
  unfold keyedHit at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.1

/-- A keyed hit is in the group. -/
theorem keyedHit_group {b : Moves.Bundle} {G : BitVec 5} {key : Moves.Slot → Bool} {q : Nat}
    (h : keyedHit b G key q = true) : ((b.get q).group == G) = true := by
  unfold keyedHit at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.2

/-- A keyed hit has the key. -/
theorem keyedHit_key {b : Moves.Bundle} {G : BitVec 5} {key : Moves.Slot → Bool} {q : Nat}
    (h : keyedHit b G key q = true) : key (b.get q) = true := by
  unfold keyedHit at h
  rw [Bool.and_eq_true] at h
  exact h.2

/-! ## 7. The first keyed hit wins -/

/-- The `slotKey` of a `T.STOP` slot keyed by `thread`. -/
theorem slotKey_stop {sl : Moves.Slot} {t : Nat} (hg : sl.group = Moves.dgTStop)
    (ht : sl.thread.toNat = t) :
    Bridge.Moves.slotKey sl = some (Moves.dgTStop.toNat, t) := by
  have hne : (sl.group == Moves.dgNone) = false := by rw [hg]; decide
  rw [show Bridge.Moves.slotKey sl = some (sl.group.toNat, Bridge.Moves.disc sl) from by
    unfold Bridge.Moves.slotKey
    rw [hne]
    rfl]
  rw [hg, Bridge.Moves.disc_tstop (by rw [hg]; rfl), ht]

/-- **The first keyed hit of a `T.STOP` key wins.**  Everything that could block
the keyed hit at `k` has the same key (`Bridge.Moves.sameKey_iff_slotKey`), so it
is a keyed hit of an earlier slot — which `hfirst` excludes. -/
theorem winAt_of_keyed_first_stop (s : State) (pin : Machine.PinIn) (t : Fin 6) {k : Nat}
    (hfirst : ∀ j, j < k →
      keyedHit (movBundle s pin) Moves.dgTStop (threadKey (BitVec.ofNat 3 t.val)) j = false)
    (hhit : keyedHit (movBundle s pin) Moves.dgTStop (threadKey (BitVec.ofNat 3 t.val)) k = true) :
    Moves.winAt (movBundle s pin) k = true := by
  have hgk := keyedHit_group hhit
  have hkeyk := keyedHit_key hhit
  have hb : Moves.blocked (movBundle s pin) k = false := by
    by_cases h : Moves.blocked (movBundle s pin) k = true
    · rw [Moves.blocked_spec] at h
      obtain ⟨j, hj, hv, hsk⟩ := h
      have hkey := (Bridge.Moves.sameKey_iff_slotKey ((movBundle s pin).get j)
        ((movBundle s pin).get k)).1 hsk
      -- the blocking slot has the same group and thread as the hit at `k`
      have hgg : (((movBundle s pin).get j).group == ((movBundle s pin).get k).group) = true := by
        unfold Moves.sameKey at hsk
        rw [Bool.and_eq_true, Bool.and_eq_true] at hsk
        exact hsk.1.1
      have hgk' : ((movBundle s pin).get k).group = Moves.dgTStop := by
        rw [beq_iff_eq] at hgk
        exact hgk
      have hgj' : ((movBundle s pin).get j).group = Moves.dgTStop := by
        have h1 := hgg
        rw [hgk'] at h1
        rwa [beq_iff_eq] at h1
      have hgj : (((movBundle s pin).get j).group == Moves.dgTStop) = true := by
        rw [hgj']; rfl
      have hkj : ((movBundle s pin).get k).thread.toNat = t.val := by
        unfold threadKey at hkeyk
        rw [beq_iff_eq] at hkeyk
        rw [hkeyk, BitVec.toNat_ofNat, show (2 : Nat) ^ 3 = 8 from by decide,
          Nat.mod_eq_of_lt (by omega)]
      have hdisc : Bridge.Moves.disc ((movBundle s pin).get j) = t.val := by
        have hne : (((movBundle s pin).get j).group == Moves.dgNone) = false := by
          rw [hgj']
          decide
        rw [show Bridge.Moves.slotKey ((movBundle s pin).get j) =
            some (Moves.dgTStop.toNat, Bridge.Moves.disc ((movBundle s pin).get j)) from by
          unfold Bridge.Moves.slotKey
          rw [hne, hgj']
          simp] at hkey
        rw [slotKey_stop (t := t.val) hgk' hkj] at hkey
        exact congrArg Prod.snd (Option.some.inj hkey)
      have hjj : ((movBundle s pin).get j).thread.toNat = t.val := by
        rw [← hdisc, Bridge.Moves.disc_tstop hgj]
      have : keyedHit (movBundle s pin) Moves.dgTStop (threadKey (BitVec.ofNat 3 t.val)) j
          = true := by
        have hthr : threadKey (BitVec.ofNat 3 t.val) ((movBundle s pin).get j) = true := by
          unfold threadKey
          rw [beq_iff_eq]
          apply BitVec.eq_of_toNat_eq
          rw [hjj, BitVec.toNat_ofNat, show (2 : Nat) ^ 3 = 8 from by decide,
            Nat.mod_eq_of_lt (by omega)]
        unfold keyedHit
        rw [hv, hgj, hthr]
        rfl
      rw [hfirst j hj] at this
      exact absurd this (by decide)
    · cases hbb : Moves.blocked (movBundle s pin) k with
      | false => rfl
      | true => rw [hbb] at h; exact absurd rfl h
  exact Moves.winAt_true_of_unblocked (keyedHit_valid hhit) hb

/-! ## 8. The hypothesis bundle of the field theorems -/

/-- The global jump-guard table hypothesis (`DstKindTable`'s sibling). -/
abbrev JGTable : Prop := ∀ n : Nat,
  Machine.Util.jumpGuardIdx.getD n Machine.Tables.guardNames.size = Core.JG_TABLE.getD n 62

/-- The cut-side group-packing identity (`WIRE_MOVEFABRIC_NOTES` §4). -/
abbrev GrpPacked (s : State) (pin : Machine.PinIn) : Prop :=
  ∀ q, q < 6 → ((movBundle s pin).get q).group = Moves.dgTable ((movBundle s pin).get q).dst

/-- A `filterMap` scan: the `some` entries are tested and the `none` entries are
replaced by the cut predicate, which must be `false` on them. -/
theorem any_filterMap_split {α : Type} {β : Type} (l : List α) (g : α → Option β)
    (f : β → Bool) (F : α → Bool)
    (h : ∀ a ∈ l, ∀ b, g a = some b → f b = F a)
    (h0 : ∀ a ∈ l, g a = none → F a = false) :
    (l.filterMap g).any f = l.any F := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.filterMap_cons]
    cases hga : g a with
    | none =>
      have hFa : F a = false := h0 a (by simp) hga
      simp only [hga, List.any_cons, hFa, Bool.false_or]
      exact ih (fun b hb c hc => h b (by simp [hb]) c hc)
        (fun b hb => h0 b (by simp [hb]))
    | some b =>
      have hFb : f b = F a := h a (by simp) b hga
      simp only [hga, List.any_cons]
      rw [hFb, ih (fun c hc b' hb' => h c (by simp [hc]) b' hb')
        (fun c hc => h0 c (by simp [hc]))]

/-- An `any` of guarded terms: under the guard the branches agree, off it both are
`false`. -/
theorem any_ite_congr (l : List Nat) (c F G : Nat → Bool)
    (h : ∀ a ∈ l, c a = true → F a = G a) :
    l.any (fun a => if c a then F a else false) =
      l.any (fun a => if c a then G a else false) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.any_cons]
    by_cases hc : c a = true
    · rw [if_pos hc, if_pos hc, h a (by simp) hc,
        ih (fun b hb => h b (by simp [hb]))]
    · have hcf : c a = false := by simpa using hc
      rw [if_neg hc, if_neg hc, ih (fun b hb => h b (by simp [hb]))]

/-- An enabled slot whose destination is a line-symbol port is valid. -/
theorem slotValid_of_range (s : State) (pin : Machine.PinIn) (q : Nat) (hq : q < 6)
    (hgrp : GrpPacked s pin)
    (hen : ((movBundle s pin).get q).enabled = true)
    (hD : (slotDst s pin q <= 3 && slotDst s pin q != 0) = true) :
    slotValid s pin q = true := by
  have hdst := movBundle_dst_slot s pin q hq
  have hg : ((movBundle s pin).get q).group = Moves.dgTable (slotDst s pin q) := by
    rw [hgrp q hq, hdst]
  have hlsym : (Moves.dgTable (slotDst s pin q) == Moves.dgLSym) = true := by
    rw [dgTable_lsym_iff]
    exact hD
  have hne : (Moves.dgTable (slotDst s pin q) == Moves.dgNone) = false := by
    by_cases hx : (Moves.dgTable (slotDst s pin q) == Moves.dgNone) = true
    · rw [beq_iff_eq] at hx
      rw [beq_iff_eq] at hlsym
      rw [hlsym] at hx
      exact absurd hx (by decide)
    · simpa using hx
  rw [slotValid_eq s pin q hq, hen, hg, hne]
  rfl

/-- An enabled slot whose destination is `T.STOP` is valid. -/
theorem slotValid_of_stop (s : State) (pin : Machine.PinIn) (q : Nat) (hq : q < 6)
    (hgrp : GrpPacked s pin)
    (hen : ((movBundle s pin).get q).enabled = true)
    (hD : (slotDst s pin q == 4) = true) :
    slotValid s pin q = true := by
  have hdst := movBundle_dst_slot s pin q hq
  have hg : ((movBundle s pin).get q).group = Moves.dgTable (slotDst s pin q) := by
    rw [hgrp q hq, hdst]
  have htstop : (Moves.dgTable (slotDst s pin q) == Moves.dgTStop) = true := by
    rw [dgTable_tstop_iff]
    exact hD
  have hne : (Moves.dgTable (slotDst s pin q) == Moves.dgNone) = false := by
    by_cases hx : (Moves.dgTable (slotDst s pin q) == Moves.dgNone) = true
    · rw [beq_iff_eq] at hx
      rw [beq_iff_eq] at htstop
      rw [htstop] at hx
      exact absurd hx (by decide)
    · simpa using hx
  rw [slotValid_eq s pin q hq, hen, hg, hne]
  rfl

/-- The machine's move thread is the cut's thread slice, as a `Bool` equality. -/
theorem thread_beq_slot (s : State) (pin : Machine.PinIn)
    {mv : Machine.Move} {q : Nat} (hthr : mv.thread = (slotThread s pin q).toNat)
    (t : Fin 6) :
    (mv.thread == t.val) = (slotThread s pin q == BitVec.ofNat 3 t.val) := by
  rw [hthr]
  apply Bool.eq_iff_iff.2
  constructor
  · intro h
    have hx : (slotThread s pin q).toNat = t.val := by simpa using h
    rw [← hx]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact beq_iff_eq.2 rfl
  · intro h
    have hx : slotThread s pin q = BitVec.ofNat 3 t.val := by simpa using h
    rw [hx, BitVec.toNat_ofNat, show (2 : Nat) ^ 3 = 8 from by decide,
      Nat.mod_eq_of_lt (by omega)]
    simp

/-! ## 9. `WireAgree.late` -/

/-- The machine's late-symbol scan of one move. -/
def lateMove (t : Fin 6) (mv : Machine.Move) : Bool :=
  mv.thread == t.val && !mv.armed && isLsym (Machine.dstOp mv.dst)

/-- The cut's late-symbol scan of one slot. -/
def lateCut (s : State) (pin : Machine.PinIn) (t : Fin 6) (q : Nat) : Bool :=
  slotValid s pin q && slotDst s pin q <= 3 && slotDst s pin q != 0 &&
    slotThread s pin q == BitVec.ofNat 3 t.val && !(threadAt s t.val).armed

/-- **The `late` per-slot identity on a live slot.** -/
theorem lateSlot (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin)
    (hcore : ∀ c : Fin 2, Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (sIr s m c) (coreIn s pin c.val))
    (hfrz : ∀ c : Fin 2, m.dbg.frz = (coreIn s pin c.val).frz)
    (hrel : ChipRel s m) (hgrp : GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (t : Fin 6) (q : Nat) (hq : q < 6) {mv : Machine.Move}
    (hmv : machSlot m pin q = some mv) :
    lateMove t mv = lateCut s pin t q := by
  have hen : ((movBundle s pin).get q).enabled = true := by
    rw [← machSlot_isSome s m pin hbus q hq, hmv]
    rfl
  unfold lateMove lateCut
  have hthr : mv.thread = (slotThread s pin q).toNat := by
    rw [← machMove_of_some hmv]
    exact machMove_thread s m pin hbus q hq hen
  have hdst : mv.dst = (slotDst s pin q).toNat := by
    rw [← machMove_of_some hmv]
    exact machMove_dstSlot s m pin hbus q hq hen
  have harm : mv.armed = (Machine.Util.vget m.threads mv.thread).armed :=
    slotArmed s m pin hcore hfrz q hq hmv
  have hkey := thread_beq_slot s pin hthr t
  have hls : isLsym (Machine.dstOp mv.dst) =
      (slotDst s pin q <= 3 && slotDst s pin q != 0) := by
    rw [hdst]
    exact isLsym_iff_range hkind (slotDst s pin q)
  by_cases hL : isLsym (Machine.dstOp mv.dst) = true
  · have hD : (slotDst s pin q <= 3 && slotDst s pin q != 0) = true := by
      rw [← hls]; exact hL
    have hV : slotValid s pin q = true := slotValid_of_range s pin q hq hgrp hen hD
    have hVD : ((slotValid s pin q && slotDst s pin q <= 3) && slotDst s pin q != 0)
        = true := by
      rw [Bool.and_assoc, hD, Bool.and_true]
      exact hV
    by_cases hA : (slotThread s pin q == BitVec.ofNat 3 t.val) = true
    · have hmvt : mv.thread = t.val := by
        have hh : (BitVec.ofNat 3 mv.thread == BitVec.ofNat 3 t.val) = true := by
          rw [hthr]
          rw [show BitVec.ofNat 3 (slotThread s pin q).toNat = slotThread s pin q from by
            rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]]
          exact hA
        exact ofNat3_eq (by rw [hthr]; simpa using (slotThread s pin q).isLt)
          (by omega) hh
      have harmT : mv.armed = (threadAt s t.val).armed := by
        rw [harm, hmvt, threads_armed s m hrel t.isLt]
      rw [hkey, hA, hL, hVD, harmT]
      cases (threadAt s t.val).armed <;> rfl
    · have hAf : (slotThread s pin q == BitVec.ofNat 3 t.val) = false := by
        simpa using hA
      rw [hkey, hAf]
      simp
  · have hLf : isLsym (Machine.dstOp mv.dst) = false := by simpa using hL
    have hDf : (slotDst s pin q <= 3 && slotDst s pin q != 0) = false := by
      rw [← hls]; exact hLf
    have hz : ((slotValid s pin q && slotDst s pin q <= 3) && slotDst s pin q != 0)
        = false := by
      rw [Bool.and_assoc, hDf, Bool.and_false]
    rw [hLf, hz]
    simp

/-- A disabled slot is not late on the cut side. -/
theorem lateCut_false (s : State) (pin : Machine.PinIn) (t : Fin 6) (q : Nat) (hq : q < 6)
    (hf : ((movBundle s pin).get q).enabled = false) :
    lateCut s pin t q = false := by
  unfold lateCut
  rw [slotValid_eq s pin q hq, hf]
  rfl

/-- **`WireAgree.late`**: the machine's `ltAllMoves` late scan is the cut's
`slotValid`-based per-thread late test. -/
theorem wireAgree_late (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : JGTable) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable) (t : Fin 6) :
    (ltThreadIn m t).late =
      (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).late := by
  have hbusM := moveBus_of_chipRel s m pin hrel hinv hJGTab hbus hgrp
  have hcore : ∀ c : Fin 2, Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (sIr s m c) (coreIn s pin c.val) :=
    fun c => rel_of_bus s m pin c hrel hinv (hbus c)
  have hfrz : ∀ c : Fin 2, m.dbg.frz = (coreIn s pin c.val).frz := fun c => by
    rw [hrel.dbg.2.1]; simp [coreIn]
  have hlhs : (ltThreadIn m t).late = (mAllMoves m pin).any (lateMove t) := by
    show (ltAllMoves m).any (lateMove t) = (mAllMoves m pin).any (lateMove t)
    rw [mAllMoves_ltAllMoves]
  have hscan : (mAllMoves m pin).any (lateMove t) =
      (List.range 6).any (lateCut s pin t) := by
    rw [mAllMoves_enum s m pin hcore hfrz]
    refine any_filterMap_split (List.range 6) (machSlot m pin) (lateMove t)
      (lateCut s pin t) ?_ ?_
    · intro q hq mv hmv
      rw [List.mem_range] at hq
      exact lateSlot s m pin hbusM hcore hfrz hrel hgrp hkind t q hq hmv
    · intro q hq hnone
      rw [List.mem_range] at hq
      have hs : (machSlot m pin q).isSome = false := by rw [hnone]; rfl
      rw [machSlot_isSome s m pin hbusM q hq] at hs
      exact lateCut_false s pin t q hq hs
  rw [hlhs, hscan, ← anySix_eq_any]
  rfl

/-! ## 10. `WireAgree.stop` -/

/-- The machine's stop scan of one move. -/
def stopMove (t : Fin 6) (mv : Machine.Move) : Bool :=
  mv.thread == t.val && isStop (Machine.dstOp mv.dst)

/-- The cut's stop scan of one slot. -/
def stopCut (s : State) (pin : Machine.PinIn) (t : Fin 6) : Nat → Bool :=
  fun q => slotValid s pin q && slotDst s pin q == 4 &&
    slotThread s pin q == BitVec.ofNat 3 t.val

/-- The cut's stop predicate of a slot is the keyed hit of the `T.STOP` group. -/
theorem stopCut_eq_keyedHit (s : State) (pin : Machine.PinIn) (t : Fin 6) (q : Nat) (hq : q < 6)
    (hgrp : GrpPacked s pin) :
    stopCut s pin t q = keyedHit (movBundle s pin) Moves.dgTStop
      (threadKey (BitVec.ofNat 3 t.val)) q := by
  have hdst := movBundle_dst_slot s pin q hq
  have hthr := movBundle_thread_slot s pin q hq
  have hg : ((movBundle s pin).get q).group = Moves.dgTable (slotDst s pin q) := by
    rw [hgrp q hq, hdst]
  have hgrpk : (((movBundle s pin).get q).group == Moves.dgTStop) =
      (slotDst s pin q == 4) := by
    rw [hg, show Moves.dgTable (slotDst s pin q) =
      Moves.dgTable (BitVec.ofNat 6 (slotDst s pin q).toNat) from by
        rw [Bridge.Moves.ofNat_toNat_6], dgTable_tstop_iff, Bridge.Moves.ofNat_toNat_6]
  have hvalid : Moves.validAt ((movBundle s pin).get q) = slotValid s pin q :=
    (slotValid_eq s pin q hq).symm
  unfold stopCut keyedHit threadKey
  rw [hvalid, hgrpk, hthr]

/-- **The `stop` per-slot identity on a live slot.** -/
theorem stopSlot (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (hgrp : GrpPacked s pin)
    (hkind : Bridge.Moves.DstKindTable) (t : Fin 6) (q : Nat) (hq : q < 6)
    (hen : ((movBundle s pin).get q).enabled = true) :
    stopMove t (machMove s m pin q) = stopCut s pin t q := by
  unfold stopMove stopCut
  have hthr : (machMove s m pin q).thread = (slotThread s pin q).toNat :=
    machMove_thread s m pin hbus q hq hen
  have hdst : (machMove s m pin q).dst = (slotDst s pin q).toNat :=
    machMove_dstSlot s m pin hbus q hq hen
  have hkey := thread_beq_slot s pin hthr t
  have hls : isStop (Machine.dstOp (machMove s m pin q).dst) = (slotDst s pin q == 4) := by
    rw [hdst]
    exact isStop_iff_code hkind (slotDst s pin q)
  by_cases hL : isStop (Machine.dstOp (machMove s m pin q).dst) = true
  · have hD : (slotDst s pin q == 4) = true := by rw [← hls]; exact hL
    have hV : slotValid s pin q = true := slotValid_of_stop s pin q hq hgrp hen hD
    rw [hkey, hL, hD, hV]
    cases (slotThread s pin q == BitVec.ofNat 3 t.val) <;> rfl
  · have hLf : isStop (Machine.dstOp (machMove s m pin q).dst) = false := by
      simpa using hL
    have hDf : (slotDst s pin q == 4) = false := by rw [← hls]; exact hLf
    rw [hkey, hLf, hDf]
    simp

/-- **The winner scan and the valid-bit scan select the same slots.**  The first
keyed hit wins, so "some winner is a keyed hit" is "some slot is a keyed hit". -/
theorem any_win_stop_eq (s : State) (pin : Machine.PinIn) (t : Fin 6)
    (hgrp : GrpPacked s pin) :
    (List.range 6).any (fun q => if Moves.winAt (movBundle s pin) q
        then stopCut s pin t q else false) =
      (List.range 6).any (stopCut s pin t) := by
  apply Bool.eq_iff_iff.2
  constructor
  · intro h
    obtain ⟨q, hq, hqtrue⟩ := List.any_eq_true.1 h
    rw [List.mem_range] at hq
    by_cases hw : Moves.winAt (movBundle s pin) q = true
    · rw [if_pos hw] at hqtrue
      exact List.any_eq_true.2 ⟨q, by simpa using hq, hqtrue⟩
    · rw [if_neg hw] at hqtrue
      exact absurd hqtrue (by decide)
  · intro h
    obtain ⟨q, hq, hqtrue⟩ := List.any_eq_true.1 h
    rw [List.mem_range] at hq
    have hne : (List.range 6).find? (stopCut s pin t) ≠ none := by
      intro hz
      have hall := List.find?_eq_none.1 hz
      have := hall q (by simpa using hq)
      rw [hqtrue] at this
      exact absurd this (by decide)
    obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 hne
    have hhit : stopCut s pin t j = true := List.find?_some hj
    have hjmem : j ∈ List.range 6 := List.mem_of_find?_eq_some hj
    have hj6 : j < 6 := List.mem_range.mp hjmem
    have hfirst : ∀ i, i < j → stopCut s pin t i = false :=
      range_find?_before (stopCut s pin t) 6 j hj
    have hkeyed : keyedHit (movBundle s pin) Moves.dgTStop
        (threadKey (BitVec.ofNat 3 t.val)) j = true := by
      rw [← stopCut_eq_keyedHit s pin t j hj6 hgrp]
      exact hhit
    have hkfirst : ∀ i, i < j → keyedHit (movBundle s pin) Moves.dgTStop
        (threadKey (BitVec.ofNat 3 t.val)) i = false := by
      intro i hi
      rw [← stopCut_eq_keyedHit s pin t i (by omega) hgrp]
      exact hfirst i hi
    have hwin := winAt_of_keyed_first_stop s pin t hkfirst hkeyed
    exact List.any_eq_true.2 ⟨j, by simpa using hjmem, by rw [if_pos hwin]; exact hhit⟩

/-- **`WireAgree.stop`**: the machine's winner scan for `T.STOP` is the cut's
per-thread `slotValid` test. -/
theorem wireAgree_stop (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s)
    (hJGTab : JGTable) (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable) (t : Fin 6) :
    (ltThreadIn m t).stop =
      (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).stop := by
  have hbusM := moveBus_of_chipRel s m pin hrel hinv hJGTab hbus hgrp
  have hcore : ∀ c : Fin 2, Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (sIr s m c) (coreIn s pin c.val) :=
    fun c => rel_of_bus s m pin c hrel hinv (hbus c)
  have hfrz : ∀ c : Fin 2, m.dbg.frz = (coreIn s pin c.val).frz := fun c => by
    rw [hrel.dbg.2.1]; simp [coreIn]
  have hws : ltWs m = (List.range 6).filterMap (fun k =>
      if Moves.winAt (movBundle s pin) k then some (machMove s m pin k) else none) := by
    have h1 : ltWs m = mWs m pin := by
      show (Machine.resolveMoves (ltAllMoves m)).1 =
        (Machine.resolveMoves (mAllMoves m pin)).1
      rw [mAllMoves_ltAllMoves]
    rw [h1, mWs_eq_six s m pin hkind hcore hfrz,
      (winners_machMove s m pin hkind hbusM).1]
  have hlhs : (ltThreadIn m t).stop = (ltWs m).any (stopMove t) := by
    rw [ltThreadIn]
    rfl
  have hscan1 : (ltWs m).any (stopMove t) =
      (List.range 6).any (fun k => if Moves.winAt (movBundle s pin) k
        then stopMove t (machMove s m pin k) else false) := by
    rw [hws]
    exact any_filterMap_ite _ _ _ _
  have hscan2 : (List.range 6).any (fun k => if Moves.winAt (movBundle s pin) k
        then stopMove t (machMove s m pin k) else false) =
      (List.range 6).any (fun k => if Moves.winAt (movBundle s pin) k
        then stopCut s pin t k else false) := by
    refine any_ite_congr (List.range 6) (fun k => Moves.winAt (movBundle s pin) k)
      (fun k => stopMove t (machMove s m pin k)) (fun k => stopCut s pin t k) ?_
    intro k hk hw
    rw [List.mem_range] at hk
    have hv : Moves.validAt ((movBundle s pin).get k) = true := Moves.winAt_valid hw
    have hen : ((movBundle s pin).get k).enabled = true := by
      have h2 := hv
      rw [show Moves.validAt ((movBundle s pin).get k) =
        (((movBundle s pin).get k).enabled &&
          !(((movBundle s pin).get k).group == Moves.dgNone)) from rfl] at h2
      rw [Bool.and_eq_true] at h2
      exact h2.1
    exact stopSlot s m pin hbusM hgrp hkind t k hk hen
  rw [hlhs, hscan1, hscan2, any_win_stop_eq s pin t hgrp, ← anySix_eq_any]
  rfl

/-! ## 11. The pointer move: `MemHostCfg.p0_open_move` -/

/-- `mhcWs` is the same winner list as `mWs`. -/
theorem mhcWs_eq_mWs (m : Machine.State) (pin : Machine.PinIn) :
    mhcWs m pin = mWs m pin := by
  show (Machine.resolveMoves ((mhcCbs m pin)[0].moves ++ (mhcCbs m pin)[1].moves)).1 =
    (Machine.resolveMoves ((mCoreComb m pin 0).moves ++ (mCoreComb m pin 1).moves)).1
  have h0 : (mhcCbs m pin)[0] = mCoreComb m pin 0 := by simp [mhcCbs, mCoreComb]
  have h1 : (mhcCbs m pin)[1] = mCoreComb m pin 1 := by simp [mhcCbs, mCoreComb]
  rw [h0, h1]

/-- Pointwise equality of the six-way disjunctions. -/
theorem anySix_congr (f g : Nat → Bool) (h : ∀ q, q < 6 → f q = g q) : anySix f = anySix g := by
  simp only [anySix, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
    h 4 (by omega), h 5 (by omega)]

/-- The generic `findSome?`/`Option.map` bridge for a two-field record. -/
theorem findSome?_map_pair {α : Type} {β : Type} {γ : Type} (l : List α) (f : α → Option β)
    (g : α → Nat) (c : β → Nat → γ) :
    ((l.findSome? (fun x => (f x).map (fun a => (a, g x)))).map (fun p : β × Nat => c p.1 p.2))
      = l.findSome? (fun x => (f x).map (fun a => c a (g x))) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.findSome?_cons, List.findSome?_cons]
    cases hb : f a with
    | none => simpa only [Option.map_none, Option.none_or] using ih
    | some b => rfl

/-- The machine's pointer-move decode as the payload of the `P0` write group. -/
def p0MoveOf : Machine.DstOp → Option Nat
  | .pAl => some 0
  | .pAh => some 1
  | .pW => some 2
  | .pR => some 3
  | _ => none

/-- **`MemHostCfg.p0_open_move`**: the machine's `P0` winner is the cut's pointer
port pick of write group `17` (codes 43..46), through `pickWord`.  The remaining
hypothesis `hPQ` is the `Fam.p0` instance of the payload table
(`WIRE_MOVEFABRIC_NOTES` §9). -/
theorem p0_open_move (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hJGTab : JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hPQ : ∀ d, d < 64 → p0MoveOf (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTable 43) then
        some ((Strobes.p0Sel (BitVec.ofNat 6 d)).toNat) else none)) :
    mhcP0Move m pin = Bridge.Mem.mvOf (memIn s pin) := by
  have hGb : (Moves.dgTable 43 == Moves.dgNone) = false := by decide
  have hG0 : (Moves.dgTable 43 == Moves.dgLSym) = false := by decide
  have hG1 : (Moves.dgTable 43 == Moves.dgTStop) = false := by decide
  have hscan := pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
    p0MoveOf (fun dst => some ((Strobes.p0Sel dst).toNat)) (fun v => v) (Moves.dgTable 43)
    hGb hG0 hG1 hPQ
  have h1 : mhcP0Move m pin =
      ((mhcWs m pin).findSome? (fun mv => (p0MoveOf (Machine.dstOp mv.dst)).map
        (fun a => (a, mv.v)))).map (fun p : Nat × Nat => (⟨p.1, p.2⟩ : Machine.P0Move)) := by
    rw [show mhcP0Move m pin = (mhcWs m pin).findSome? (fun mm =>
        match Machine.dstOp mm.dst with
        | .pAl => some ⟨0, mm.v⟩ | .pAh => some ⟨1, mm.v⟩
        | .pW => some ⟨2, mm.v⟩ | .pR => some ⟨3, mm.v⟩ | _ => none) from rfl]
    rw [show (fun mm : Machine.Move => match Machine.dstOp mm.dst with
        | .pAl => some ⟨0, mm.v⟩ | .pAh => some ⟨1, mm.v⟩
        | .pW => some ⟨2, mm.v⟩ | .pR => some ⟨3, mm.v⟩ | _ => none) =
      (fun mv => (p0MoveOf (Machine.dstOp mv.dst)).map
        (fun a => (⟨a, mv.v⟩ : Machine.P0Move))) from
      funext (fun x => by cases Machine.dstOp x.dst <;> rfl)]
    exact (findSome?_map_pair (mhcWs m pin) (fun mv => p0MoveOf (Machine.dstOp mv.dst))
      (fun mv => mv.v) (fun a b => (⟨a, b⟩ : Machine.P0Move))).symm
  rw [h1, mhcWs_eq_mWs, hscan]
  rw [show Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (Moves.dgTable 43))
      (mvDst s pin) (mvDat s pin) = gw s pin 43 from rfl]
  rw [show Bridge.Mem.mvOf (memIn s pin) = (if (gw s pin 43).we then
      some ⟨(Strobes.p0Sel (gw s pin 43).dst).toNat, (gw s pin 43).data.toNat⟩
      else none) from rfl]
  cases (gw s pin 43).we <;> rfl

/-! ## 12. The `HOST.IN` read: `CtrlMoveFabric.hostInRead` -/

/-- The machine's `srcOp` is the host mailbox read. -/
def isHostIn : Machine.SrcOp → Bool
  | .hostIn => true
  | _ => false

/-- `isHostIn` is "source class 2". -/
theorem isHostIn_class (o : Machine.SrcOp) :
    isHostIn o = (Bridge.Moves.srcClassNat o == 2) := by
  cases o <;> rfl

/-- The source table's `HOST.IN` code is `38` alone.  The table is the total,
computable `srcOpOf` of `Bridge.Glue` (`SrcTable`), so this is a 64-code kernel
check. -/
theorem srcOpOf_hostIn_all :
    (List.range 64).all (fun d => ((Bridge.Moves.srcClassNat (Bridge.Glue.srcOpOf d) == 2) ==
      ((BitVec.ofNat 6 d) == Moves.srcHostIn))) = true := by
  decide

/-- **The `HOST.IN` decode is the cut's source code `38`.** -/
theorem srcHostIn_iff (hsrc : Bridge.Glue.SrcTable) {d : Nat} (hd : d < 64) :
    isHostIn (Machine.srcOp d) = (BitVec.ofNat 6 d == Moves.srcHostIn) := by
  rw [isHostIn_class, hsrc.eq d]
  have h := List.all_eq_true.1 srcOpOf_hostIn_all d (by simpa [List.mem_range] using hd)
  exact beq_iff_eq.1 h

/-- The machine's `hostInRead` scan of the cycle. -/
theorem ctrlInTrue_hostInRead (m : Machine.State) (pin : Machine.PinIn) :
    (ctrlInTrue m pin).hostInRead =
      (ltAllMoves m).any (fun mv => isHostIn (Machine.srcOp mv.src)) := by
  simp only [ctrlInTrue, ltAllMoves, ltCbs, isHostIn]
  rfl

/-- `Glue.bitAt` is the machine's bit extraction. -/
theorem glue_bitAt_eq {n : Nat} (x : BitVec n) (i : Nat) :
    Metronome.Glue.bitAt x i = Machine.Util.bit x i :=
  (util_bit_eq_bitAt x i).symm

/-- **The per-slot `HOST.IN` read identity on a live slot.** -/
theorem hostInSlot (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (hsrc : Bridge.Glue.SrcTable) (q : Nat) (hq : q < 6)
    {mv : Machine.Move} (hmv : machSlot m pin q = some mv)
    (hen : ((movBundle s pin).get q).enabled = true) :
    isHostIn (Machine.srcOp mv.src) =
      (CoreCtl.bitAt (mvEn s pin) q &&
        (Core.slice (mvSrc s pin) (6 * q) 6 == Moves.srcHostIn)) := by
  have hsrcq : mv.src = (Core.slice (mvSrc s pin) (6 * q) 6).toNat :=
    hbus.src q hq mv hmv
  have hlt : (Core.slice (mvSrc s pin) (6 * q) 6).toNat < 64 := by
    simpa using (Core.slice (mvSrc s pin) (6 * q) 6).isLt
  rw [hsrcq, srcHostIn_iff hsrc hlt, Bridge.Moves.ofNat_toNat_6]
  have hbit : CoreCtl.bitAt (mvEn s pin) q = true := by
    rw [hbus.en q hq, hmv]
    rfl
  rw [hbit]
  rfl

/-- **`CtrlMoveFabric.hostInRead`**: the machine's `HOST.IN` read scan is the
cut's `rd_hin` mask. -/
theorem ctrlMoveFabric_hostInRead (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hJGTab : JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hsrc : Bridge.Glue.SrcTable) :
    (ctrlInTrue m pin).hostInRead = (Bridge.Glue.ctrlInOf (glueIn s pin)).hostInRead := by
  have hbusM := moveBus_of_chipRel s m pin hrel hinv hJGTab hbus hgrp
  have hcore : ∀ c : Fin 2, Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (sIr s m c) (coreIn s pin c.val) :=
    fun c => rel_of_bus s m pin c hrel hinv (hbus c)
  have hfrz : ∀ c : Fin 2, m.dbg.frz = (coreIn s pin c.val).frz := fun c => by
    rw [hrel.dbg.2.1]; simp [coreIn]
  have hlhs := ctrlInTrue_hostInRead m pin
  have hscan : (ltAllMoves m).any (fun mv => isHostIn (Machine.srcOp mv.src)) =
      (List.range 6).any (fun q =>
        (CoreCtl.bitAt (mvEn s pin) q &&
          (Core.slice (mvSrc s pin) (6 * q) 6 == Moves.srcHostIn))) := by
    rw [mAllMoves_ltAllMoves, mAllMoves_enum s m pin hcore hfrz]
    refine any_filterMap_split (List.range 6) (machSlot m pin) _
      (fun q => CoreCtl.bitAt (mvEn s pin) q &&
        (Core.slice (mvSrc s pin) (6 * q) 6 == Moves.srcHostIn)) ?_ ?_
    · intro q hq mv hmv
      rw [List.mem_range] at hq
      have hen : ((movBundle s pin).get q).enabled = true := by
        rw [← machSlot_isSome s m pin hbusM q hq, hmv]
        rfl
      exact hostInSlot s m pin hbusM hsrc q hq hmv hen
    · intro q hq hnone
      rw [List.mem_range] at hq
      have hbit : CoreCtl.bitAt (mvEn s pin) q = false := by
        have hs : (machSlot m pin q).isSome = false := by rw [hnone]; rfl
        rw [← hbusM.en q hq] at hs
        exact hs
      rw [hbit]
      rfl
  have hcut : (Bridge.Glue.ctrlInOf (glueIn s pin)).hostInRead =
      (List.range 6).any (fun q =>
        (CoreCtl.bitAt (mvEn s pin) q &&
          (Core.slice (mvSrc s pin) (6 * q) 6 == Moves.srcHostIn))) := by
    rw [show (Bridge.Glue.ctrlInOf (glueIn s pin)).hostInRead =
      Metronome.Glue.anyRead (Moves.readsOf (mvEn s pin) (mvSrc s pin) Moves.srcHostIn)
      from rfl]
    rw [show Metronome.Glue.anyRead (Moves.readsOf (mvEn s pin) (mvSrc s pin) Moves.srcHostIn) =
      anySix (fun q => Metronome.Glue.bitAt (Moves.readsOf (mvEn s pin) (mvSrc s pin)
        Moves.srcHostIn) q) from rfl]
    rw [← anySix_eq_any]
    apply anySix_congr
    intro q hq
    rw [glue_bitAt_eq, Moves.readsOf, bits6_bit (hq := hq)]
    unfold Moves.readAt
    rfl
  rw [hlhs, hscan, hcut]

/-! ## 13. The per-line `L.SYM` winner mask

The cut's `Wire.symWord l` is `Moves.hitOr` of the per-line `L.SYM` winner mask
`Moves.symMask (mvWin …) (mvGrp …) (mvXl …) l`.  Two facts are needed for the
projected `WireAgree.sym` (`WIRE_MOVEFABRIC_KEYED_NOTES` §10):

* the mask is **at most one-hot**: two set bits are two winners of the key
  `(DG_L_SYM, line)`, which `Moves.winners_unique` forbids (`symMask_atMostOne`);
* `hitOr` of a one-hot mask is that slot's `{1, dst, data}` word
  (`hitOr_onehot`), so the cut's word is the single winner's.
-/

/-- Bit `q` of the cut's winner vector is the bundle's `winAt`. -/
theorem winBits_bit (en : BitVec 6) (grp : BitVec 30) (xl : BitVec 4) (xt : BitVec 6)
    (q : Nat) (hq : q < 6) :
    CoreCtl.bitAt (Moves.winBits en grp xl xt) q =
      Moves.winAt (Moves.arbBundle en grp xl xt) q := by
  rw [show CoreCtl.bitAt (Moves.winBits en grp xl xt) q =
    Machine.Util.bit (Moves.winBits en grp xl xt) q from (util_bit_eq_bitAt _ _).symm]
  rw [show Moves.winBits en grp xl xt =
    Moves.bits6 (fun r => Moves.winAt (Moves.arbBundle en grp xl xt) r) from rfl]
  exact bits6_bit (fun r => Moves.winAt (Moves.arbBundle en grp xl xt) r) q hq

/-- Two `L.SYM` slots of one line contend (same group, same line). -/
theorem sameKey_lsym {a b : Moves.Slot} (hga : (a.group == Moves.dgLSym) = true)
    (hgb : (b.group == Moves.dgLSym) = true) (hl : a.line = b.line) :
    Moves.sameKey a b = true := by
  have hgg : (a.group == b.group) = true := by
    rw [beq_iff_eq] at hga hgb
    rw [hga, hgb]
    decide
  have hne : (a.group == Moves.dgTStop) = false := by
    rw [beq_iff_eq] at hga
    rw [hga]
    decide
  unfold Moves.sameKey
  rw [hgg, hga, hne, hl]
  simp

/-- Two set bits of the per-line mask are two winners with one key. -/
theorem symMask_pair (en : BitVec 6) (grp : BitVec 30) (xl : BitVec 4) (xt : BitVec 6)
    (line : BitVec 2) {i j : Nat} (hi : i < 6) (hj : j < 6) (hij : i ≠ j) :
    (CoreCtl.bitAt (Moves.symMask (Moves.winBits en grp xl xt) grp xl line) i &&
      CoreCtl.bitAt (Moves.symMask (Moves.winBits en grp xl xt) grp xl line) j) = false := by
  rw [Moves.symMask_bit (hq := hi), Moves.symMask_bit (hq := hj)]
  by_cases hwi : CoreCtl.bitAt (Moves.winBits en grp xl xt) i = true
  · by_cases hwj : CoreCtl.bitAt (Moves.winBits en grp xl xt) j = true
    · by_cases hgi : (CoreCtl.slice grp (5 * i) 5 == Moves.dgLSym) = true
      · by_cases hli : (CoreCtl.slice xl (2 * (i / 3)) 2 == line) = true
        · by_cases hgj : (CoreCtl.slice grp (5 * j) 5 == Moves.dgLSym) = true
          · by_cases hlj : (CoreCtl.slice xl (2 * (j / 3)) 2 == line) = true
            · exfalso
              have hsk : Moves.sameKey ((Moves.arbBundle en grp xl xt).get i)
                  ((Moves.arbBundle en grp xl xt).get j) = true := by
                apply sameKey_lsym
                · have h1 : ((Moves.arbBundle en grp xl xt).get i).group =
                      CoreCtl.slice grp (5 * i) 5 := by
                    rw [show (Moves.arbBundle en grp xl xt).get i =
                      ((Moves.bundleOf en grp 0 0 xl xt).get i) from rfl]
                    exact bundle_grp en grp 0 0 xl xt i hi
                  rw [h1]; exact hgi
                · have h1 : ((Moves.arbBundle en grp xl xt).get j).group =
                      CoreCtl.slice grp (5 * j) 5 := by
                    rw [show (Moves.arbBundle en grp xl xt).get j =
                      ((Moves.bundleOf en grp 0 0 xl xt).get j) from rfl]
                    exact bundle_grp en grp 0 0 xl xt j hj
                  rw [h1]; exact hgj
                · have h2 : ((Moves.arbBundle en grp xl xt).get i).line =
                      ((Moves.arbBundle en grp xl xt).get j).line := by
                    rw [show (Moves.arbBundle en grp xl xt).get i =
                        ((Moves.bundleOf en grp 0 0 xl xt).get i) from rfl,
                      show (Moves.arbBundle en grp xl xt).get j =
                        ((Moves.bundleOf en grp 0 0 xl xt).get j) from rfl,
                      bundle_line en grp 0 0 xl xt i hi, bundle_line en grp 0 0 xl xt j hj]
                    rw [beq_iff_eq] at hli hlj
                    rw [hli, hlj]
                  exact h2
              have hwin : Moves.winAt (Moves.arbBundle en grp xl xt) i = true := by
                rw [← winBits_bit en grp xl xt i hi]; exact hwi
              have hwinj : Moves.winAt (Moves.arbBundle en grp xl xt) j = true := by
                rw [← winBits_bit en grp xl xt j hj]; exact hwj
              have hf := Moves.winners_unique (Moves.arbBundle en grp xl xt) hij hwin hwinj
              rw [hf] at hsk
              exact absurd hsk (by decide)
            · have hljf : (CoreCtl.slice xl (2 * (j / 3)) 2 == line) = false := by
                simpa using hlj
              rw [hljf]; simp
          · have hgjf : (CoreCtl.slice grp (5 * j) 5 == Moves.dgLSym) = false := by
              simpa using hgj
            rw [hgjf]; simp
        · have hlif : (CoreCtl.slice xl (2 * (i / 3)) 2 == line) = false := by
            simpa using hli
          rw [hlif]; simp
      · have hgif : (CoreCtl.slice grp (5 * i) 5 == Moves.dgLSym) = false := by
          simpa using hgi
        rw [hgif]; simp
    · have hwjf : CoreCtl.bitAt (Moves.winBits en grp xl xt) j = false := by simpa using hwj
      rw [hwjf]; simp
  · have hwif : CoreCtl.bitAt (Moves.winBits en grp xl xt) i = false := by simpa using hwi
    rw [hwif]; simp

/-- **The per-line `L.SYM` winner mask is at most one-hot.** -/
theorem symMask_atMostOne (en : BitVec 6) (grp : BitVec 30) (xl : BitVec 4) (xt : BitVec 6)
    (line : BitVec 2) :
    Moves.atMostOne (Moves.symMask (Moves.winBits en grp xl xt) grp xl line) = true := by
  have h01 := symMask_pair en grp xl xt line (i := 0) (j := 1) (by omega) (by omega)
    (by decide : (0 : Nat) ≠ 1)
  have h02 := symMask_pair en grp xl xt line (i := 0) (j := 2) (by omega) (by omega)
    (by decide : (0 : Nat) ≠ 2)
  have h03 := symMask_pair en grp xl xt line (i := 0) (j := 3) (by omega) (by omega)
    (by decide : (0 : Nat) ≠ 3)
  have h04 := symMask_pair en grp xl xt line (i := 0) (j := 4) (by omega) (by omega)
    (by decide : (0 : Nat) ≠ 4)
  have h05 := symMask_pair en grp xl xt line (i := 0) (j := 5) (by omega) (by omega)
    (by decide : (0 : Nat) ≠ 5)
  have h12 := symMask_pair en grp xl xt line (i := 1) (j := 2) (by omega) (by omega)
    (by decide : (1 : Nat) ≠ 2)
  have h13 := symMask_pair en grp xl xt line (i := 1) (j := 3) (by omega) (by omega)
    (by decide : (1 : Nat) ≠ 3)
  have h14 := symMask_pair en grp xl xt line (i := 1) (j := 4) (by omega) (by omega)
    (by decide : (1 : Nat) ≠ 4)
  have h15 := symMask_pair en grp xl xt line (i := 1) (j := 5) (by omega) (by omega)
    (by decide : (1 : Nat) ≠ 5)
  have h23 := symMask_pair en grp xl xt line (i := 2) (j := 3) (by omega) (by omega)
    (by decide : (2 : Nat) ≠ 3)
  have h24 := symMask_pair en grp xl xt line (i := 2) (j := 4) (by omega) (by omega)
    (by decide : (2 : Nat) ≠ 4)
  have h25 := symMask_pair en grp xl xt line (i := 2) (j := 5) (by omega) (by omega)
    (by decide : (2 : Nat) ≠ 5)
  have h34 := symMask_pair en grp xl xt line (i := 3) (j := 4) (by omega) (by omega)
    (by decide : (3 : Nat) ≠ 4)
  have h35 := symMask_pair en grp xl xt line (i := 3) (j := 5) (by omega) (by omega)
    (by decide : (3 : Nat) ≠ 5)
  have h45 := symMask_pair en grp xl xt line (i := 4) (j := 5) (by omega) (by omega)
    (by decide : (4 : Nat) ≠ 5)
  simp only [Moves.atMostOne, h01, h02, h03, h04, h05, h12, h13, h14, h15, h23, h24, h25,
    h34, h35, h45, Bool.not_false, Bool.and_true]

/-- **`hitOr` of a one-hot mask is that slot's word.** -/
theorem hitOr_onehot (k : Nat) (hk : k < 6) (dst : BitVec 36) (dat : BitVec 48) :
    Moves.hitOr ((1 : BitVec 6) <<< k) dst dat =
      CoreCtl.makeWord true (CoreCtl.slice dst (6 * k) 6) (CoreCtl.slice dat (8 * k) 8) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    (simp only [Moves.hitOr]
     repeat' first
       | rw [if_pos (by decide)]
       | rw [if_neg (by decide)]
     simp)

/-! ## 14. Data-width witnesses for the exact (`Option`) forms

The cut truncates at the consumption site (`Wire.lineIn.symD = truncate 4`,
`ctlD = ofNat 3`) while the machine carries the picked bus byte; and the cut's
stream `rx` is the low bit of the picked word (`src/project.v:471`).  The exact
`Option`-valued field forms are therefore false; these are the numeric cores (the
`% 16` / `% 8` / `% 2` forms are the provable ones, see the notes §10).
-/

/-- The machine's byte `2` is not the cut's 1-bit stream receive value. -/
theorem stream_rx_data_witness : (2 : Nat) ≠ (if Machine.Util.bit (2 : BitVec 8) 0 then 1 else 0) := by
  decide

/-- No `Sk.CTL` move: the machine has `none`, the cut still reports `some 0`
(`absIn.ctlMove = some (ctlVal i)` folds the host bits in). -/
theorem stream_ctl_absent_witness : (none : Option Nat) ≠ some (0 : Nat) := by
  simp

/-- `% 2` of a byte is its bit 0 (the `rx` projection). -/
theorem byte_mod_two (d : BitVec 8) :
    d.toNat % 2 = (if Machine.Util.bit d 0 then 1 else 0) := by
  have hb : Machine.Util.bit d 0 = ((d.toNat % 2) == 1) := by
    rw [Bridge.Line.bit_eq_nbit]
    simp [Machine.Util.nbit]
  rw [hb]
  have h2 : d.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  rcases (by omega : d.toNat % 2 = 0 ∨ d.toNat % 2 = 1) with h | h <;> simp [h]

/-- The move part of the `Sk.CTL` control bits: `rewind`/`flush` from data bits
0/1 (the cut's `ctlVal` ORs the host `SRT.CTL` bits into the same value). -/
def ctlMoveBits (d : BitVec 8) : Nat :=
  (if Machine.Util.bit d 0 then 1 else 0) + (if Machine.Util.bit d 1 then 2 else 0)

/-- `% 4` of a byte is its two control bits (the `ctlMove` projection). -/
theorem byte_mod_four (d : BitVec 8) : d.toNat % 4 = ctlMoveBits d := by
  have h0 : Machine.Util.bit d 0 = ((d.toNat % 2) == 1) := by
    rw [Bridge.Line.bit_eq_nbit]
    simp [Machine.Util.nbit]
  have h1 : Machine.Util.bit d 1 = ((d.toNat / 2 % 2) == 1) := by
    rw [Bridge.Line.bit_eq_nbit]
    simp [Machine.Util.nbit, Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 1 = 2 from by decide]
  unfold ctlMoveBits
  rw [h0, h1]
  have h2 : d.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  have h4 : d.toNat / 2 % 2 < 2 := Nat.mod_lt _ (by decide)
  rcases (by omega : d.toNat % 2 = 0 ∨ d.toNat % 2 = 1) with a | a <;>
    rcases (by omega : d.toNat / 2 % 2 = 0 ∨ d.toNat / 2 % 2 = 1) with b | b <;>
    simp [a, b] <;> omega

/-- **The stream / line-control destination-code table.**  The rows that
`DstPayloadTable.codeOf` does not cover: each stream and line-control port's
decoder value pins its code, and the three line-symbol codes decode to their own
number.  `Machine.dstOp` is opaque on those parsed names (`String.splitOn` is
irreducible), so this is a global table hypothesis like `DstKindTable` /
`DstPayloadTable`; `decode_check_streamline.lean` in the evidence directory checks
every row for all 64 codes by compiled evaluation. -/
structure DstStreamLineTable : Prop where
  /-- `S*.ADV`: code `47 + n` -/
  sAdv : ∀ d, d < 64 → ∀ n, Machine.dstOp d = .sAdv n → d = 47 + n
  /-- `S*.RX`: code `49 + n` -/
  sRx : ∀ d, d < 64 → ∀ n, Machine.dstOp d = .sRx n → d = 49 + n
  /-- `S*.CTL`: code `51 + n` -/
  sCtl : ∀ d, d < 64 → ∀ n, Machine.dstOp d = .sCtl n → d = 51 + n
  /-- `L*.CTL`: code `53 + n` -/
  lCtl : ∀ d, d < 64 → ∀ n, Machine.dstOp d = .lCtl n → d = 53 + n
  /-- `L.SYM`/`L.DBIT`/`L.XOR` decode to their own code (`1`/`2`/`3`) -/
  lsym : ∀ d, d < 64 → ∀ n, Machine.dstOp d = .lsym n → n = d

/-- A six-bit code `d < 64` equals another one iff their `ofNat` codes are equal. -/
theorem ofNat6_beq_of_ne {a b : Nat} (ha : a < 64) (hb : b < 64) (h : a ≠ b) :
    ((BitVec.ofNat 6 a) == (BitVec.ofNat 6 b)) = false := by
  by_cases hx : ((BitVec.ofNat 6 a) == (BitVec.ofNat 6 b)) = true
  · rw [beq_iff_eq] at hx
    exact absurd (by
      have := congrArg BitVec.toNat hx
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this) h
  · simpa using hx

theorem ofNat6_beq_self (a : Nat) (ha : a < 64) :
    ((BitVec.ofNat 6 a) == (BitVec.ofNat 6 a)) = true := by simp

/-- **Code `47 + n` decodes as `S*.ADV n`** (payload + the stream table). -/
theorem dstOp_sAdv (hT : DstPayloadTable) (hC : DstStreamLineTable) {n : Nat}
    (hd : 47 + n < 64) :
    Machine.dstOp (47 + n) = .sAdv n := by
  have hfam : famIn (.stream n) (Machine.dstOp (47 + n)) = true := by
    rw [← hT.payload (.stream n) (47 + n) hd]
    rw [show Moves.dgTable (BitVec.ofNat 6 (47 + n)) = famG (.stream n) from rfl]
    simp
  cases h : Machine.dstOp (47 + n) with
  | sAdv j =>
    rw [h] at hfam
    have hj : j = n := by simpa [famIn] using hfam
    rw [hj]
  | sRx j =>
    rw [h] at hfam
    have hj : j = n := by simpa [famIn] using hfam
    have hc := hC.sRx (47 + n) hd j h
    rw [hj] at hc
    exact absurd hc (by omega)
  | sCtl j =>
    rw [h] at hfam
    have hj : j = n := by simpa [famIn] using hfam
    have hc := hC.sCtl (47 + n) hd j h
    rw [hj] at hc
    exact absurd hc (by omega)
  | _ => rw [h] at hfam; exact absurd hfam (by simp [famIn])

/-- **Code `49 + n` decodes as `S*.RX n`.** -/
theorem dstOp_sRx (hT : DstPayloadTable) (hC : DstStreamLineTable) {n : Nat}
    (hn : n < 2) (hd : 49 + n < 64) :
    Machine.dstOp (49 + n) = .sRx n := by
  have hfam : famIn (.stream n) (Machine.dstOp (49 + n)) = true := by
    rw [← hT.payload (.stream n) (49 + n) hd]
    rw [show Moves.dgTable (BitVec.ofNat 6 (49 + n)) = famG (.stream n) from by
      rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> decide]
    simp
  cases h : Machine.dstOp (49 + n) with
  | sRx j =>
    rw [h] at hfam
    have hj : j = n := by simpa [famIn] using hfam
    rw [hj]
  | sAdv j =>
    rw [h] at hfam
    have hj : j = n := by simpa [famIn] using hfam
    have hc := hC.sAdv (49 + n) hd j h
    rw [hj] at hc
    exact absurd hc (by omega)
  | sCtl j =>
    rw [h] at hfam
    have hj : j = n := by simpa [famIn] using hfam
    have hc := hC.sCtl (49 + n) hd j h
    rw [hj] at hc
    exact absurd hc (by omega)
  | _ => rw [h] at hfam; exact absurd hfam (by simp [famIn])



/-! ## 16. StreamDbg plumbing for the stream move picks -/

/-- The StreamDbg machine move list is the cut-side `mAllMoves`. -/
theorem machAllMoves_eq (m : Machine.State) (pin : Machine.PinIn) :
    machAllMoves m = mAllMoves m pin := by
  show (machCbs m)[0].moves ++ (machCbs m)[1].moves = _
  have h0 : (machCbs m)[0] = mCoreComb m pin 0 := by simp [machCbs, mCoreComb]
  have h1 : (machCbs m)[1] = mCoreComb m pin 1 := by simp [machCbs, mCoreComb]
  rw [h0, h1]
  rfl

/-- The StreamDbg winner list is `mWs`. -/
theorem machWs_eq_mWs' (m : Machine.State) (pin : Machine.PinIn) :
    machWs m = mWs m pin := by
  show (Machine.resolveMoves (machAllMoves m)).1 =
    (Machine.resolveMoves (mAllMoves m pin)).1
  rw [machAllMoves_eq]

/-- The machine's stream `adv` field in `sel`-form. -/
theorem machStreamIn_adv (m : Machine.State) (k : Fin 2) :
    (machStreamIn m k).adv =
      ((machWs m).findSome? (fun mm => (match Machine.dstOp mm.dst with
        | .sAdv j => if j == k.val then some 0 else none
        | _ => none).map (fun _ => mm.v))).isSome := rfl

/-- `findSome?` preserves `isSome` under a pointwise-`isSome`-equal family. -/
theorem findSome?_isSome_congr {α : Type} {β : Type} (l : List α) (f g : α → Option β)
    (h : ∀ x, (f x).isSome = (g x).isSome) :
    (l.findSome? f).isSome = (l.findSome? g).isSome := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.findSome?_cons, List.findSome?_cons]
    cases hfa : f a with
    | none =>
      cases hga : g a with
      | none => simpa only [hfa, hga, Option.none_or, Option.isSome_none] using ih
      | some b =>
        have h1 := h a
        rw [hfa, hga] at h1
        exact absurd h1 (by simp)
    | some b =>
      cases hga : g a with
      | none =>
        have h1 := h a
        rw [hfa, hga] at h1
        exact absurd h1 (by simp)
      | some c => rfl

def sAdvNat (k : Fin 2) : Machine.DstOp -> Option Nat
  | .sAdv j => if j == k.val then some 0 else none
  | _ => none

def sAdvUnit (k : Fin 2) : Machine.DstOp -> Option Unit
  | .sAdv j => if j == k.val then some () else none
  | _ => none

theorem sAdv_isSome_eq (k : Fin 2) (o : Machine.DstOp) :
    (sAdvNat k o).isSome = (sAdvUnit k o).isSome := by
  cases o with
  | sAdv j => by_cases hj : j = k.val <;> simp [sAdvNat, sAdvUnit, hj]
  | _ => rfl


/-! ## S*.ADV (spliced by the orchestrator from W1b round-5 draft; fixes: explicit `pin`
in machWs_eq_mWs', type-general findSome?_isSome_congr', final case split on the generalized
pick word). -/

/-- **The `Fam.stream k` payload instance for `S*.ADV`**: the machine's
`.sAdv k` test is the cut's group test conjoined with the code test
`dst == 47 + k`.  This is the `hPQ` that `pickScan_mWs` needs. -/
theorem hPQ_stream_adv (hT : DstPayloadTable) (hC : DstStreamLineTable) (k : Fin 2) :
    ∀ d, d < 64 → sAdvUnit k (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == famG (.stream k.val)) then
        (if (BitVec.ofNat 6 d) == BitVec.ofNat 6 (47 + k.val) then some () else none)
       else none) := by
  intro d hd
  have hpay := hT.payload (.stream k.val) d hd
  by_cases hg : (Moves.dgTable (BitVec.ofNat 6 d) == famG (.stream k.val)) = true
  · have hfam : famIn (.stream k.val) (Machine.dstOp d) = true := by rw [← hpay, hg]
    rw [if_pos hg]
    cases h : Machine.dstOp d with
    | sAdv j =>
      rw [h] at hfam
      have hj : j = k.val := by simpa [famIn] using hfam
      have hd47 : d = 47 + k.val := by simpa [hj] using hC.sAdv d hd j h
      rw [hd47]
      simp [sAdvUnit, hj]
    | sRx j =>
      rw [h] at hfam
      have hj : j = k.val := by simpa [famIn] using hfam
      have hd49 : d = 49 + k.val := by simpa [hj] using hC.sRx d hd j h
      rw [hd49, ofNat6_beq_of_ne (by omega) (by omega) (by omega)]
      simp [sAdvUnit]
    | sCtl j =>
      rw [h] at hfam
      have hj : j = k.val := by simpa [famIn] using hfam
      have hd51 : d = 51 + k.val := by simpa [hj] using hC.sCtl d hd j h
      rw [hd51, ofNat6_beq_of_ne (by omega) (by omega) (by omega)]
      simp [sAdvUnit]
    | _ => rw [h] at hfam; exact absurd hfam (by simp [famIn])
  · rw [if_neg (by simpa using hg)]
    by_cases hP : sAdvUnit k (Machine.dstOp d) = some ()
    · exfalso
      cases h : Machine.dstOp d with
      | sAdv j =>
        rw [h] at hP
        have hj : j = k.val := by
          by_cases hjk : j = k.val
          · exact hjk
          · simp [sAdvUnit, hjk] at hP
        have hd47 : d = 47 + k.val := by simpa [hj] using hC.sAdv d hd j h
        rw [hd47] at hg
        rw [show Moves.dgTable (BitVec.ofNat 6 (47 + k.val)) = famG (.stream k.val) from rfl] at hg
        exact absurd hg (by simp)
      | _ => rw [h] at hP; exact absurd hP (by simp [sAdvUnit])
    · cases h : sAdvUnit k (Machine.dstOp d) with
      | none => rfl
      | some u => cases u; exact absurd h hP

/-- `findSome?_isSome_congr` across different value types. -/
theorem findSome?_isSome_congr' {α β γ : Type} (l : List α) (f : α → Option β)
    (g : α → Option γ) (h : ∀ x, (f x).isSome = (g x).isSome) :
    (l.findSome? f).isSome = (l.findSome? g).isSome := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha := h a
    simp only [List.findSome?_cons]
    cases hf : f a <;> cases hg : g a <;> simp_all

/-- **`StreamWire.input`'s `adv` component is exact**: the machine's
`(machStreamIn m k).adv` is the cut's `Sk.ADV` strobe `opg(DG_SK, 47+k)`. -/
theorem streams_adv (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hJGTab : JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hT : DstPayloadTable) (hC : DstStreamLineTable) (k : Fin 2) :
    (machStreamIn m k).adv = (absInOf k (streamAt s k.val) (streamIn s pin k.val)).adv := by
  have hpq := hPQ_stream_adv hT hC k
  have hscan := pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
    (sAdvUnit k) (fun dst => if dst == BitVec.ofNat 6 (47 + k.val) then some () else none)
    (fun v => v) (famG (.stream k.val))
    (famG_nonkeyed hT).1 (famG_nonkeyed hT).2.1 (famG_nonkeyed hT).2.2 hpq
  have hmach : (machStreamIn m k).adv =
      ((mWs m pin).findSome? (fun mv => (sAdvUnit k (Machine.dstOp mv.dst)).map
        (fun a => (a, mv.v)))).isSome := by
    rw [machStreamIn_adv, machWs_eq_mWs' m pin]
    exact findSome?_isSome_congr' _ _ _ (fun mv => by
      rw [Option.isSome_map, Option.isSome_map]
      exact sAdv_isSome_eq k (Machine.dstOp mv.dst))
  rw [hmach, hscan]
  show _ = strobe s pin (BitVec.ofNat 6 (47 + k.val))
  rw [show strobe s pin (BitVec.ofNat 6 (47 + k.val)) = Strobes.opg (mvEn s pin)
      (mvGrp s pin) (mvDst s pin) (Moves.dgTable (BitVec.ofNat 6 (47 + k.val)))
      (BitVec.ofNat 6 (47 + k.val)) from rfl,
    Strobes.opg_eq_pick (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
      (Moves.dgTable (BitVec.ofNat 6 (47 + k.val))) (BitVec.ofNat 6 (47 + k.val))]
  rw [show Moves.dgTable (BitVec.ofNat 6 (47 + k.val)) = famG (.stream k.val) from rfl]
  generalize Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.stream k.val)))
    (mvDst s pin) (mvDat s pin) = w
  cases w.we <;> cases (w.dst == BitVec.ofNat 6 (47 + k.val)) <;> rfl


end Metronome.ChipCut.Discharge.MoveFabricKeyed

