/-
# ChipCut discharge: the line move-fabric wiring fields, in projected form

`LineThread.lean` states `WireAgree.sym`/`WireAgree.ctl` as *exact* equalities of the
machine's `LineIn` fields with the cut's `Bridge.Line.absIn`:

```
(ltLineIn m l).sym = (Bridge.Line.absIn (lineIn s pin l.val)).sym
(ltLineIn m l).ctlMove = (Bridge.Line.absIn (lineIn s pin l.val)).ctlMove
```

Both exact forms are **false**: the machine keeps the winning move's whole 8-bit data
byte (`Machine.Move.v`), while the cut truncates at the consumption site
(`Wire.lineIn.symD = BitVec.truncate 4`, `ctlD = BitVec.ofNat 3`).  The witnesses are
`MoveFabric.sym_data_witness`/`ctl_data_witness`.

This file proves the **projected** forms

```lean
(ltLineIn m l).sym.map (fun w => (w.op, w.v % 16)) =
  (Bridge.Line.absIn (lineIn s pin l.val)).sym.map (fun w => (w.op, w.v))

(ltLineIn m l).ctlMove.map (fun v => v % 8) =
  (Bridge.Line.absIn (lineIn s pin l.val)).ctlMove
```

* `ctl` (`Lk.CTL`, group `20+k`, code `53+k`) is a non-keyed group pick: one
  `MoveFabric.pickScan_mWs` instance for `Fam.lCtl l`, with the payload table giving
  the machine's `.lCtl` decode and a 64-code `dgTable` check giving the cut's
  single-code group (`we → dst == 53+l`), then `% 8` on the data byte.
* `sym` (`L.SYM`, group `0`, keyed by line) is the keyed `hitOr`-of-`symMask` word of
  `Wire.symWord`: `MoveFabricKeyed.symMask_atMostOne` makes the per-line winner mask
  one-hot, `MoveFabricKeyed.hitOr_onehot` extracts that slot's word, and the machine's
  winner scan over `.lsym` with `mv.line == l` picks the same slot (the
  `DstStreamLineTable.lsym` row `dstOp d = .lsym n → n = d` identifies the op code
  with the destination code).
-/
import Metronome.ChipCut.Discharge.MoveFabricKeyed

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 4096

namespace Metronome.ChipCut.Discharge.LineMoveWire

open Metronome
open Metronome.ChipCut.Discharge
open Metronome.ChipCut.Discharge.MoveFabric
open Metronome.ChipCut.Discharge.MoveFabricKeyed

/-! ## 1. Small arithmetic and bit plumbing -/

/-- `BitVec.ofNat 3` of a natural number truncates modulo 8. -/
theorem ofNat3_toNat (x : Nat) : (BitVec.ofNat 3 x).toNat = x % 8 := by
  rw [BitVec.toNat_ofNat, show (2 : Nat) ^ 3 = 8 from by decide]

/-- The `BitVec` test `x == ofNat 2 l` is the `Nat` test `x.toNat == l`. -/
theorem beq_ofNat2_toNat (x : BitVec 2) (l : Nat) (hl : l < 4) :
    (x == BitVec.ofNat 2 l) = (x.toNat == l) := by
  have h2 : (BitVec.ofNat 2 l).toNat = l := by
    rw [BitVec.toNat_ofNat, show (2 : Nat) ^ 2 = 4 from by decide, Nat.mod_eq_of_lt hl]
  by_cases h : x = BitVec.ofNat 2 l
  · subst h
    rw [beq_self_eq_true, h2, beq_self_eq_true]
  · have hf : (x == BitVec.ofNat 2 l) = false := by simpa using h
    have hx : (x.toNat == l) = false := by
      by_cases hx' : x.toNat = l
      · have hxe : x = BitVec.ofNat 2 l := by
          apply BitVec.eq_of_toNat_eq
          rw [h2]
          exact hx'
        exact absurd hxe h
      · simpa using hx'
    rw [hf, hx]

/-- A concrete bit of the zero mask. -/
theorem bitAt_zero6 (i : Nat) (hi : i < 6) : CoreCtl.bitAt (0 : BitVec 6) i = false := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `Moves.bits6` is zero when all six bits are false. -/
theorem bits6_eq_zero (f : Nat → Bool) (h : ∀ q, q < 6 → f q = false) :
    Moves.bits6 f = 0 := by
  simp only [Moves.bits6, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
    h 4 (by omega), h 5 (by omega), if_false]
  decide

/-- `Moves.hitOr` of the zero mask is the zero word. -/
theorem hitOr_zero (dst : BitVec 36) (dat : BitVec 48) : Moves.hitOr 0 dst dat = 0 := by
  simp only [Moves.hitOr, bitAt_zero6 0 (by omega), bitAt_zero6 1 (by omega),
    bitAt_zero6 2 (by omega), bitAt_zero6 3 (by omega), bitAt_zero6 4 (by omega),
    bitAt_zero6 5 (by omega), Bool.false_eq_true, if_false]
  decide

/-- The low nibble of a packed group word is the low nibble of its data byte. -/
theorem truncate_four_makeWord (we : Bool) (d : BitVec 6) (da : BitVec 8) :
    BitVec.truncate 4 (CoreCtl.makeWord we d da) = BitVec.truncate 4 da := by
  cases we <;>
    (unfold CoreCtl.makeWord
     bv_decide)

/-- A concrete bit of the zero 15-bit word. -/
theorem util_bit_zero (i : Nat) : Machine.Util.bit (0 : BitVec 15) i = false := by
  simp [Machine.Util.bit]

/-! ## 2. `Lk.CTL`: the single-code group `20+l` -/

/-- Every code whose `dgTable` is group `20+l`'s group is `53+l`: the `Lk.CTL` groups
each hold exactly one code (a 4 x 64-code kernel check of the literal table). -/
theorem dgTable_lctl_code (l : Fin 4) {d : Nat} (hd : d < 64)
    (h : (Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgTable (BitVec.ofNat 6 (53 + l.val))) = true) :
    d = 53 + l.val := by
  have hall : (List.range 4).all (fun t =>
      (List.range 64).all (fun d =>
        ((Moves.dgTable (BitVec.ofNat 6 d) ==
            Moves.dgTable (BitVec.ofNat 6 (53 + t))) == (d == 53 + t)))) = true := by
    decide
  have h1 := List.all_eq_true.1 hall l.val (by simp [List.mem_range])
  have h' := List.all_eq_true.1 h1 d (by simpa [List.mem_range] using hd)
  rw [beq_iff_eq] at h'
  have h2 : (d == 53 + l.val) = true := by rw [← h']; exact h
  simpa using h2

/-- **`WireAgree.ctl` in the projected (`% 8`) form**: the machine's `Lk.CTL` winner
is the cut's control-move word of group `20+l`, code `53+l`, with the cut's
`BitVec.ofNat 3` truncation of the data byte. -/
theorem wireAgree_ctl_low3 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hJGTab : JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hT : DstPayloadTable) (l : Fin 4) :
    (ltLineIn m l).ctlMove.map (fun v => v % 8) =
      (Bridge.Line.absIn (lineIn s pin l.val)).ctlMove := by
  have hgn : (Moves.dgTable (BitVec.ofNat 6 (53 + l.val)) == Moves.dgNone) = false :=
    (famG_nonkeyed (f := .lCtl l.val) hT).1
  -- the winner's code is `53+l`, hence the cut's strobe is the pick's `we`
  have huniq : (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin)
        (Moves.dgTable (BitVec.ofNat 6 (53 + l.val)))) (mvDst s pin) (mvDat s pin)).we = true →
      ((Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin)
        (Moves.dgTable (BitVec.ofNat 6 (53 + l.val)))) (mvDst s pin) (mvDat s pin)).dst ==
        BitVec.ofNat 6 (53 + l.val)) = true := by
    intro hw
    obtain ⟨j, hj, hhit, hfirst⟩ := pickWord_we_exists (mvEn s pin) (mvGrp s pin)
      (Moves.dgTable (BitVec.ofNat 6 (53 + l.val))) (mvDst s pin) (mvDat s pin) hw
    have hpw := Bridge.Moves.pickWord_eq_word (mvEn s pin) (mvGrp s pin) (mvDst s pin)
      (mvDat s pin) (mvXl s) (mvXt s) (Moves.dgTable (BitVec.ofNat 6 (53 + l.val))) j hj hhit hfirst
    rw [show (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin)
        (Moves.dgTable (BitVec.ofNat 6 (53 + l.val)))) (mvDst s pin) (mvDat s pin)).dst =
        ((movBundle s pin).get j).dst from
      congrArg CoreCtl.GroupWord.dst hpw]
    have hgrpJ : (Moves.dgTable ((movBundle s pin).get j).dst ==
        Moves.dgTable (BitVec.ofNat 6 (53 + l.val))) = true := by
      have h2 := hhit
      rw [hitAt_bundle s pin (Moves.dgTable (BitVec.ofNat 6 (53 + l.val))) hgn j hj,
        Bool.and_eq_true] at h2
      have h3 : ((movBundle s pin).get j).group = Moves.dgTable ((movBundle s pin).get j).dst :=
        hgrp j hj
      rw [h3] at h2
      exact h2.2
    have hgrpJ' : (Moves.dgTable (BitVec.ofNat 6 ((movBundle s pin).get j).dst.toNat) ==
        Moves.dgTable (BitVec.ofNat 6 (53 + l.val))) = true := by
      rw [Bridge.Moves.ofNat_toNat_6]
      exact hgrpJ
    have hcode := dgTable_lctl_code l (d := ((movBundle s pin).get j).dst.toNat)
      (by simpa using ((movBundle s pin).get j).dst.isLt) hgrpJ'
    rw [← Bridge.Moves.ofNat_toNat_6 ((movBundle s pin).get j).dst, hcode]
    exact beq_self_eq_true _
  -- the payload table gives the `pickScan` side condition for `Fam.lCtl l`
  have hpq := hPQ_of_payload (famIn (.lCtl l.val))
    (fun o => match o with | .lCtl j => if j == l.val then some () else none | _ => none)
    (fun _ => some ()) (famG (.lCtl l.val)) (hT.payload (.lCtl l.val))
    (by intro d _ hp; cases h : Machine.dstOp d <;> simp_all [famIn])
    (by intro d _ hp; cases h : Machine.dstOp d <;> simp_all [famIn])
  -- the machine's scan, in the `T = · % 8` form
  have hpack : (mWs m pin).findSome? (fun mv =>
        ((match Machine.dstOp mv.dst with
          | .lCtl j => if j == l.val then some () else none
          | _ => none).map (fun a => (a, mv.v % 8))).map (fun p : Unit × Nat => p.2))
      = (if (gw s pin (BitVec.ofNat 6 (53 + l.val))).we then
          some ((gw s pin (BitVec.ofNat 6 (53 + l.val))).data.toNat % 8) else none) := by
    rw [findSome?_snd_map,
      pickScan_mWs s m pin hrel hinv hJGTab hbus hgrp hkind
        (fun o => match o with | .lCtl j => if j == l.val then some () else none | _ => none)
        (fun _ => some ()) (fun v => v % 8) (famG (.lCtl l.val))
        (famG_nonkeyed hT).1 (famG_nonkeyed hT).2.1 (famG_nonkeyed hT).2.2 hpq]
    rw [show gw s pin (BitVec.ofNat 6 (53 + l.val)) = Moves.pickWord
        (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.lCtl l.val)))
        (mvDst s pin) (mvDat s pin) from rfl]
    cases (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) (famG (.lCtl l.val)))
      (mvDst s pin) (mvDat s pin)).we <;> rfl
  -- the machine side, projected
  have hltWs : ltWs m = mWs m pin := by
    show (Machine.resolveMoves (ltAllMoves m)).1 = (Machine.resolveMoves (mAllMoves m pin)).1
    rw [mAllMoves_ltAllMoves]
  have hlhs : (ltLineIn m l).ctlMove.map (fun v => v % 8) =
      (mWs m pin).findSome? (fun mv =>
        ((match Machine.dstOp mv.dst with
          | .lCtl j => if j == l.val then some mv.v else none
          | _ => none).map (fun v => v % 8))) := by
    rw [show (ltLineIn m l).ctlMove = (ltWs m).findSome? (fun mv =>
        match Machine.dstOp mv.dst with
        | .lCtl j => if j == l.val then some mv.v else none
        | _ => none) from rfl, hltWs]
    exact findSome?_map_value (mWs m pin) _ _
  have hstep : ∀ mv : Machine.Move,
      ((match Machine.dstOp mv.dst with
          | .lCtl j => if j == l.val then some mv.v else none
          | _ => none).map (fun v => v % 8)) =
        ((match Machine.dstOp mv.dst with
          | .lCtl j => if j == l.val then some () else none
          | _ => none).map (fun a => (a, mv.v % 8))).map (fun p : Unit × Nat => p.2) := by
    intro mv
    cases Machine.dstOp mv.dst <;> simp
  -- the cut side: the strobe is the pick's `we`, the data byte is `% 8`
  have hstr : strobe s pin (BitVec.ofNat 6 (53 + l.val)) =
      (gw s pin (BitVec.ofNat 6 (53 + l.val))).we := by
    rw [show strobe s pin (BitVec.ofNat 6 (53 + l.val)) = Strobes.opg (mvEn s pin)
        (mvGrp s pin) (mvDst s pin) (Moves.dgTable (BitVec.ofNat 6 (53 + l.val)))
        (BitVec.ofNat 6 (53 + l.val)) from rfl,
      Strobes.opg_eq_pick (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)]
    by_cases hw : (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin)
        (Moves.dgTable (BitVec.ofNat 6 (53 + l.val)))) (mvDst s pin) (mvDat s pin)).we = true
    · rw [show gw s pin (BitVec.ofNat 6 (53 + l.val)) = Moves.pickWord
          (Moves.hitsMask (mvEn s pin) (mvGrp s pin)
            (Moves.dgTable (BitVec.ofNat 6 (53 + l.val)))) (mvDst s pin) (mvDat s pin) from rfl]
      simp [hw, huniq hw]
    · have hf : (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin)
          (Moves.dgTable (BitVec.ofNat 6 (53 + l.val)))) (mvDst s pin) (mvDat s pin)).we
          = false := by simpa using hw
      rw [show gw s pin (BitVec.ofNat 6 (53 + l.val)) = Moves.pickWord
          (Moves.hitsMask (mvEn s pin) (mvGrp s pin)
            (Moves.dgTable (BitVec.ofNat 6 (53 + l.val)))) (mvDst s pin) (mvDat s pin) from rfl, hf]
      simp
  have hcut : (Bridge.Line.absIn (lineIn s pin l.val)).ctlMove =
      (if (gw s pin (BitVec.ofNat 6 (53 + l.val))).we then
        some ((gw s pin (BitVec.ofNat 6 (53 + l.val))).data.toNat % 8) else none) := by
    show (if (lineIn s pin l.val).ctlWe then some (lineIn s pin l.val).ctlD.toNat else none) = _
    rw [show (lineIn s pin l.val).ctlWe = strobe s pin (BitVec.ofNat 6 (53 + l.val)) from rfl,
      hstr,
      show (lineIn s pin l.val).ctlD =
        BitVec.ofNat 3 (gw s pin (BitVec.ofNat 6 (53 + l.val))).data.toNat from rfl,
      ofNat3_toNat]
  rw [hlhs, findSome?_congr (fun mv => hstep mv), hpack, hcut]

/-! ## 3. `L.SYM`: the line-keyed group

The cut's `Wire.symWord l` is `Moves.hitOr` of the per-line winner mask
`Moves.symMask (mvWin …) (mvGrp …) (mvXl …) l`.  The mask is at most one-hot
(`MoveFabricKeyed.symMask_atMostOne`), so either it is zero (the cut sees no symbol
write) or it is `1 <<< q` for a unique winner `q`, and `hitOr_onehot` makes the cut's
word that winner's `{we, dst, data}`.

The machine scans its winners for `.lsym op` with `mv.line == l`.  Both sides select
the same slot: at a winner, the mask bit is exactly the machine's scan test
(`symSlot`), and the slot's destination code is its op code
(`DstStreamLineTable.lsym`).
-/

/-- The machine's `L.SYM` scan of the winners, as `ltLineIn` performs it. -/
def symVal (l : Fin 4) (mv : Machine.Move) : Option Machine.SymWrite :=
  match Machine.dstOp mv.dst with
  | .lsym op => if mv.line == l.val then some { op := op, v := mv.v } else none
  | _ => none

/-- The same scan over the six slots, with the data byte projected (`% 16`). -/
def symScan (s : State) (m : Machine.State) (pin : Machine.PinIn) (l : Fin 4)
    (q : Nat) : Option (Nat × Nat) :=
  if Moves.winAt (movBundle s pin) q then
    (match Machine.dstOp (machMove s m pin q).dst with
      | .lsym op => if (machMove s m pin q).line == l.val then
          some (op, (machMove s m pin q).v % 16) else none
      | _ => none)
  else none

/-- The winner scan's per-slot form. -/
theorem symScan_of_win (s : State) (m : Machine.State) (pin : Machine.PinIn) (l : Fin 4)
    (q : Nat) (h : Moves.winAt (movBundle s pin) q = true) :
    symScan s m pin l q =
      (match Machine.dstOp (machMove s m pin q).dst with
        | .lsym op => if (machMove s m pin q).line == l.val then
            some (op, (machMove s m pin q).v % 16) else none
        | _ => none) := by
  rw [symScan, if_pos h]

/-- `winAt` does not read a slot's destination or data word. -/
theorem winAt_bundleOf (en : BitVec 6) (grp : BitVec 30) (xl : BitVec 4) (xt : BitVec 6)
    (d d' : BitVec 36) (a a' : BitVec 48) (q : Nat) (hq : q < 6) :
    Moves.winAt (Moves.bundleOf en grp d a xl xt) q =
      Moves.winAt (Moves.bundleOf en grp d' a' xl xt) q := by
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Moves.winAt, Moves.validAt, Moves.blocked, Moves.sameKey,
      show List.range 5 = [0, 1, 2, 3, 4] from by decide,
      show List.range 4 = [0, 1, 2, 3] from by decide,
      show List.range 3 = [0, 1, 2] from by decide,
      show List.range 2 = [0, 1] from by decide,
      show List.range 1 = [0] from by decide,
      List.range_zero, List.any_cons, List.any_nil, Moves.bundleOf, Moves.Bundle.get]

/-- The cut's winner vector is `winAt` on the real move bundle. -/
theorem winAt_arbBundle (s : State) (pin : Machine.PinIn) (q : Nat) (hq : q < 6) :
    Moves.winAt (Moves.arbBundle (mvEn s pin) (mvGrp s pin) (mvXl s) (mvXt s)) q =
      Moves.winAt (movBundle s pin) q :=
  winAt_bundleOf (mvEn s pin) (mvGrp s pin) (mvXl s) (mvXt s) (d := 0) (d' := mvDst s pin)
    (a := 0) (a' := mvDat s pin) q hq

/-- Bit `k` of a one-hot mask at `j` is `k == j`. -/
theorem bitAt_one_shift {j k : Nat} (hj : j < 6) (hk : k < 6) :
    CoreCtl.bitAt ((1 : BitVec 6) <<< j) k = (k == j) := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A mask that is at most one-hot and has a set bit is that bit's one-hot mask. -/
theorem eq_shift_of_atMostOne {hit : BitVec 6} (h : Moves.atMostOne hit = true)
    {k : Nat} (hk : k < 6) (hbit : CoreCtl.bitAt hit k = true) :
    hit = (1 : BitVec 6) <<< k := by
  rcases Strobes.atMostOne_cases h with h0 | h0 | h0 | h0 | h0 | h0 | h0 <;>
    (rw [h0] at hbit ⊢) <;>
    (rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl) <;>
    first
      | decide
      | exact absurd hbit (by decide)

/-- The cut's symbol op of an `L.SYM`-group code is its code (`L.SYM`/`L.DBIT`/`L.XOR`
= 1/2/3, `Strobes.lineSop` = 0/1/2, `Bridge.Line.absSymOp` recovers the code). -/
theorem absSymOp_lineSop (v : BitVec 6) (h : (Moves.dgTable v == Moves.dgLSym) = true) :
    Bridge.Line.absSymOp (Strobes.lineSop v) = v.toNat := by
  have hall : (List.range 64).all (fun d =>
      (!(Moves.dgTable (BitVec.ofNat 6 d) == Moves.dgLSym) ||
        (Bridge.Line.absSymOp (Strobes.lineSop (BitVec.ofNat 6 d)) == d))) = true := by
    decide
  have h' := List.all_eq_true.1 hall v.toNat (by simpa [List.mem_range] using v.isLt)
  rw [← Bridge.Moves.ofNat_toNat_6 v] at h
  rw [h] at h'
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at h'
  simpa [Bridge.Moves.ofNat_toNat_6] using h'

/-- At a winner, the cut's per-line `L.SYM` mask bit is the machine's scan test
(`.lsym` and the slot's line is `l`). -/
theorem symSlot (s : State) (m : Machine.State) (pin : Machine.PinIn) (hbus : MoveBus s m pin)
    (hgrp : GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable) (l : Fin 4) (q : Nat)
    (hq : q < 6) (hwin : Moves.winAt (movBundle s pin) q = true) :
    CoreCtl.bitAt (Moves.symMask (mvWin s pin) (mvGrp s pin) (mvXl s) (BitVec.ofNat 2 l.val)) q =
      (match Machine.dstOp (machMove s m pin q).dst with
        | .lsym _ => ((machMove s m pin q).line == l.val)
        | _ => false) := by
  have hwb : CoreCtl.bitAt (mvWin s pin) q = true := by
    rw [mvWin, winBits_bit (hq := hq), winAt_arbBundle s pin q hq]
    exact hwin
  have hen : ((movBundle s pin).get q).enabled = true := by
    have hv := Moves.winAt_valid hwin
    rw [show Moves.validAt ((movBundle s pin).get q) =
      (((movBundle s pin).get q).enabled &&
        !(((movBundle s pin).get q).group == Moves.dgNone)) from rfl, Bool.and_eq_true] at hv
    exact hv.1
  rw [Moves.symMask_bit (hq := hq), hwb, Bool.true_and]
  -- the group conjunct is the machine's `.lsym` test
  have hg : (CoreCtl.slice (mvGrp s pin) (5 * q) 5 == Moves.dgLSym) =
      isLsym (Machine.dstOp (machMove s m pin q).dst) := by
    have h1 : CoreCtl.slice (mvGrp s pin) (5 * q) 5 = ((movBundle s pin).get q).group :=
      (bundle_grp (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin) (mvXl s) (mvXt s)
        q hq).symm
    rw [h1, hgrp q hq]
    have h2 := isLsym_eq_group hkind (d := ((movBundle s pin).get q).dst.toNat)
      (by simpa using ((movBundle s pin).get q).dst.isLt)
    rw [Bridge.Moves.ofNat_toNat_6] at h2
    rw [← h2, machMove_dst s m pin hbus q hq hen]
  -- the line conjunct is the machine's `mv.line == l` test
  have hl : (CoreCtl.slice (mvXl s) (2 * (q / 3)) 2 == BitVec.ofNat 2 l.val) =
      ((machMove s m pin q).line == l.val) := by
    rw [hbus.line q hq]
    exact beq_ofNat2_toNat _ l.val l.isLt
  rw [hg, hl]
  cases Machine.dstOp (machMove s m pin q).dst <;> rfl

/-- The scan finds nothing exactly when the line's mask bit is clear. -/
theorem symScan_eq_none_iff (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) (hgrp : GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (l : Fin 4) (q : Nat) (hq : q < 6) :
    (symScan s m pin l q = none) ↔
      (CoreCtl.bitAt (Moves.symMask (mvWin s pin) (mvGrp s pin) (mvXl s)
        (BitVec.ofNat 2 l.val)) q = false) := by
  by_cases hwin : Moves.winAt (movBundle s pin) q = true
  · rw [symScan_of_win s m pin l q hwin,
      symSlot s m pin hbus hgrp hkind l q hq hwin]
    cases hd : Machine.dstOp (machMove s m pin q).dst with
    | lsym op =>
      by_cases hl : ((machMove s m pin q).line == l.val) = true
      · simp [hd, hl]
      · simp [hd, hl]
    | _ => simp [hd]
  · have hwf : Moves.winAt (movBundle s pin) q = false := by simpa using hwin
    have hwb : CoreCtl.bitAt (mvWin s pin) q = false := by
      rw [mvWin, winBits_bit (hq := hq), winAt_arbBundle s pin q hq]
      exact hwf
    rw [symScan, if_neg (by simpa using hwin), Moves.symMask_bit (hq := hq), hwb]
    simp

/-- **`WireAgree.sym` in the projected (`% 16`) form**: the machine's `L.SYM` winner
of line `l` is the cut's per-line symbol word, with the cut's `truncate 4` of the
data byte and the `absSymOp ∘ lineSop` recoding of the op. -/
theorem wireAgree_sym_low4 (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hJGTab : JGTable)
    (hbus : ∀ c : Fin 2, CoreInputBus s m pin c (sIr s m c))
    (hgrp : GrpPacked s pin) (hkind : Bridge.Moves.DstKindTable)
    (hC : DstStreamLineTable) (l : Fin 4) :
    (ltLineIn m l).sym.map (fun w => (w.op, w.v % 16)) =
      (Bridge.Line.absIn (lineIn s pin l.val)).sym.map (fun w => (w.op, w.v)) := by
  have hbusM := moveBus_of_chipRel s m pin hrel hinv hJGTab hbus hgrp
  have hcore : ∀ c : Fin 2, Bridge.Core.Rel (c.val == 1) m (Machine.cfgView m.cfg)
      (Machine.pinView m.sync m.dbg) (sIr s m c) (coreIn s pin c.val) :=
    fun c => rel_of_bus s m pin c hrel hinv (hbus c)
  have hfrz : ∀ c : Fin 2, m.dbg.frz = (coreIn s pin c.val).frz := fun c => by
    rw [hrel.dbg.2.1]; simp [coreIn]
  have hws : ltWs m = (List.range 6).filterMap (fun k =>
      if Moves.winAt (movBundle s pin) k then some (machMove s m pin k) else none) := by
    have h1 : ltWs m = mWs m pin := by
      show (Machine.resolveMoves (ltAllMoves m)).1 = (Machine.resolveMoves (mAllMoves m pin)).1
      rw [mAllMoves_ltAllMoves]
    rw [h1, mWs_eq_six s m pin hkind hcore hfrz, (winners_machMove s m pin hkind hbusM).1]
  have hstep : ∀ mv : Machine.Move,
      (symVal l mv).map (fun w => (w.op, w.v % 16)) =
      (match Machine.dstOp mv.dst with
        | .lsym op => if mv.line == l.val then some (op, mv.v % 16) else none
        | _ => none) := by
    intro mv
    unfold symVal
    cases Machine.dstOp mv.dst <;> simp
  have hLHS : (ltLineIn m l).sym.map (fun w => (w.op, w.v % 16)) =
      (List.range 6).findSome? (symScan s m pin l) := by
    rw [show (ltLineIn m l).sym = (ltWs m).findSome? (symVal l) from rfl,
      findSome?_map_value, hws,
      scan_rewrite (List.range 6) (fun k => Moves.winAt (movBundle s pin) k)
        (machMove s m pin) (fun mv => (symVal l mv).map (fun w => (w.op, w.v % 16)))]
    refine findSome?_congr (fun q => ?_)
    by_cases hw : Moves.winAt (movBundle s pin) q = true
    · rw [if_pos hw, symScan_of_win s m pin l q hw]
      exact hstep (machMove s m pin q)
    · rw [if_neg (by simpa using hw), symScan, if_neg (by simpa using hw)]
  let M := Moves.symMask (mvWin s pin) (mvGrp s pin) (mvXl s) (BitVec.ofNat 2 l.val)
  have hM : Moves.atMostOne M = true :=
    symMask_atMostOne (mvEn s pin) (mvGrp s pin) (mvXl s) (mvXt s) (BitVec.ofNat 2 l.val)
  have hswOf : symWord s pin l.val = Moves.hitOr M (mvDst s pin) (mvDat s pin) := rfl
  by_cases hsome : (List.range 6).findSome? (symScan s m pin l) = none
  · -- no slot: the mask is zero and the cut sees no symbol write
    have hbits : ∀ q, q < 6 → CoreCtl.bitAt M q = false := by
      intro q hq
      have h1 : symScan s m pin l q = none :=
        (List.findSome?_eq_none_iff.1 hsome) q (List.mem_range.mpr hq)
      exact (symScan_eq_none_iff s m pin hbusM hgrp hkind l q hq).1 h1
    have hM0 : M = 0 := by
      refine bits6_eq_zero _ (fun q hq => ?_)
      rw [← Moves.symMask_bit (hq := hq)]
      exact hbits q hq
    have hsw0 : symWord s pin l.val = 0 := by
      rw [hswOf, hM0, hitOr_zero]
    have hcut : (Bridge.Line.absIn (lineIn s pin l.val)).sym.map (fun w => (w.op, w.v)) = none := by
      have hif : (Bridge.Line.absIn (lineIn s pin l.val)).sym =
          (if (lineIn s pin l.val).symWe then
            some ⟨Bridge.Line.absSymOp (lineIn s pin l.val).symOp,
              (lineIn s pin l.val).symD.toNat⟩ else none) := rfl
      rw [hif, show (lineIn s pin l.val).symWe = Machine.Util.bit (symWord s pin l.val) 14
        from rfl, hsw0, util_bit_zero]
      rfl
    rw [hLHS, hsome, hcut]
  · -- a unique winner supplies the cut's word
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hsome
    obtain ⟨l₁, q, l₂, hsplit, hq_some, _hbefore⟩ := List.findSome?_eq_some_iff.1 hv
    have hqmem : q ∈ List.range 6 := by
      have hmem : q ∈ l₁ ++ q :: l₂ := List.mem_append_right _ (List.mem_cons_self ..)
      rwa [← hsplit] at hmem
    have hq6 : q < 6 := List.mem_range.1 hqmem
    have hne : symScan s m pin l q ≠ none := by
      rw [hq_some]
      exact Option.some_ne_none v
    have hbit : CoreCtl.bitAt M q = true := by
      by_cases hb : CoreCtl.bitAt M q = true
      · exact hb
      · have hbf : CoreCtl.bitAt M q = false := by simpa using hb
        rw [(symScan_eq_none_iff s m pin hbusM hgrp hkind l q hq6).2 hbf] at hne
        exact absurd rfl hne
    have hwin : Moves.winAt (movBundle s pin) q = true := by
      by_cases hb : Moves.winAt (movBundle s pin) q = true
      · exact hb
      · rw [symScan, if_neg (by simpa using hb)] at hne
        exact absurd rfl hne
    have hen : ((movBundle s pin).get q).enabled = true := by
      have hv' := Moves.winAt_valid hwin
      rw [show Moves.validAt ((movBundle s pin).get q) =
        (((movBundle s pin).get q).enabled &&
          !(((movBundle s pin).get q).group == Moves.dgNone)) from rfl, Bool.and_eq_true] at hv'
      exact hv'.1
    have hdstQ : (machMove s m pin q).dst = ((movBundle s pin).get q).dst.toNat :=
      machMove_dst s m pin hbusM q hq6 hen
    have hdataQ : (machMove s m pin q).v = ((movBundle s pin).get q).data.toNat :=
      machMove_data s m pin hbusM q hq6 hen
    have hdstSl : (machMove s m pin q).dst =
        (CoreCtl.slice (mvDst s pin) (6 * q) 6).toNat := by
      rw [hdstQ, movBundle_dst s pin q hq6]
      rfl
    have hdataSl : (machMove s m pin q).v =
        (CoreCtl.slice (mvDat s pin) (8 * q) 8).toNat := by
      rw [hdataQ, movBundle_data s pin q hq6]
      rfl
    have hdstlt : (machMove s m pin q).dst < 64 := by
      rw [hdstSl]
      exact (CoreCtl.slice (mvDst s pin) (6 * q) 6).isLt
    -- the mask bit's group and line conjuncts
    have hbit' := hbit
    rw [Moves.symMask_bit (hq := hq6), Bool.and_eq_true, Bool.and_eq_true] at hbit'
    have hgrpT : (Moves.dgTable ((movBundle s pin).get q).dst == Moves.dgLSym) = true := by
      have h3 : CoreCtl.slice (mvGrp s pin) (5 * q) 5 = ((movBundle s pin).get q).group :=
        (bundle_grp (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin) (mvXl s) (mvXt s)
          q hq6).symm
      rw [h3, hgrp q hq6] at hbit'
      exact hbit'.1.2
    have hgrpSl : (Moves.dgTable (CoreCtl.slice (mvDst s pin) (6 * q) 6) == Moves.dgLSym) = true := by
      rw [movBundle_dst s pin q hq6] at hgrpT
      exact hgrpT
    have hline : ((machMove s m pin q).line == l.val) = true := by
      rw [hbusM.line q hq6, ← beq_ofNat2_toNat _ l.val l.isLt]
      exact hbit'.2
    -- the winner's op code is its destination code
    have hlsym : Machine.dstOp (machMove s m pin q).dst =
        .lsym (CoreCtl.slice (mvDst s pin) (6 * q) 6).toNat := by
      cases hd : Machine.dstOp (machMove s m pin q).dst with
      | lsym op =>
        have hop : op = (CoreCtl.slice (mvDst s pin) (6 * q) 6).toNat := by
          rw [← hdstSl]
          exact hC.lsym ((machMove s m pin q).dst) hdstlt op hd
        rw [hop]
      | _ =>
        exfalso
        have his : isLsym (Machine.dstOp (machMove s m pin q).dst) = true := by
          rw [isLsym_eq_group hkind hdstlt, hdstSl, Bridge.Moves.ofNat_toNat_6]
          exact hgrpSl
        rw [hd] at his
        exact absurd his (by simp [isLsym])
    -- the machine's slot value
    have hmach : symScan s m pin l q =
        some ((CoreCtl.slice (mvDst s pin) (6 * q) 6).toNat,
          (CoreCtl.slice (mvDat s pin) (8 * q) 8).toNat % 16) := by
      rw [symScan_of_win s m pin l q hwin, hlsym]
      simp only [hdataSl, if_pos hline]
    have hval : v = ((CoreCtl.slice (mvDst s pin) (6 * q) 6).toNat,
        (CoreCtl.slice (mvDat s pin) (8 * q) 8).toNat % 16) := by
      rw [hmach] at hq_some
      exact (Option.some.inj hq_some).symm
    -- the cut's word is the same slot's word
    have hMq : M = (1 : BitVec 6) <<< q := eq_shift_of_atMostOne hM hq6 hbit
    have hsw : symWord s pin l.val =
        CoreCtl.makeWord true (CoreCtl.slice (mvDst s pin) (6 * q) 6)
          (CoreCtl.slice (mvDat s pin) (8 * q) 8) := by
      rw [hswOf, hMq, hitOr_onehot q hq6]
    have hsymWe : (lineIn s pin l.val).symWe = true := by
      rw [show (lineIn s pin l.val).symWe = Machine.Util.bit (symWord s pin l.val) 14 from rfl,
        util_bit_eq_bitAt, hsw]
      exact bitAt_makeWord_14 true _ _
    have hsymOp : (lineIn s pin l.val).symOp =
        Strobes.lineSop (CoreCtl.slice (mvDst s pin) (6 * q) 6) := by
      show Strobes.lineSop (CoreCtl.slice (symWord s pin l.val) 8 6) = _
      rw [hsw, show CoreCtl.slice (CoreCtl.makeWord true (CoreCtl.slice (mvDst s pin) (6 * q) 6)
        (CoreCtl.slice (mvDat s pin) (8 * q) 8)) 8 6 = CoreCtl.slice (mvDst s pin) (6 * q) 6
        from slice_makeWord_8_6 true _ _]
    have hsymD : (lineIn s pin l.val).symD.toNat =
        (CoreCtl.slice (mvDat s pin) (8 * q) 8).toNat % 16 := by
      show (BitVec.truncate 4 (symWord s pin l.val)).toNat = _
      rw [hsw, truncate_four_makeWord, truncate_four_toNat]
    have hcut : (Bridge.Line.absIn (lineIn s pin l.val)).sym.map (fun w => (w.op, w.v)) =
        some ((CoreCtl.slice (mvDst s pin) (6 * q) 6).toNat,
          (CoreCtl.slice (mvDat s pin) (8 * q) 8).toNat % 16) := by
      have hif : (Bridge.Line.absIn (lineIn s pin l.val)).sym =
          (if (lineIn s pin l.val).symWe then
            some ⟨Bridge.Line.absSymOp (lineIn s pin l.val).symOp,
              (lineIn s pin l.val).symD.toNat⟩ else none) := rfl
      rw [hif, hsymWe, if_pos rfl, Option.map_some]
      simp only [Option.some.injEq, Prod.mk.injEq]
      exact ⟨by rw [hsymOp, absSymOp_lineSop _ hgrpSl], hsymD⟩
    rw [hLHS, hv, hval, hcut]

end Metronome.ChipCut.Discharge.LineMoveWire
