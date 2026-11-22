import Metronome.Glue
import Metronome.Machine
import Std.Tactic.BVDecide

/-!
# Bridge: the chip-top glue cut (`Metronome.Glue`) and the machine glue

`Metronome/Glue.lean` is the independent specification of the chip-top glue
(sources, guards, control/mailbox registers, output pins) that `glue_check.py`
proves the elaborated RTL equal to.  `Metronome/Machine/**` is the whole-chip
executable machine.  This file proves that each glue quantity of the cut is the
corresponding machine function, under an explicit abstraction map from the
machine state to the cut's free leaves.

## Abstraction map

The cut binds every combinational input as a per-cycle leaf (`Sources`,
`Guards`, `LineGuards`, `GlueInput`, `OutCfg`).  The machine reads them from its
chip state.  The map is a function of the machine state and the cycle's decoded
configuration and pins (`Env`, `sourcesOf`, `guardsOf`, `lineGuardsOf`).

The machine's source and guard index decoders (`machine.SrcOp`,
`machine.GuardOp`) are built at definition time from string tables, and
`String.splitOnAux` is `@[irreducible]` in Lean 4.35.0 core, so the kernel
cannot evaluate the entries that go through `parsePort`.  The entries whose
names are in the decoder's fixed list (11 of 39 sources, 12 of 62 guards) are
checked in the kernel (`srcOp_fixed`, `guardOp_fixed`); the remaining entries
are the single global hypotheses `SrcTable`/`GuardTable`, checked by compiled
evaluation in `data/raw/lean_bridge_glue_debug_v4_20261121/decode_check.lean`.
This is a Lean-library reduction limitation, not a disagreement between the
specifications.

## Cycle boundary

Every theorem is about cycle-`t` values: the cut's state and the machine's
state are the same registers, and the machine's step is `Chip.runStep` (whose
pieces `ctrlNext`, `unitsNext`, `outNext`, `dbgNext` are read here).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Metronome.Bridge.Glue

open Metronome
open Metronome.Machine Metronome.Machine.Util

/-! ## Plumbing: bits, slices, list folds -/

/-- The cut's bit extractor is the machine's `nbit` of the value. -/
theorem bitAt_eq_nbit {w : Nat} (x : BitVec w) (i : Nat) :
    Metronome.Glue.bitAt x i = nbit x.toNat i := by
  rw [Bool.eq_iff_iff]
  simp only [Metronome.Glue.bitAt, nbit, BitVec.getLsbD, bne_iff_ne, ne_eq,
    BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod, Nat.reducePow,
    BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  rw [show BitVec.ushiftRight x i = (x >>> i) from rfl, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [show ((0 : BitVec 1)).toNat = 0 from by decide]
  rcases Nat.mod_two_eq_zero_or_one (x.toNat / 2 ^ i) with h | h <;> simp [h]

/-- The cut's slice has the machine's `nbits` value. -/
theorem slice_toNat {w : Nat} (x : BitVec w) (off n : Nat) :
    (Metronome.Glue.slice x off n).toNat = nbits x.toNat off n := by
  unfold Metronome.Glue.slice nbits
  rw [BitVec.truncate_eq_setWidth]
  simp only [BitVec.ushiftRight_eq, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]

/-- A one-bit source's byte. -/
theorem bitByte_toNat (b : Bool) : (Metronome.Glue.bitByte b).toNat = b2n b := by
  unfold Metronome.Glue.bitByte b2n
  cases b <;> rfl

/-- `Machine.Util.bv n x.toNat` is `x`. -/
theorem bv_toNat {n : Nat} (x : BitVec n) : bv n x.toNat = x := by
  simp [bv]

theorem b2n_lt (b : Bool) : b2n b < 2 := by cases b <;> decide

/-- The machine's `bit` is `nbit` of the value. -/
theorem bit_eq_nbit {w : Nat} (x : BitVec w) (i : Nat) : bit x i = nbit x.toNat i := by
  rw [Bool.eq_iff_iff]
  simp only [bit, nbit, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq,
    Nat.shiftRight_eq_div_pow, decide_eq_true_eq, beq_iff_eq]

/-- `b2n` of a bit is the bit as a `Nat`. -/
theorem b2n_nbit (m i : Nat) : b2n (nbit m i) = (m >>> i) % 2 := by
  unfold b2n nbit
  rw [Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ i) with h | h <;> simp [h]

/-- One bit of a two-entry packed vector. -/
theorem bit_two (a b : Bool) (k : Nat) (hk : k < 2) :
    nbit (b2n b * 2 + b2n a) k = (if k = 0 then a else b) := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;>
  · simp only [nbit, b2n]
    cases a <;> cases b <;> decide

/-- One bit of a three-entry packed vector. -/
theorem bit_three (a b c : Bool) (k : Nat) (hk : k < 3) :
    nbit (b2n c * 4 + b2n b * 2 + b2n a) k = (if k = 0 then a else if k = 1 then b else c) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
  · simp only [nbit, b2n]
    cases a <;> cases b <;> cases c <;> decide

/-- One bit of a four-entry packed vector. -/
theorem bit_four (a b c d : Bool) (k : Nat) (hk : k < 4) :
    nbit (b2n d * 8 + b2n c * 4 + b2n b * 2 + b2n a) k =
      (if k = 0 then a else if k = 1 then b else if k = 2 then c else d) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  · simp only [nbit, b2n]
    cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- The `Nat` value of a `BitVec 2` assembled as `hi * 2 + lo`. -/
theorem bv_two_toNat (hi lo : Bool) :
    (bv 2 (b2n hi * 2 + b2n lo)).toNat = b2n hi * 2 + b2n lo := by
  rw [bv]
  apply Nat.mod_eq_of_lt
  cases hi <;> cases lo <;> decide

/-- The `Nat` value of a `BitVec 3` assembled from three bits. -/
theorem bv_three_toNat (h2 h1 h0 : Bool) :
    (bv 3 (b2n h2 * 4 + b2n h1 * 2 + b2n h0)).toNat = b2n h2 * 4 + b2n h1 * 2 + b2n h0 := by
  rw [bv]
  apply Nat.mod_eq_of_lt
  cases h2 <;> cases h1 <;> cases h0 <;> decide

/-- The `Nat` value of a `BitVec 4` assembled from four bits. -/
theorem bv_four_toNat (h3 h2 h1 h0 : Bool) :
    (bv 4 (b2n h3 * 8 + b2n h2 * 4 + b2n h1 * 2 + b2n h0)).toNat =
      b2n h3 * 8 + b2n h2 * 4 + b2n h1 * 2 + b2n h0 := by
  rw [bv]
  apply Nat.mod_eq_of_lt
  cases h3 <;> cases h2 <;> cases h1 <;> cases h0 <;> decide

/-! ### Slices of concatenations, at the widths the glue uses -/

theorem slice64_0 (a b : BitVec 32) : Metronome.Glue.slice (a ++ b) 0 8 = Metronome.Glue.slice b 0 8 := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice64_8 (a b : BitVec 32) : Metronome.Glue.slice (a ++ b) 8 8 = Metronome.Glue.slice b 8 8 := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice64_16 (a b : BitVec 32) : Metronome.Glue.slice (a ++ b) 16 8 = Metronome.Glue.slice b 16 8 := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice64_24 (a b : BitVec 32) : Metronome.Glue.slice (a ++ b) 24 8 = Metronome.Glue.slice b 24 8 := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice64_32 (a b : BitVec 32) : Metronome.Glue.slice (a ++ b) 32 8 = Metronome.Glue.slice a 0 8 := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice64_40 (a b : BitVec 32) : Metronome.Glue.slice (a ++ b) 40 8 = Metronome.Glue.slice a 8 8 := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice64_48 (a b : BitVec 32) : Metronome.Glue.slice (a ++ b) 48 8 = Metronome.Glue.slice a 16 8 := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice64_56 (a b : BitVec 32) : Metronome.Glue.slice (a ++ b) 56 8 = Metronome.Glue.slice a 24 8 := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice48_0 (a b c : BitVec 16) :
    Metronome.Glue.slice ((a ++ b) ++ c) 0 8 = Metronome.Glue.slice c 0 8 := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice48_8 (a b c : BitVec 16) :
    Metronome.Glue.slice ((a ++ b) ++ c) 8 8 = Metronome.Glue.slice c 8 8 := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice48_16 (a b c : BitVec 16) :
    Metronome.Glue.slice ((a ++ b) ++ c) 16 8 = Metronome.Glue.slice b 0 8 := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice48_24 (a b c : BitVec 16) :
    Metronome.Glue.slice ((a ++ b) ++ c) 24 8 = Metronome.Glue.slice b 8 8 := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice48_32 (a b c : BitVec 16) :
    Metronome.Glue.slice ((a ++ b) ++ c) 32 8 = Metronome.Glue.slice a 0 8 := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice48_40 (a b c : BitVec 16) :
    Metronome.Glue.slice ((a ++ b) ++ c) 40 8 = Metronome.Glue.slice a 8 8 := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice_bytes_0 (a b c d : BitVec 8) :
    Metronome.Glue.slice (((a ++ b) ++ c) ++ d) 0 8 = d := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice_bytes_1 (a b c d : BitVec 8) :
    Metronome.Glue.slice (((a ++ b) ++ c) ++ d) 8 8 = c := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice_bytes_2 (a b c d : BitVec 8) :
    Metronome.Glue.slice (((a ++ b) ++ c) ++ d) 16 8 = b := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice_bytes_3 (a b c d : BitVec 8) :
    Metronome.Glue.slice (((a ++ b) ++ c) ++ d) 24 8 = a := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice16_0 (a b : BitVec 8) : Metronome.Glue.slice (a ++ b) 0 8 = b := by
  unfold Metronome.Glue.slice; bv_decide

theorem slice16_8 (a b : BitVec 8) : Metronome.Glue.slice (a ++ b) 8 8 = a := by
  unfold Metronome.Glue.slice; bv_decide

/-- The low bits of a two-chunk value `B + A * 2^m`. -/
theorem nbits_low {m : Nat} (A B off w : Nat) (_hB : B < 2 ^ m) (h : off + w ≤ m) :
    nbits (B + A * 2 ^ m) off w = nbits B off w := by
  unfold nbits
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hm : A * 2 ^ m = A * 2 ^ (m - off) * 2 ^ off := by
    rw [Nat.mul_assoc, Nat.mul_comm (2 ^ (m - off)) (2 ^ off), ← Nat.pow_add,
      Nat.add_sub_cancel' (by omega : off ≤ m)]
  rw [hm, Nat.add_mul_div_right B (A * 2 ^ (m - off)) (Nat.two_pow_pos off)]
  have hd : 2 ^ (m - off) = 2 ^ w * 2 ^ (m - off - w) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega : w ≤ m - off)]
  rw [hd, Nat.mul_left_comm, Nat.mul_comm (2 ^ w), Nat.add_mul_mod_self_right]

/-- The high bits of a two-chunk value `B + A * 2^m`. -/
theorem nbits_high {m : Nat} (A B off w : Nat) (hB : B < 2 ^ m) :
    nbits (B + A * 2 ^ m) (m + off) w = nbits A off w := by
  unfold nbits
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_add,
    ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right B A (Nat.two_pow_pos m),
    Nat.div_eq_of_lt hB, Nat.zero_add]

/-! ## The abstraction map -/

structure Env where
  ms : Machine.State
  cv : Machine.CfgView
  p : Machine.PinView
  l : Nat
  imm : Nat
  hlvl : p.lvl < 2 ^ 13

/-- The machine's source port value for slot `i`. -/
def srcV (e : Env) (i : Nat) : Nat :=
  srcVal e.ms e.cv e.p e.l e.imm (srcOp i)

/-- The machine's guard value for slot `i`, read on line `l`. -/
def guardV (e : Env) (i : Nat) : Bool :=
  guardVal e.ms e.cv e.p e.l (guardOp i)

/-- `SHk.OUT` of shifter `k`. -/
def shOk (u : UnitsSt) (k : Nat) : Bool := shOut (vget u.sh k)

/-- `SHk.DONE` of shifter `k`. -/
def doneK (u : UnitsSt) (k : Nat) : Bool := (vget u.sh k).cnt.toNat == 0

/-- The cut's `Sources` leaves from the machine state. -/
def sourcesOf (e : Env) : Metronome.Glue.Sources :=
  let u := e.ms.units
  { fl := u.f
    pins := bv 13 e.p.lvl
    accA := u.a
    accR := ((vget u.r 3 ++ vget u.r 2) ++ vget u.r 1) ++ vget u.r 0
    shD := (vget u.sh 1).d ++ (vget u.sh 0).d
    shO := bv 2 (b2n (shOk u 1) * 2 + b2n (shOk u 0))
    cnV := (vget u.cnt 2 ++ vget u.cnt 1) ++ vget u.cnt 0
    lfS := vget u.lf 1 ++ vget u.lf 0
    pDat := e.ms.p0.d
    sBit := bv 2 (b2n (streamBit (vget e.cv.streams 1) 1 e.ms.dbg (vget e.ms.streams 1)) * 2 +
      b2n (streamBit (vget e.cv.streams 0) 0 e.ms.dbg (vget e.ms.streams 0)))
    sByte := (bv 8 (streamByte (vget e.cv.streams 1) (vget e.ms.streams 1))) ++
      (bv 8 (streamByte (vget e.cv.streams 0) (vget e.ms.streams 0)))
    inB := e.ms.ctrl.inb }

/-- The cut's `Guards` leaves from the machine state. -/
def guardsOf (e : Env) : Metronome.Glue.Guards :=
  let u := e.ms.units
  { fl := u.f
    shDone := bv 2 (b2n (doneK u 1) * 2 + b2n (doneK u 0))
    shOut := bv 2 (b2n (shOk u 1) * 2 + b2n (shOk u 0))
    cntZ := bv 3 (b2n ((vget u.cnt 2).toNat == 0) * 4 + b2n ((vget u.cnt 1).toNat == 0) * 2 +
      b2n ((vget u.cnt 0).toNat == 0))
    accZ := u.z
    accC := u.c
    accN := u.n
    lfS := vget u.lf 1 ++ vget u.lf 0
    inv := e.ms.ctrl.inv
    outv := e.ms.ctrl.outv
    pRdy := e.ms.p0.rdy
    sEnd := bv 2 (b2n (streamEnd (vget e.cv.streams 1) (vget e.ms.streams 1)) * 2 +
      b2n (streamEnd (vget e.cv.streams 0) (vget e.ms.streams 0)))
    sMark := bv 2 (b2n (streamMark (vget e.cv.streams 1) (vget e.ms.streams 1)) * 2 +
      b2n (streamMark (vget e.cv.streams 0) (vget e.ms.streams 0)))
    sByte := bv 2 (b2n (streamAtByte (vget e.ms.streams 1)) * 2 +
      b2n (streamAtByte (vget e.ms.streams 0)))
    sBit := bv 2 (b2n (streamBit (vget e.cv.streams 1) 1 e.ms.dbg (vget e.ms.streams 1)) * 2 +
      b2n (streamBit (vget e.cv.streams 0) 0 e.ms.dbg (vget e.ms.streams 0)))
    pins := bv 13 e.p.lvl
    lRun := bv 4 (b2n (vget e.ms.lines 3).run * 8 + b2n (vget e.ms.lines 2).run * 4 +
      b2n (vget e.ms.lines 1).run * 2 + b2n (vget e.ms.lines 0).run) }

/-- The cut's `LineGuards` leaves from the machine state. -/
def lineGuardsOf (e : Env) : Metronome.Glue.LineGuards :=
  let sym (l : Nat) : Nat := inSym (vget e.cv.lines l) (vget e.ms.lines l)
  { inn := bv 8 ((sym 3) * 64 + (sym 2) * 16 + (sym 1) * 4 + (sym 0))
    sp := bv 4 (b2n (vget e.ms.lines 3).sp * 8 + b2n (vget e.ms.lines 2).sp * 4 +
      b2n (vget e.ms.lines 1).sp * 2 + b2n (vget e.ms.lines 0).sp)
    pinA := bv 4 (b2n (e.p.pin (vget e.cv.lines 3).pina) * 8 +
      b2n (e.p.pin (vget e.cv.lines 2).pina) * 4 +
      b2n (e.p.pin (vget e.cv.lines 1).pina) * 2 + b2n (e.p.pin (vget e.cv.lines 0).pina))
    pinB := bv 4 (b2n (e.p.pin (vget e.cv.lines 3).pinb) * 8 +
      b2n (e.p.pin (vget e.cv.lines 2).pinb) * 4 +
      b2n (e.p.pin (vget e.cv.lines 1).pinb) * 2 + b2n (e.p.pin (vget e.cv.lines 0).pinb)) }

/-! ## The machine's source and guard tables -/

/-- The ISA source table as machine constructors (index 39 and above read `ZERO`). -/
def srcOpOf : Nat → SrcOp
  | 0 => .zero
  | 1 => .imm
  | 2 => .lIn
  | 3 => .lCap
  | 4 => .flagsLo
  | 5 => .flagsHi
  | 6 => .pinsLo
  | 7 => .pinsHi
  | 8 => .acc
  | 9 => .reg 0
  | 10 => .reg 1
  | 11 => .reg 2
  | 12 => .reg 3
  | 13 => .shD 0
  | 14 => .shD 1
  | 15 => .shO 0
  | 16 => .shO 1
  | 17 => .cntLo 0
  | 18 => .cntLo 1
  | 19 => .cntLo 2
  | 20 => .cntHi 0
  | 21 => .cntHi 1
  | 22 => .cntHi 2
  | 23 => .lfB 0 0
  | 24 => .lfB 0 1
  | 25 => .lfB 0 2
  | 26 => .lfB 0 3
  | 27 => .lfB 1 0
  | 28 => .lfB 1 1
  | 29 => .lfB 1 2
  | 30 => .lfB 1 3
  | 31 => .lfO 0
  | 32 => .lfO 1
  | 33 => .pD
  | 34 => .sBit 0
  | 35 => .sBit 1
  | 36 => .sByte 0
  | 37 => .sByte 1
  | 38 => .hostIn
  | _ => .zero

/-- The ISA guard table as machine constructors (index 62 and above are `invalid`). -/
def guardOpOf : Nat → GuardOp
  | 0 => .true_
  | 1 => .flag 0
  | 2 => .flag 1
  | 3 => .flag 2
  | 4 => .flag 3
  | 5 => .flag 4
  | 6 => .flag 5
  | 7 => .flag 6
  | 8 => .flag 7
  | 9 => .flag 8
  | 10 => .flag 9
  | 11 => .flag 10
  | 12 => .flag 11
  | 13 => .flag 12
  | 14 => .flag 13
  | 15 => .flag 14
  | 16 => .flag 15
  | 17 => .shDone 0
  | 18 => .shDone 1
  | 19 => .shOut 0
  | 20 => .shOut 1
  | 21 => .cntZ 0
  | 22 => .cntZ 1
  | 23 => .cntZ 2
  | 24 => .accZ
  | 25 => .accC
  | 26 => .accN
  | 27 => .lIn0
  | 28 => .lIn1
  | 29 => .lSync
  | 30 => .lPinA
  | 31 => .lPinB
  | 32 => .lfOut 0
  | 33 => .lfOut 1
  | 34 => .hostInv
  | 35 => .hostOutE
  | 36 => .pRdy
  | 37 => .sEnd 0
  | 38 => .sEnd 1
  | 39 => .sMark 0
  | 40 => .sMark 1
  | 41 => .sByte 0
  | 42 => .sByte 1
  | 43 => .sBit 0
  | 44 => .sBit 1
  | 45 => .pin 0
  | 46 => .pin 1
  | 47 => .pin 2
  | 48 => .pin 3
  | 49 => .pin 4
  | 50 => .pin 5
  | 51 => .pin 6
  | 52 => .pin 7
  | 53 => .pin 8
  | 54 => .pin 9
  | 55 => .pin 10
  | 56 => .pin 11
  | 57 => .pin 12
  | 58 => .lRun 0
  | 59 => .lRun 1
  | 60 => .lRun 2
  | 61 => .lRun 3
  | _ => .invalid

structure SrcTable : Prop where
  eq : ∀ i, Machine.srcOp i = srcOpOf i

structure GuardTable : Prop where
  eq : ∀ i, Machine.guardOp i = guardOpOf i

theorem srcOp_eq (i : Nat) :
    Machine.srcOp i =
      ((Tables.srcNames[i]?).map srcOfName).getD .zero := by
  simp only [Machine.srcOp, srcOps, Array.getD_eq_getD_getElem?, Array.getElem?_map]

theorem guardOp_eq (i : Nat) :
    Machine.guardOp i =
      ((Tables.guardNames[i]?).map guardOfName).getD .invalid := by
  simp only [Machine.guardOp, guardOps, Array.getD_eq_getD_getElem?, Array.getElem?_map]

deriving instance DecidableEq for Metronome.Machine.SrcOp
deriving instance DecidableEq for Metronome.Machine.GuardOp

theorem srcOp_fixed :
    Machine.srcOp 0 = .zero ∧ Machine.srcOp 1 = .imm ∧ Machine.srcOp 2 = .lIn ∧
    Machine.srcOp 3 = .lCap ∧ Machine.srcOp 4 = .flagsLo ∧ Machine.srcOp 5 = .flagsHi ∧
    Machine.srcOp 6 = .pinsLo ∧ Machine.srcOp 7 = .pinsHi ∧ Machine.srcOp 8 = .acc ∧
    Machine.srcOp 33 = .pD ∧ Machine.srcOp 38 = .hostIn := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [srcOp_eq] <;> decide

theorem guardOp_fixed :
    Machine.guardOp 0 = .true_ ∧ Machine.guardOp 24 = .accZ ∧
    Machine.guardOp 25 = .accC ∧ Machine.guardOp 26 = .accN ∧
    Machine.guardOp 34 = .hostInv ∧ Machine.guardOp 35 = .hostOutE ∧
    Machine.guardOp 36 = .pRdy := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [guardOp_eq] <;> decide


/-! ## Sources: the 64 slots

Each slot theorem says: the machine's `srcVal` of the slot's ISA source port is the
cut's `srcAt` slot value, given the table hypothesis.  The four core-local ports
(`ZERO`, `IMM`, `L.IN`, `L.CAP`) are *not* zero in the machine (the machine reads the
core-local value); the cut's global vector has them zero because each core substitutes
them (`Metronome.Core`), so their machine-side values are stated separately. -/

theorem src_slot_0 (h : SrcTable) (e : Env) :
    srcV e 0 = (Metronome.Glue.srcAt 0 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  rfl

theorem src_slot_1 (h : SrcTable) (e : Env) :
    srcV e 1 = e.imm % 256 := by
  rw [srcV, h.eq]
  simp [srcOpOf, srcVal]

theorem src_slot_2 (h : SrcTable) (e : Env) :
    srcV e 2 = inSym (vget e.cv.lines e.l) (vget e.ms.lines e.l) := by
  rw [srcV, h.eq]
  simp [srcOpOf, srcVal]

theorem src_slot_3 (h : SrcTable) (e : Env) :
    srcV e 3 = b2n (vget e.ms.lines e.l).rem * 16 + (vget e.ms.lines e.l).sn.toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, srcVal]

theorem src_slot_4 (h : SrcTable) (e : Env) :
    srcV e 4 = (Metronome.Glue.srcAt 4 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, getByte, slice_toNat]

theorem src_slot_5 (h : SrcTable) (e : Env) :
    srcV e 5 = (Metronome.Glue.srcAt 5 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, getByte, slice_toNat]

theorem src_slot_6 (h : SrcTable) (e : Env) :
    srcV e 6 = (Metronome.Glue.srcAt 6 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp only [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, nbits, bv,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.shiftRight_eq_div_pow, Nat.div_one, Nat.zero_add,
    Nat.mod_eq_of_lt e.hlvl]

theorem src_slot_7 (h : SrcTable) (e : Env) :
    srcV e 7 = (Metronome.Glue.srcAt 7 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp only [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, nbits, bv,
    BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.reducePow, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt e.hlvl]
  have hlt : e.p.lvl / 256 % 32 < 256 := by
    have := Nat.mod_lt (e.p.lvl / 256) (by decide : 0 < 32)
    omega
  rw [Nat.mod_eq_of_lt hlt]

theorem src_slot_8 (h : SrcTable) (e : Env) :
    srcV e 8 = (Metronome.Glue.srcAt 8 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal]

theorem src_slot_9 (h : SrcTable) (e : Env) :
    srcV e 9 = (Metronome.Glue.srcAt 9 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice_bytes_0]

theorem src_slot_10 (h : SrcTable) (e : Env) :
    srcV e 10 = (Metronome.Glue.srcAt 10 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice_bytes_1]

theorem src_slot_11 (h : SrcTable) (e : Env) :
    srcV e 11 = (Metronome.Glue.srcAt 11 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice_bytes_2]

theorem src_slot_12 (h : SrcTable) (e : Env) :
    srcV e 12 = (Metronome.Glue.srcAt 12 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice_bytes_3]

theorem src_slot_13 (h : SrcTable) (e : Env) :
    srcV e 13 = (Metronome.Glue.srcAt 13 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice16_0]

theorem src_slot_14 (h : SrcTable) (e : Env) :
    srcV e 14 = (Metronome.Glue.srcAt 14 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice16_8]

theorem src_slot_15 (h : SrcTable) (e : Env) :
    srcV e 15 = (Metronome.Glue.srcAt 15 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp only [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, bitByte_toNat, shOk,
    bitAt_eq_nbit, bv_two_toNat, b2n_nbit, Nat.reducePow]
  have h0 := b2n_lt (shOut (vget e.ms.units.sh 0))
  have h1 := b2n_lt (shOut (vget e.ms.units.sh 1))
  omega

theorem src_slot_16 (h : SrcTable) (e : Env) :
    srcV e 16 = (Metronome.Glue.srcAt 16 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp only [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, bitByte_toNat, shOk,
    bitAt_eq_nbit, bv_two_toNat, b2n_nbit, Nat.reducePow]
  have h0 := b2n_lt (shOut (vget e.ms.units.sh 0))
  have h1 := b2n_lt (shOut (vget e.ms.units.sh 1))
  omega

theorem src_slot_17 (h : SrcTable) (e : Env) :
    srcV e 17 = (Metronome.Glue.srcAt 17 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice48_0, getByte]

theorem src_slot_18 (h : SrcTable) (e : Env) :
    srcV e 18 = (Metronome.Glue.srcAt 18 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice48_16, getByte]

theorem src_slot_19 (h : SrcTable) (e : Env) :
    srcV e 19 = (Metronome.Glue.srcAt 19 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice48_32, getByte]

theorem src_slot_20 (h : SrcTable) (e : Env) :
    srcV e 20 = (Metronome.Glue.srcAt 20 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice48_8, getByte]

theorem src_slot_21 (h : SrcTable) (e : Env) :
    srcV e 21 = (Metronome.Glue.srcAt 21 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice48_24, getByte]

theorem src_slot_22 (h : SrcTable) (e : Env) :
    srcV e 22 = (Metronome.Glue.srcAt 22 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice48_40, getByte]

theorem src_slot_23 (h : SrcTable) (e : Env) :
    srcV e 23 = (Metronome.Glue.srcAt 23 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice64_0, getByte]

theorem src_slot_24 (h : SrcTable) (e : Env) :
    srcV e 24 = (Metronome.Glue.srcAt 24 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice64_8, getByte]

theorem src_slot_25 (h : SrcTable) (e : Env) :
    srcV e 25 = (Metronome.Glue.srcAt 25 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice64_16, getByte]

theorem src_slot_26 (h : SrcTable) (e : Env) :
    srcV e 26 = (Metronome.Glue.srcAt 26 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice64_24, getByte]

theorem src_slot_27 (h : SrcTable) (e : Env) :
    srcV e 27 = (Metronome.Glue.srcAt 27 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice64_32, getByte]

theorem src_slot_28 (h : SrcTable) (e : Env) :
    srcV e 28 = (Metronome.Glue.srcAt 28 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice64_40, getByte]

theorem src_slot_29 (h : SrcTable) (e : Env) :
    srcV e 29 = (Metronome.Glue.srcAt 29 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice64_48, getByte]

theorem src_slot_30 (h : SrcTable) (e : Env) :
    srcV e 30 = (Metronome.Glue.srcAt 30 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice64_56, getByte]

theorem src_slot_31 (h : SrcTable) (e : Env) :
    srcV e 31 = (Metronome.Glue.srcAt 31 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp only [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, bitByte_toNat, bitAt_eq_nbit,
    bit_eq_nbit, b2n_nbit, BitVec.toNat_append]
  have hB : (vget e.ms.units.lf 0).toNat < 2 ^ 32 := (vget e.ms.units.lf 0).isLt
  have hL : (vget e.ms.units.lf 1).toNat <<< 32 ||| (vget e.ms.units.lf 0).toNat =
      (vget e.ms.units.lf 0).toNat + (vget e.ms.units.lf 1).toNat * 2 ^ 32 := by
    rw [Nat.shiftLeft_eq, Nat.mul_comm (vget e.ms.units.lf 1).toNat (2 ^ 32),
      ← Nat.two_pow_add_eq_or_of_lt hB, Nat.mul_comm (2 ^ 32), Nat.add_comm]
  rw [hL]
  have hh := nbits_low (A := (vget e.ms.units.lf 1).toNat) (B := (vget e.ms.units.lf 0).toNat)
    (off := 0) (w := 1) hB (by omega)
  simpa [nbits, nbit, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.div_one] using hh.symm

theorem src_slot_32 (h : SrcTable) (e : Env) :
    srcV e 32 = (Metronome.Glue.srcAt 32 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp only [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, bitByte_toNat, bitAt_eq_nbit,
    bit_eq_nbit, b2n_nbit, BitVec.toNat_append]
  have hB : (vget e.ms.units.lf 0).toNat < 2 ^ 32 := (vget e.ms.units.lf 0).isLt
  have hL : (vget e.ms.units.lf 1).toNat <<< 32 ||| (vget e.ms.units.lf 0).toNat =
      (vget e.ms.units.lf 0).toNat + (vget e.ms.units.lf 1).toNat * 2 ^ 32 := by
    rw [Nat.shiftLeft_eq, Nat.mul_comm (vget e.ms.units.lf 1).toNat (2 ^ 32),
      ← Nat.two_pow_add_eq_or_of_lt hB, Nat.mul_comm (2 ^ 32), Nat.add_comm]
  rw [hL]
  have hh := nbits_high (m := 32) (A := (vget e.ms.units.lf 1).toNat)
    (B := (vget e.ms.units.lf 0).toNat) (off := 0) (w := 1) hB
  simpa [nbits, nbit, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.div_one] using hh.symm

theorem src_slot_33 (h : SrcTable) (e : Env) :
    srcV e 33 = (Metronome.Glue.srcAt 33 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal]

theorem src_slot_34 (h : SrcTable) (e : Env) :
    srcV e 34 = (Metronome.Glue.srcAt 34 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp only [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, bitByte_toNat, bitAt_eq_nbit,
    bv_two_toNat, b2n_nbit, Nat.reducePow]
  have h0 := b2n_lt (streamBit (vget e.cv.streams 0) 0 e.ms.dbg (vget e.ms.streams 0))
  have h1 := b2n_lt (streamBit (vget e.cv.streams 1) 1 e.ms.dbg (vget e.ms.streams 1))
  omega

theorem src_slot_35 (h : SrcTable) (e : Env) :
    srcV e 35 = (Metronome.Glue.srcAt 35 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp only [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, bitByte_toNat, bitAt_eq_nbit,
    bv_two_toNat, b2n_nbit, Nat.reducePow]
  have h0 := b2n_lt (streamBit (vget e.cv.streams 0) 0 e.ms.dbg (vget e.ms.streams 0))
  have h1 := b2n_lt (streamBit (vget e.cv.streams 1) 1 e.ms.dbg (vget e.ms.streams 1))
  omega

theorem streamByte_lt (c : StreamCfg) (s : StreamSt) : streamByte c s < 256 := by
  unfold streamByte
  split
  · exact s.pend.isLt
  · exact s.cur.isLt

theorem src_slot_36 (h : SrcTable) (e : Env) :
    srcV e 36 = (Metronome.Glue.srcAt 36 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp only [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice16_0]
  have h0 := streamByte_lt (vget e.cv.streams 0) (vget e.ms.streams 0)
  simp [bv, Nat.mod_eq_of_lt h0]

theorem src_slot_37 (h : SrcTable) (e : Env) :
    srcV e 37 = (Metronome.Glue.srcAt 37 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp only [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal, slice_toNat, slice16_8]
  have h1 := streamByte_lt (vget e.cv.streams 1) (vget e.ms.streams 1)
  simp [bv, Nat.mod_eq_of_lt h1]

theorem src_slot_38 (h : SrcTable) (e : Env) :
    srcV e 38 = (Metronome.Glue.srcAt 38 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]
  simp [srcOpOf, Metronome.Glue.srcAt, sourcesOf, srcVal]

theorem src_slot_39 (h : SrcTable) (e : Env) :
    srcV e 39 = (Metronome.Glue.srcAt 39 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_40 (h : SrcTable) (e : Env) :
    srcV e 40 = (Metronome.Glue.srcAt 40 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_41 (h : SrcTable) (e : Env) :
    srcV e 41 = (Metronome.Glue.srcAt 41 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_42 (h : SrcTable) (e : Env) :
    srcV e 42 = (Metronome.Glue.srcAt 42 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_43 (h : SrcTable) (e : Env) :
    srcV e 43 = (Metronome.Glue.srcAt 43 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_44 (h : SrcTable) (e : Env) :
    srcV e 44 = (Metronome.Glue.srcAt 44 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_45 (h : SrcTable) (e : Env) :
    srcV e 45 = (Metronome.Glue.srcAt 45 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_46 (h : SrcTable) (e : Env) :
    srcV e 46 = (Metronome.Glue.srcAt 46 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_47 (h : SrcTable) (e : Env) :
    srcV e 47 = (Metronome.Glue.srcAt 47 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_48 (h : SrcTable) (e : Env) :
    srcV e 48 = (Metronome.Glue.srcAt 48 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_49 (h : SrcTable) (e : Env) :
    srcV e 49 = (Metronome.Glue.srcAt 49 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_50 (h : SrcTable) (e : Env) :
    srcV e 50 = (Metronome.Glue.srcAt 50 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_51 (h : SrcTable) (e : Env) :
    srcV e 51 = (Metronome.Glue.srcAt 51 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_52 (h : SrcTable) (e : Env) :
    srcV e 52 = (Metronome.Glue.srcAt 52 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_53 (h : SrcTable) (e : Env) :
    srcV e 53 = (Metronome.Glue.srcAt 53 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_54 (h : SrcTable) (e : Env) :
    srcV e 54 = (Metronome.Glue.srcAt 54 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_55 (h : SrcTable) (e : Env) :
    srcV e 55 = (Metronome.Glue.srcAt 55 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_56 (h : SrcTable) (e : Env) :
    srcV e 56 = (Metronome.Glue.srcAt 56 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_57 (h : SrcTable) (e : Env) :
    srcV e 57 = (Metronome.Glue.srcAt 57 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_58 (h : SrcTable) (e : Env) :
    srcV e 58 = (Metronome.Glue.srcAt 58 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_59 (h : SrcTable) (e : Env) :
    srcV e 59 = (Metronome.Glue.srcAt 59 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_60 (h : SrcTable) (e : Env) :
    srcV e 60 = (Metronome.Glue.srcAt 60 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_61 (h : SrcTable) (e : Env) :
    srcV e 61 = (Metronome.Glue.srcAt 61 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_62 (h : SrcTable) (e : Env) :
    srcV e 62 = (Metronome.Glue.srcAt 62 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

theorem src_slot_63 (h : SrcTable) (e : Env) :
    srcV e 63 = (Metronome.Glue.srcAt 63 (sourcesOf e)).toNat := by
  rw [srcV, h.eq]; rfl

/-! ## Guards: the 64 global slots

The five line-relative guard slots (27..31) are supplied per line by the chip top's
`g_line` bundle; the machine evaluates them on the reading line `l`.  The cut's global
vector reads `false` there, and `lineGuard`'s bundle is the machine's per-line value
(see `line_guard_*` below). -/

theorem guard_slot_0 (h : GuardTable) (e : Env) :
    guardV e 0 = Metronome.Glue.guardAt 0 (guardsOf e) := by
  rw [guardV, h.eq]
  rfl

theorem guard_slot_1 (h : GuardTable) (e : Env) :
    guardV e 1 = Metronome.Glue.guardAt 1 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_2 (h : GuardTable) (e : Env) :
    guardV e 2 = Metronome.Glue.guardAt 2 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_3 (h : GuardTable) (e : Env) :
    guardV e 3 = Metronome.Glue.guardAt 3 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_4 (h : GuardTable) (e : Env) :
    guardV e 4 = Metronome.Glue.guardAt 4 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_5 (h : GuardTable) (e : Env) :
    guardV e 5 = Metronome.Glue.guardAt 5 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_6 (h : GuardTable) (e : Env) :
    guardV e 6 = Metronome.Glue.guardAt 6 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_7 (h : GuardTable) (e : Env) :
    guardV e 7 = Metronome.Glue.guardAt 7 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_8 (h : GuardTable) (e : Env) :
    guardV e 8 = Metronome.Glue.guardAt 8 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_9 (h : GuardTable) (e : Env) :
    guardV e 9 = Metronome.Glue.guardAt 9 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_10 (h : GuardTable) (e : Env) :
    guardV e 10 = Metronome.Glue.guardAt 10 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_11 (h : GuardTable) (e : Env) :
    guardV e 11 = Metronome.Glue.guardAt 11 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_12 (h : GuardTable) (e : Env) :
    guardV e 12 = Metronome.Glue.guardAt 12 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_13 (h : GuardTable) (e : Env) :
    guardV e 13 = Metronome.Glue.guardAt 13 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_14 (h : GuardTable) (e : Env) :
    guardV e 14 = Metronome.Glue.guardAt 14 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_15 (h : GuardTable) (e : Env) :
    guardV e 15 = Metronome.Glue.guardAt 15 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_16 (h : GuardTable) (e : Env) :
    guardV e 16 = Metronome.Glue.guardAt 16 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bit_eq_nbit]

theorem guard_slot_17 (h : GuardTable) (e : Env) :
    guardV e 17 = Metronome.Glue.guardAt 17 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, doneK, bitAt_eq_nbit,
    bv_two_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_two ((vget e.ms.units.sh 0).cnt.toNat == 0)
    ((vget e.ms.units.sh 1).cnt.toNat == 0) 0 (by omega)]
  simp

theorem guard_slot_18 (h : GuardTable) (e : Env) :
    guardV e 18 = Metronome.Glue.guardAt 18 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, doneK, bitAt_eq_nbit,
    bv_two_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_two ((vget e.ms.units.sh 0).cnt.toNat == 0)
    ((vget e.ms.units.sh 1).cnt.toNat == 0) 1 (by omega)]
  simp

theorem guard_slot_19 (h : GuardTable) (e : Env) :
    guardV e 19 = Metronome.Glue.guardAt 19 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, shOk, bitAt_eq_nbit,
    bv_two_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_two (shOut (vget e.ms.units.sh 0)) (shOut (vget e.ms.units.sh 1)) 0 (by omega)]
  simp

theorem guard_slot_20 (h : GuardTable) (e : Env) :
    guardV e 20 = Metronome.Glue.guardAt 20 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, shOk, bitAt_eq_nbit,
    bv_two_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_two (shOut (vget e.ms.units.sh 0)) (shOut (vget e.ms.units.sh 1)) 1 (by omega)]
  simp

theorem guard_slot_21 (h : GuardTable) (e : Env) :
    guardV e 21 = Metronome.Glue.guardAt 21 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bv_three_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_three ((vget e.ms.units.cnt 0).toNat == 0) ((vget e.ms.units.cnt 1).toNat == 0)
    ((vget e.ms.units.cnt 2).toNat == 0) 0 (by omega)]
  simp

theorem guard_slot_22 (h : GuardTable) (e : Env) :
    guardV e 22 = Metronome.Glue.guardAt 22 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bv_three_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_three ((vget e.ms.units.cnt 0).toNat == 0) ((vget e.ms.units.cnt 1).toNat == 0)
    ((vget e.ms.units.cnt 2).toNat == 0) 1 (by omega)]
  simp

theorem guard_slot_23 (h : GuardTable) (e : Env) :
    guardV e 23 = Metronome.Glue.guardAt 23 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bv_three_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_three ((vget e.ms.units.cnt 0).toNat == 0) ((vget e.ms.units.cnt 1).toNat == 0)
    ((vget e.ms.units.cnt 2).toNat == 0) 2 (by omega)]
  simp

theorem guard_slot_24 (h : GuardTable) (e : Env) :
    guardV e 24 = Metronome.Glue.guardAt 24 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal]

theorem guard_slot_25 (h : GuardTable) (e : Env) :
    guardV e 25 = Metronome.Glue.guardAt 25 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal]

theorem guard_slot_26 (h : GuardTable) (e : Env) :
    guardV e 26 = Metronome.Glue.guardAt 26 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal]

theorem guard_slot_32 (h : GuardTable) (e : Env) :
    guardV e 32 = Metronome.Glue.guardAt 32 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bit_eq_nbit, b2n_nbit, BitVec.toNat_append]
  have hB : (vget e.ms.units.lf 0).toNat < 2 ^ 32 := (vget e.ms.units.lf 0).isLt
  have hL : (vget e.ms.units.lf 1).toNat <<< 32 ||| (vget e.ms.units.lf 0).toNat =
      (vget e.ms.units.lf 0).toNat + (vget e.ms.units.lf 1).toNat * 2 ^ 32 := by
    rw [Nat.shiftLeft_eq, Nat.mul_comm (vget e.ms.units.lf 1).toNat (2 ^ 32),
      ← Nat.two_pow_add_eq_or_of_lt hB, Nat.mul_comm (2 ^ 32), Nat.add_comm]
  rw [hL]
  have hh := nbits_low (A := (vget e.ms.units.lf 1).toNat) (B := (vget e.ms.units.lf 0).toNat)
    (off := 0) (w := 1) hB (by omega)
  have hb : (vget e.ms.units.lf 0).toNat % 2 =
      ((vget e.ms.units.lf 0).toNat + (vget e.ms.units.lf 1).toNat * 2 ^ 32) % 2 := by
    simpa [nbits, Nat.reducePow, Nat.shiftRight_eq_div_pow, Nat.div_one] using hh.symm
  simp only [nbit, Nat.pow_one, Nat.reducePow, Nat.shiftRight_eq_div_pow, Nat.div_one]
  rw [hb]

theorem guard_slot_33 (h : GuardTable) (e : Env) :
    guardV e 33 = Metronome.Glue.guardAt 33 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bit_eq_nbit, b2n_nbit, BitVec.toNat_append]
  have hB : (vget e.ms.units.lf 0).toNat < 2 ^ 32 := (vget e.ms.units.lf 0).isLt
  have hL : (vget e.ms.units.lf 1).toNat <<< 32 ||| (vget e.ms.units.lf 0).toNat =
      (vget e.ms.units.lf 0).toNat + (vget e.ms.units.lf 1).toNat * 2 ^ 32 := by
    rw [Nat.shiftLeft_eq, Nat.mul_comm (vget e.ms.units.lf 1).toNat (2 ^ 32),
      ← Nat.two_pow_add_eq_or_of_lt hB, Nat.mul_comm (2 ^ 32), Nat.add_comm]
  rw [hL]
  have hh := nbits_high (m := 32) (A := (vget e.ms.units.lf 1).toNat)
    (B := (vget e.ms.units.lf 0).toNat) (off := 0) (w := 1) hB
  have hb : (vget e.ms.units.lf 1).toNat % 2 =
      ((vget e.ms.units.lf 0).toNat + (vget e.ms.units.lf 1).toNat * 2 ^ 32) / 2 ^ 32 % 2 := by
    simpa [nbits, Nat.reducePow, Nat.shiftRight_eq_div_pow, Nat.div_one] using hh.symm
  simp only [nbit, Nat.pow_one, Nat.reducePow, Nat.shiftRight_eq_div_pow, Nat.div_one]
  rw [hb]

theorem guard_slot_34 (h : GuardTable) (e : Env) :
    guardV e 34 = Metronome.Glue.guardAt 34 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal]

theorem guard_slot_35 (h : GuardTable) (e : Env) :
    guardV e 35 = Metronome.Glue.guardAt 35 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal]

theorem guard_slot_36 (h : GuardTable) (e : Env) :
    guardV e 36 = Metronome.Glue.guardAt 36 (guardsOf e) := by
  rw [guardV, h.eq]
  simp [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal]

theorem guard_slot_37 (h : GuardTable) (e : Env) :
    guardV e 37 = Metronome.Glue.guardAt 37 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bv_two_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_two (streamEnd (vget e.cv.streams 0) (vget e.ms.streams 0))
    (streamEnd (vget e.cv.streams 1) (vget e.ms.streams 1)) 0 (by omega)]
  simp

theorem guard_slot_38 (h : GuardTable) (e : Env) :
    guardV e 38 = Metronome.Glue.guardAt 38 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bv_two_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_two (streamEnd (vget e.cv.streams 0) (vget e.ms.streams 0))
    (streamEnd (vget e.cv.streams 1) (vget e.ms.streams 1)) 1 (by omega)]
  simp

theorem guard_slot_39 (h : GuardTable) (e : Env) :
    guardV e 39 = Metronome.Glue.guardAt 39 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bv_two_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_two (streamMark (vget e.cv.streams 0) (vget e.ms.streams 0))
    (streamMark (vget e.cv.streams 1) (vget e.ms.streams 1)) 0 (by omega)]
  simp

theorem guard_slot_40 (h : GuardTable) (e : Env) :
    guardV e 40 = Metronome.Glue.guardAt 40 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bv_two_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_two (streamMark (vget e.cv.streams 0) (vget e.ms.streams 0))
    (streamMark (vget e.cv.streams 1) (vget e.ms.streams 1)) 1 (by omega)]
  simp

theorem guard_slot_41 (h : GuardTable) (e : Env) :
    guardV e 41 = Metronome.Glue.guardAt 41 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bv_two_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_two (streamAtByte (vget e.ms.streams 0)) (streamAtByte (vget e.ms.streams 1)) 0
    (by omega)]
  simp

theorem guard_slot_42 (h : GuardTable) (e : Env) :
    guardV e 42 = Metronome.Glue.guardAt 42 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bv_two_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_two (streamAtByte (vget e.ms.streams 0)) (streamAtByte (vget e.ms.streams 1)) 1
    (by omega)]
  simp

theorem guard_slot_43 (h : GuardTable) (e : Env) :
    guardV e 43 = Metronome.Glue.guardAt 43 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bv_two_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_two (streamBit (vget e.cv.streams 0) 0 e.ms.dbg (vget e.ms.streams 0))
    (streamBit (vget e.cv.streams 1) 1 e.ms.dbg (vget e.ms.streams 1)) 0 (by omega)]
  simp

theorem guard_slot_44 (h : GuardTable) (e : Env) :
    guardV e 44 = Metronome.Glue.guardAt 44 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bv_two_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_two (streamBit (vget e.cv.streams 0) 0 e.ms.dbg (vget e.ms.streams 0))
    (streamBit (vget e.cv.streams 1) 1 e.ms.dbg (vget e.ms.streams 1)) 1 (by omega)]
  simp

theorem guard_slot_45 (h : GuardTable) (e : Env) :
    guardV e 45 = Metronome.Glue.guardAt 45 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bv,
    bit_eq_nbit, Nat.reducePow, Nat.shiftRight_eq_div_pow, Nat.div_one]
  simp [Metronome.Machine.PinView.pin, Tables.N_IN_PINS, Nat.mod_eq_of_lt (by simpa using e.hlvl)]

theorem guard_slot_46 (h : GuardTable) (e : Env) :
    guardV e 46 = Metronome.Glue.guardAt 46 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bv,
    bit_eq_nbit, Nat.reducePow, Nat.shiftRight_eq_div_pow]
  simp [Metronome.Machine.PinView.pin, Tables.N_IN_PINS, Nat.mod_eq_of_lt (by simpa using e.hlvl)]

theorem guard_slot_47 (h : GuardTable) (e : Env) :
    guardV e 47 = Metronome.Glue.guardAt 47 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bv,
    bit_eq_nbit, Nat.reducePow, Nat.shiftRight_eq_div_pow]
  simp [Metronome.Machine.PinView.pin, Tables.N_IN_PINS, Nat.mod_eq_of_lt (by simpa using e.hlvl)]

theorem guard_slot_48 (h : GuardTable) (e : Env) :
    guardV e 48 = Metronome.Glue.guardAt 48 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bv,
    bit_eq_nbit, Nat.reducePow, Nat.shiftRight_eq_div_pow]
  simp [Metronome.Machine.PinView.pin, Tables.N_IN_PINS, Nat.mod_eq_of_lt (by simpa using e.hlvl)]

theorem guard_slot_49 (h : GuardTable) (e : Env) :
    guardV e 49 = Metronome.Glue.guardAt 49 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bv,
    bit_eq_nbit, Nat.reducePow, Nat.shiftRight_eq_div_pow]
  simp [Metronome.Machine.PinView.pin, Tables.N_IN_PINS, Nat.mod_eq_of_lt (by simpa using e.hlvl)]

theorem guard_slot_50 (h : GuardTable) (e : Env) :
    guardV e 50 = Metronome.Glue.guardAt 50 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bv,
    bit_eq_nbit, Nat.reducePow, Nat.shiftRight_eq_div_pow]
  simp [Metronome.Machine.PinView.pin, Tables.N_IN_PINS, Nat.mod_eq_of_lt (by simpa using e.hlvl)]

theorem guard_slot_51 (h : GuardTable) (e : Env) :
    guardV e 51 = Metronome.Glue.guardAt 51 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bv,
    bit_eq_nbit, Nat.reducePow, Nat.shiftRight_eq_div_pow]
  simp [Metronome.Machine.PinView.pin, Tables.N_IN_PINS, Nat.mod_eq_of_lt (by simpa using e.hlvl)]

theorem guard_slot_52 (h : GuardTable) (e : Env) :
    guardV e 52 = Metronome.Glue.guardAt 52 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bv,
    bit_eq_nbit, Nat.reducePow, Nat.shiftRight_eq_div_pow]
  simp [Metronome.Machine.PinView.pin, Tables.N_IN_PINS, Nat.mod_eq_of_lt (by simpa using e.hlvl)]

theorem guard_slot_53 (h : GuardTable) (e : Env) :
    guardV e 53 = Metronome.Glue.guardAt 53 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bv,
    bit_eq_nbit, Nat.reducePow, Nat.shiftRight_eq_div_pow]
  simp [Metronome.Machine.PinView.pin, Tables.N_IN_PINS, Nat.mod_eq_of_lt (by simpa using e.hlvl)]

theorem guard_slot_54 (h : GuardTable) (e : Env) :
    guardV e 54 = Metronome.Glue.guardAt 54 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bv,
    bit_eq_nbit, Nat.reducePow, Nat.shiftRight_eq_div_pow]
  simp [Metronome.Machine.PinView.pin, Tables.N_IN_PINS, Nat.mod_eq_of_lt (by simpa using e.hlvl)]

theorem guard_slot_55 (h : GuardTable) (e : Env) :
    guardV e 55 = Metronome.Glue.guardAt 55 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bv,
    bit_eq_nbit, Nat.reducePow, Nat.shiftRight_eq_div_pow]
  simp [Metronome.Machine.PinView.pin, Tables.N_IN_PINS, Nat.mod_eq_of_lt (by simpa using e.hlvl)]

theorem guard_slot_56 (h : GuardTable) (e : Env) :
    guardV e 56 = Metronome.Glue.guardAt 56 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bv,
    bit_eq_nbit, Nat.reducePow, Nat.shiftRight_eq_div_pow]
  simp [Metronome.Machine.PinView.pin, Tables.N_IN_PINS, Nat.mod_eq_of_lt (by simpa using e.hlvl)]

theorem guard_slot_57 (h : GuardTable) (e : Env) :
    guardV e 57 = Metronome.Glue.guardAt 57 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit, bv,
    bit_eq_nbit, Nat.reducePow, Nat.shiftRight_eq_div_pow]
  simp [Metronome.Machine.PinView.pin, Tables.N_IN_PINS, Nat.mod_eq_of_lt (by simpa using e.hlvl)]

theorem guard_slot_58 (h : GuardTable) (e : Env) :
    guardV e 58 = Metronome.Glue.guardAt 58 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bv_four_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_four ((vget e.ms.lines 0).run) ((vget e.ms.lines 1).run)
    ((vget e.ms.lines 2).run) ((vget e.ms.lines 3).run) 0 (by omega)]
  simp

theorem guard_slot_59 (h : GuardTable) (e : Env) :
    guardV e 59 = Metronome.Glue.guardAt 59 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bv_four_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_four ((vget e.ms.lines 0).run) ((vget e.ms.lines 1).run)
    ((vget e.ms.lines 2).run) ((vget e.ms.lines 3).run) 1 (by omega)]
  simp

theorem guard_slot_60 (h : GuardTable) (e : Env) :
    guardV e 60 = Metronome.Glue.guardAt 60 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bv_four_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_four ((vget e.ms.lines 0).run) ((vget e.ms.lines 1).run)
    ((vget e.ms.lines 2).run) ((vget e.ms.lines 3).run) 2 (by omega)]
  simp

theorem guard_slot_61 (h : GuardTable) (e : Env) :
    guardV e 61 = Metronome.Glue.guardAt 61 (guardsOf e) := by
  rw [guardV, h.eq]
  simp only [guardOpOf, Metronome.Glue.guardAt, guardsOf, guardVal, bitAt_eq_nbit,
    bv_four_toNat, b2n_nbit, Nat.reducePow]
  rw [bit_four ((vget e.ms.lines 0).run) ((vget e.ms.lines 1).run)
    ((vget e.ms.lines 2).run) ((vget e.ms.lines 3).run) 3 (by omega)]
  simp

theorem guard_slot_62 (h : GuardTable) (e : Env) :
    guardV e 62 = Metronome.Glue.guardAt 62 (guardsOf e) := by
  rw [guardV, h.eq]; rfl

theorem guard_slot_63 (h : GuardTable) (e : Env) :
    guardV e 63 = Metronome.Glue.guardAt 63 (guardsOf e) := by
  rw [guardV, h.eq]; rfl

/-! ## Line-relative guard bundle `g_line` (SPEC_V2 §7, item 4N)

The cut's global guard vector leaves indices 27..31 false (`guardAt_lineRelative`);
the chip top instead hands each core the five-bit bundle `Glue.lineGuard l` of its
reading line.  This section proves the machine's `guardVal` of those five ports,
evaluated on line `l`, is that bundle's bit `j`.

The bit extraction is base-4 (`lineGuardsOf.inn`: two input-symbol bits per line,
`lineGuardsOf.sp`/`pinA`/`pinB`: one bit per line), so the lemmas below describe
one two-bit field inside a packed natural number. -/

/-- The reading line's input symbol `IN = {LUT1[{REM, SN}], LUT0[{REM, SN}]}`. -/
def symOf (e : Env) (l : Nat) : Nat := inSym (vget e.cv.lines l) (vget e.ms.lines l)

theorem symOf_lt (e : Env) (l : Nat) : symOf e l < 4 := by
  have h1 : b2n (nbit (vget e.cv.lines l).lut1
      (b2n (vget e.ms.lines l).rem * 16 + (vget e.ms.lines l).sn.toNat)) ≤ 1 := by
    have h := b2n_lt (nbit (vget e.cv.lines l).lut1
      (b2n (vget e.ms.lines l).rem * 16 + (vget e.ms.lines l).sn.toNat))
    omega
  have h2 : b2n (nbit (vget e.cv.lines l).lut0
      (b2n (vget e.ms.lines l).rem * 16 + (vget e.ms.lines l).sn.toNat)) ≤ 1 := by
    have h := b2n_lt (nbit (vget e.cv.lines l).lut0
      (b2n (vget e.ms.lines l).rem * 16 + (vget e.ms.lines l).sn.toNat))
    omega
  show b2n (nbit (vget e.cv.lines l).lut1
      (b2n (vget e.ms.lines l).rem * 16 + (vget e.ms.lines l).sn.toNat)) * 2 +
    b2n (nbit (vget e.cv.lines l).lut0
      (b2n (vget e.ms.lines l).rem * 16 + (vget e.ms.lines l).sn.toNat)) < 4
  omega

/-- Bits 0 and 1 of `a + 4 * b` are the bits of `a` (for `a < 4`). -/
theorem nbit_quad_low (a b i : Nat) (hi : i < 2) :
    nbit (a + 4 * b) i = nbit a i := by
  unfold nbit
  have h4 : a + 4 * b = a + b * 2 * 2 := by omega
  rw [h4]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · rw [Nat.shiftRight_zero, Nat.shiftRight_zero, Nat.add_mul_mod_self_right]
  · rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_one,
      Nat.add_mul_div_right a (b * 2) (by decide : 0 < 2), Nat.add_mul_mod_self_right]

/-- Bits `2 + i` of `R + 4 * M` are the bits `i` of `M` (for `R < 4`). -/
theorem nbit_quad_shift (R M i : Nat) (hR : R < 4) :
    nbit (R + 4 * M) (2 + i) = nbit M i := by
  unfold nbit
  have h4 : R + 4 * M = R + M * 4 := by omega
  rw [h4, Nat.shiftRight_add]
  have hdiv : (R + M * 4) >>> 2 = M := by
    rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 2 = 4 from rfl,
      Nat.add_mul_div_right R M (by decide : 0 < 4), Nat.div_eq_of_lt hR, Nat.zero_add]
  rw [hdiv]

/-- The cut's packed two-bit-per-line `inn` byte, unpacked: bit `2 * l + j` is the
machine's `IN` bit `j` of line `l`. -/
theorem inn_bit (e : Env) (l : Nat) (hl : l < 4) (j : Nat) (hj : j < 2) :
    Metronome.Glue.bitAt (lineGuardsOf e).inn (2 * l + j) = nbit (symOf e l) j := by
  have hN : (lineGuardsOf e).inn =
      bv 8 (symOf e 3 * 64 + symOf e 2 * 16 + symOf e 1 * 4 + symOf e 0) := rfl
  rw [hN, bitAt_eq_nbit]
  have hlt : symOf e 3 * 64 + symOf e 2 * 16 + symOf e 1 * 4 + symOf e 0 < 256 := by
    have h0 := symOf_lt e 0
    have h1 := symOf_lt e 1
    have h2 := symOf_lt e 2
    have h3 := symOf_lt e 3
    omega
  rw [show (bv 8 (symOf e 3 * 64 + symOf e 2 * 16 + symOf e 1 * 4 + symOf e 0)).toNat =
      symOf e 3 * 64 + symOf e 2 * 16 + symOf e 1 * 4 + symOf e 0 from by
    simp only [bv, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hlt]
  have hdec : symOf e 3 * 64 + symOf e 2 * 16 + symOf e 1 * 4 + symOf e 0 =
      symOf e 0 + 4 * (symOf e 1 + 4 * (symOf e 2 + 4 * symOf e 3)) := by omega
  rw [hdec]
  have h0 := symOf_lt e 0
  have h1 := symOf_lt e 1
  have h2 := symOf_lt e 2
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  · rw [show 2 * 0 + j = j from by omega, nbit_quad_low _ _ j hj]
  · rw [show 2 * 1 + j = 2 + j from by omega, nbit_quad_shift _ _ _ h0,
      nbit_quad_low _ _ j hj]
  · rw [show 2 * 2 + j = 2 + (2 + j) from by omega, nbit_quad_shift _ _ _ h0,
      nbit_quad_shift _ _ _ h1, nbit_quad_low _ _ j hj]
  · rw [show 2 * 3 + j = 2 + (2 + (2 + j)) from by omega, nbit_quad_shift _ _ _ h0,
      nbit_quad_shift _ _ _ h1, nbit_quad_shift _ _ _ h2]

/-- Bit `l` of the packed one-bit-per-line `SP` bus. -/
theorem sp_bit (e : Env) (l : Nat) (hl : l < 4) :
    Metronome.Glue.bitAt (lineGuardsOf e).sp l = (vget e.ms.lines l).sp := by
  have hN : (lineGuardsOf e).sp = bv 4 (b2n (vget e.ms.lines 3).sp * 8 +
      b2n (vget e.ms.lines 2).sp * 4 + b2n (vget e.ms.lines 1).sp * 2 +
      b2n (vget e.ms.lines 0).sp) := rfl
  rw [hN, bitAt_eq_nbit]
  rw [show (bv 4 (b2n (vget e.ms.lines 3).sp * 8 + b2n (vget e.ms.lines 2).sp * 4 +
      b2n (vget e.ms.lines 1).sp * 2 + b2n (vget e.ms.lines 0).sp)).toNat =
      b2n (vget e.ms.lines 3).sp * 8 + b2n (vget e.ms.lines 2).sp * 4 +
      b2n (vget e.ms.lines 1).sp * 2 + b2n (vget e.ms.lines 0).sp from by
    simp only [bv, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have h0 := b2n_lt (vget e.ms.lines 0).sp
    have h1 := b2n_lt (vget e.ms.lines 1).sp
    have h2 := b2n_lt (vget e.ms.lines 2).sp
    have h3 := b2n_lt (vget e.ms.lines 3).sp
    omega]
  rw [bit_four (vget e.ms.lines 0).sp (vget e.ms.lines 1).sp (vget e.ms.lines 2).sp
    (vget e.ms.lines 3).sp l hl]
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> simp

/-- Bit `l` of the packed `PINA` pin level, one bit per line. -/
theorem pinA_bit (e : Env) (l : Nat) (hl : l < 4) :
    Metronome.Glue.bitAt (lineGuardsOf e).pinA l = e.p.pin (vget e.cv.lines l).pina := by
  have hN : (lineGuardsOf e).pinA = bv 4 (b2n (e.p.pin (vget e.cv.lines 3).pina) * 8 +
      b2n (e.p.pin (vget e.cv.lines 2).pina) * 4 + b2n (e.p.pin (vget e.cv.lines 1).pina) * 2 +
      b2n (e.p.pin (vget e.cv.lines 0).pina)) := rfl
  rw [hN, bitAt_eq_nbit]
  rw [show (bv 4 (b2n (e.p.pin (vget e.cv.lines 3).pina) * 8 +
      b2n (e.p.pin (vget e.cv.lines 2).pina) * 4 +
      b2n (e.p.pin (vget e.cv.lines 1).pina) * 2 +
      b2n (e.p.pin (vget e.cv.lines 0).pina))).toNat =
      b2n (e.p.pin (vget e.cv.lines 3).pina) * 8 +
      b2n (e.p.pin (vget e.cv.lines 2).pina) * 4 +
      b2n (e.p.pin (vget e.cv.lines 1).pina) * 2 +
      b2n (e.p.pin (vget e.cv.lines 0).pina) from by
    simp only [bv, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have h0 := b2n_lt (e.p.pin (vget e.cv.lines 0).pina)
    have h1 := b2n_lt (e.p.pin (vget e.cv.lines 1).pina)
    have h2 := b2n_lt (e.p.pin (vget e.cv.lines 2).pina)
    have h3 := b2n_lt (e.p.pin (vget e.cv.lines 3).pina)
    omega]
  rw [bit_four (e.p.pin (vget e.cv.lines 0).pina) (e.p.pin (vget e.cv.lines 1).pina)
    (e.p.pin (vget e.cv.lines 2).pina) (e.p.pin (vget e.cv.lines 3).pina) l hl]
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> simp

/-- Bit `l` of the packed `PINB` pin level, one bit per line. -/
theorem pinB_bit (e : Env) (l : Nat) (hl : l < 4) :
    Metronome.Glue.bitAt (lineGuardsOf e).pinB l = e.p.pin (vget e.cv.lines l).pinb := by
  have hN : (lineGuardsOf e).pinB = bv 4 (b2n (e.p.pin (vget e.cv.lines 3).pinb) * 8 +
      b2n (e.p.pin (vget e.cv.lines 2).pinb) * 4 + b2n (e.p.pin (vget e.cv.lines 1).pinb) * 2 +
      b2n (e.p.pin (vget e.cv.lines 0).pinb)) := rfl
  rw [hN, bitAt_eq_nbit]
  rw [show (bv 4 (b2n (e.p.pin (vget e.cv.lines 3).pinb) * 8 +
      b2n (e.p.pin (vget e.cv.lines 2).pinb) * 4 +
      b2n (e.p.pin (vget e.cv.lines 1).pinb) * 2 +
      b2n (e.p.pin (vget e.cv.lines 0).pinb))).toNat =
      b2n (e.p.pin (vget e.cv.lines 3).pinb) * 8 +
      b2n (e.p.pin (vget e.cv.lines 2).pinb) * 4 +
      b2n (e.p.pin (vget e.cv.lines 1).pinb) * 2 +
      b2n (e.p.pin (vget e.cv.lines 0).pinb) from by
    simp only [bv, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have h0 := b2n_lt (e.p.pin (vget e.cv.lines 0).pinb)
    have h1 := b2n_lt (e.p.pin (vget e.cv.lines 1).pinb)
    have h2 := b2n_lt (e.p.pin (vget e.cv.lines 2).pinb)
    have h3 := b2n_lt (e.p.pin (vget e.cv.lines 3).pinb)
    omega]
  rw [bit_four (e.p.pin (vget e.cv.lines 0).pinb) (e.p.pin (vget e.cv.lines 1).pinb)
    (e.p.pin (vget e.cv.lines 2).pinb) (e.p.pin (vget e.cv.lines 3).pinb) l hl]
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> simp

/-- `g_line` bit 0: `L.IN0` on the reading line. -/
theorem line_guard_0 (h : GuardTable) (e : Env) (hl : e.l < 4) :
    guardV e 27 = Metronome.Glue.bitAt (Metronome.Glue.lineGuard e.l (lineGuardsOf e)) 0 := by
  rw [guardV, h.eq]
  simp only [guardOpOf, guardVal]
  rw [show Metronome.Glue.bitAt (Metronome.Glue.lineGuard e.l (lineGuardsOf e)) 0 =
      Metronome.Glue.bitAt (lineGuardsOf e).inn (2 * e.l) from
    (Metronome.Glue.lineGuard_at e.l (lineGuardsOf e)).1,
    show Metronome.Glue.bitAt (lineGuardsOf e).inn (2 * e.l) =
      nbit (symOf e e.l) 0 from inn_bit e e.l hl 0 (by omega)]
  rfl

/-- `g_line` bit 1: `L.IN1` on the reading line. -/
theorem line_guard_1 (h : GuardTable) (e : Env) (hl : e.l < 4) :
    guardV e 28 = Metronome.Glue.bitAt (Metronome.Glue.lineGuard e.l (lineGuardsOf e)) 1 := by
  rw [guardV, h.eq]
  simp only [guardOpOf, guardVal]
  rw [show Metronome.Glue.bitAt (Metronome.Glue.lineGuard e.l (lineGuardsOf e)) 1 =
      Metronome.Glue.bitAt (lineGuardsOf e).inn (2 * e.l + 1) from
    (Metronome.Glue.lineGuard_at e.l (lineGuardsOf e)).2.1,
    show Metronome.Glue.bitAt (lineGuardsOf e).inn (2 * e.l + 1) =
      nbit (symOf e e.l) 1 from inn_bit e e.l hl 1 (by omega)]
  rfl

/-- `g_line` bit 2: `L.SYNC` on the reading line. -/
theorem line_guard_2 (h : GuardTable) (e : Env) (hl : e.l < 4) :
    guardV e 29 = Metronome.Glue.bitAt (Metronome.Glue.lineGuard e.l (lineGuardsOf e)) 2 := by
  rw [guardV, h.eq]
  simp only [guardOpOf, guardVal]
  rw [show Metronome.Glue.bitAt (Metronome.Glue.lineGuard e.l (lineGuardsOf e)) 2 =
      Metronome.Glue.bitAt (lineGuardsOf e).sp e.l from
    (Metronome.Glue.lineGuard_at e.l (lineGuardsOf e)).2.2.1,
    show Metronome.Glue.bitAt (lineGuardsOf e).sp e.l = (vget e.ms.lines e.l).sp from
      sp_bit e e.l hl]

/-- `g_line` bit 3: `L.PINA` on the reading line. -/
theorem line_guard_3 (h : GuardTable) (e : Env) (hl : e.l < 4) :
    guardV e 30 = Metronome.Glue.bitAt (Metronome.Glue.lineGuard e.l (lineGuardsOf e)) 3 := by
  rw [guardV, h.eq]
  simp only [guardOpOf, guardVal]
  rw [show Metronome.Glue.bitAt (Metronome.Glue.lineGuard e.l (lineGuardsOf e)) 3 =
      Metronome.Glue.bitAt (lineGuardsOf e).pinA e.l from
    (Metronome.Glue.lineGuard_at e.l (lineGuardsOf e)).2.2.2.1,
    show Metronome.Glue.bitAt (lineGuardsOf e).pinA e.l = e.p.pin (vget e.cv.lines e.l).pina from
      pinA_bit e e.l hl]

/-- `g_line` bit 4: `L.PINB` on the reading line. -/
theorem line_guard_4 (h : GuardTable) (e : Env) (hl : e.l < 4) :
    guardV e 31 = Metronome.Glue.bitAt (Metronome.Glue.lineGuard e.l (lineGuardsOf e)) 4 := by
  rw [guardV, h.eq]
  simp only [guardOpOf, guardVal]
  rw [show Metronome.Glue.bitAt (Metronome.Glue.lineGuard e.l (lineGuardsOf e)) 4 =
      Metronome.Glue.bitAt (lineGuardsOf e).pinB e.l from
    (Metronome.Glue.lineGuard_at e.l (lineGuardsOf e)).2.2.2.2,
    show Metronome.Glue.bitAt (lineGuardsOf e).pinB e.l = e.p.pin (vget e.cv.lines e.l).pinb from
      pinB_bit e e.l hl]

/-- **Line-relative guard bundle.**  The machine's five line-relative guards on the
reading line `Env.l` (guard indices 27..31) are the bits of the cut's `g_line` bundle. -/
theorem lineGuard_bridge (h : GuardTable) (e : Env) (hl : e.l < 4) (j : Nat) (hj : j < 5) :
    guardV e (27 + j) =
      Metronome.Glue.bitAt (Metronome.Glue.lineGuard e.l (lineGuardsOf e)) j := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl
  · exact line_guard_0 h e hl
  · exact line_guard_1 h e hl
  · exact line_guard_2 h e hl
  · exact line_guard_3 h e hl
  · exact line_guard_4 h e hl

/-! ## Control registers, flags and mailbox (SPEC_V2 §6.1, §9, §12.3, item 4N)

The cut's `Glue.step` fields against `Machine.ctrlNext` (§9, §6.1, 9a.5) and
`Machine.unitsNext`'s flag pair (§6.1, §12.3).

The interface hypotheses are: each of the five `CTRL` host-write bytes the cut decodes
(`RUN`, `IRQEN`, `DOORBELL`, `HOSTIN`, `HOSTSTAT`) is the machine's `hwByte` of that
register, present exactly when the cut's strobe is high (`CtrlWr`); the `ERR` terms the
cut binds as leaves are the machine's sticky errors, thread `LATE`/`OVR`, line
`TAPMISS` and stream `STARVED` (`ErrTerms`); and the cut's registers currently hold the
machine's values (`CtrlRegs`). -/

/-- The cut's bit extractor is the machine's `nbit`. -/
theorem bitAt_eq_nbit' {w : Nat} (x : BitVec w) (i : Nat) :
    Metronome.Glue.bitAt x i = nbit x.toNat i := bitAt_eq_nbit x i

/-- `bit` of a vector is its `nbit`. -/
theorem bit_eq_nbit' {w : Nat} (x : BitVec w) (i : Nat) : bit x i = nbit x.toNat i :=
  bit_eq_nbit x i

theorem nbit_eq_testBit (x i : Nat) : nbit x i = x.testBit i := by
  rw [nbit, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rfl

theorem getLsbD_eq_testBit {w : Nat} (x : BitVec w) (i : Nat) :
    x.getLsbD i = x.toNat.testBit i := rfl

theorem bitAt_eq_getLsbD {w : Nat} (x : BitVec w) (i : Nat) :
    Metronome.Glue.bitAt x i = x.getLsbD i := by
  rw [bitAt_eq_nbit, nbit_eq_testBit]
  rfl

/-- `bv n x.toNat` is the cut's low-`n` slice of `x`. -/
theorem bv_toNat_slice {w : Nat} (x : BitVec w) (n : Nat) :
    bv n x.toNat = Metronome.Glue.slice x 0 n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show bv n x.toNat = BitVec.ofNat n x.toNat from rfl, BitVec.getLsbD_ofNat,
    show decide (i < n) = true from by simp [hi], Bool.true_and]
  rw [getLsbD_eq_testBit, slice_toNat, nbits, Nat.shiftRight_zero, Nat.testBit_mod_two_pow,
    show decide (i < n) = true from by simp [hi], Bool.true_and]

/-! ### The single flag bit: `Util.setBit` is the cut's `setFlag` -/

theorem testBit_succ_of_even (A k : Nat) (hA : A % 2 = 0) (hk : 0 < k) :
    (A + 1).testBit k = A.testBit k := by
  obtain ⟨m, rfl⟩ : ∃ m, A = 2 * m := by
    exact ⟨A / 2, by
      have := Nat.div_add_mod A 2
      omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.testBit_add_one, Nat.testBit_add_one,
    Nat.mul_add_div (by decide : 0 < 2), Nat.div_eq_of_lt (by decide : 1 < 2), Nat.add_zero,
    Nat.mul_comm 2 m, Nat.mul_div_cancel _ (by decide : 0 < 2)]

/-- Setting the `i`-th bit of `x` when it is clear: the `i`-th bit becomes 1 and every
other bit is unchanged. -/
theorem testBit_add_two_pow {x i j : Nat}
    (hxi : x.testBit i = false) :
    (x + 2 ^ i).testBit j = (if j = i then true else x.testBit j) := by
  have hB : x % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
  have hdecomp : x = 2 ^ i * (x / 2 ^ i) + x % 2 ^ i := by
    exact (Nat.div_add_mod x (2 ^ i)).symm
  have hxt : ∀ k : Nat, x.testBit k = (2 ^ i * (x / 2 ^ i) + x % 2 ^ i).testBit k := by
    intro k
    conv => lhs; rw [hdecomp]
  have hA : (x / 2 ^ i) % 2 = 0 := by
    have h1 : (x / 2 ^ i).testBit 0 = false := by
      rw [Nat.testBit_div_two_pow]
      simpa using hxi
    rw [Nat.testBit_zero] at h1
    have h2 : ¬ ((x / 2 ^ i) % 2 = 1) := by simpa using h1
    omega
  have hsum : x + 2 ^ i = 2 ^ i * (x / 2 ^ i + 1) + x % 2 ^ i := by
    conv => lhs; rw [hdecomp]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [hsum, Nat.testBit_two_pow_mul_add _ hB j]
  by_cases hj : j < i
  · rw [if_pos hj, if_neg (by omega : ¬ j = i), hxt j, Nat.testBit_two_pow_mul_add _ hB j,
      if_pos hj]
  · rw [if_neg hj]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, Nat.sub_self, Nat.testBit_zero]
      have h3 : (x / 2 ^ i + 1) % 2 = 1 := by omega
      simp [h3]
    · rw [if_neg hji, testBit_succ_of_even _ _ hA (by omega), hxt j,
        Nat.testBit_two_pow_mul_add _ hB j, if_neg (by omega : ¬ j < i)]

/-- Clearing the `i`-th bit of `x` when it is set. -/
theorem testBit_sub_two_pow {x i j n : Nat} (hx : x < 2 ^ n) (hi : i < n)
    (hxi : x.testBit i = true) :
    (x - 2 ^ i).testBit j = (if j = i then false else x.testBit j) := by
  have hge : 2 ^ i ≤ x := Nat.ge_two_pow_of_testBit hxi
  have hxy : x - 2 ^ i + 2 ^ i = x := Nat.sub_add_cancel hge
  have hsub : x - 2 ^ i < 2 ^ n := Nat.lt_of_le_of_lt (Nat.sub_le x (2 ^ i)) hx
  have hyi : (x - 2 ^ i).testBit i = false := by
    have h := Nat.testBit_two_pow_add_eq (x - 2 ^ i) i
    rw [Nat.add_comm, hxy, hxi] at h
    simpa using h.symm
  have hA := testBit_add_two_pow (x := x - 2 ^ i) (i := i) (j := j) hyi
  rw [hxy] at hA
  by_cases hj : j = i
  · subst hj
    rw [hyi, if_pos rfl]
  · rw [if_neg hj]
    have hres : x.testBit j = (x - 2 ^ i).testBit j := by
      rw [hA, if_neg hj]
    rw [hres]

/-- The machine's `setBit` writes exactly one bit of the sixteen flags. -/
theorem setBit_getLsbD {n : Nat} (x : BitVec n) (i j : Nat) (v : Bool)
    (hi : i < n) (hj : j < n) :
    (setBit x i v).getLsbD j = (if j = i then v else x.getLsbD j) := by
  have hlt : x.toNat < 2 ^ n := x.isLt
  unfold setBit bv
  rw [BitVec.getLsbD_ofNat]
  simp only [show decide (j < n) = true from by simp [hj], Bool.true_and]
  rw [getLsbD_eq_testBit]
  by_cases hb : bit x i
  · rw [if_pos hb]
    have hb' : x.toNat.testBit i = true := hb
    have hge : 2 ^ i ≤ x.toNat := Nat.ge_two_pow_of_testBit hb'
    by_cases hv : v
    · rw [if_pos hv, hv, show x.toNat - 2 ^ i + 2 ^ i = x.toNat from Nat.sub_add_cancel hge]
      by_cases hj' : j = i
      · rw [if_pos hj', hj', hb']
      · rw [if_neg hj']
    · have hv' : v = false := by
        cases v with
        | false => rfl
        | true => exact absurd rfl hv
      rw [if_neg hv, hv', Nat.add_zero, testBit_sub_two_pow hlt hi hb']
  · rw [if_neg hb, Nat.sub_zero]
    have hbfalse : bit x i = false := by
      cases h : bit x i with
      | false => rfl
      | true => exact absurd h hb
    have hb' : x.toNat.testBit i = false := hbfalse
    by_cases hv : v
    · rw [if_pos hv, hv, testBit_add_two_pow hb']
    · have hv' : v = false := by
        cases v with
        | false => rfl
        | true => exact absurd rfl hv
      rw [if_neg hv, hv', Nat.add_zero]
      by_cases hj' : j = i
      · rw [if_pos hj', hj', hb']
      · rw [if_neg hj']

/-- The cut's `setFlag` writes exactly one bit of the sixteen flags. -/
theorem setFlag_getLsbD (f : BitVec 16) (k : Nat) (v : Bool) (j : Nat)
    (hk : k < 16) (hj : j < 16) :
    (Metronome.Glue.setFlag f (bv 4 k) v).getLsbD j =
      (if j = k then v else f.getLsbD j) := by
  have hidx : (bv 4 k).toNat = k := by
    simp only [bv]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbit : (BitVec.shiftLeft (1 : BitVec 16) k).getLsbD j = decide (k = j) := by
    show (BitVec.twoPow 16 k).getLsbD j = decide (k = j)
    rw [BitVec.getLsbD_twoPow]
    simp [hk]
  have htrue : ∀ h : k = j, decide (k = j) = true := fun h => by simp [h]
  have hfalse : ∀ h : ¬ k = j, decide (k = j) = false := fun h => by
    rw [decide_eq_false_iff_not]; exact h
  simp only [Metronome.Glue.setFlag, hidx]
  by_cases hv : v
  · rw [if_pos hv, BitVec.getLsbD_or, hbit]
    by_cases hjk : j = k
    · rw [if_pos hjk, htrue hjk.symm, Bool.or_true, hv]
    · rw [if_neg hjk, hfalse (fun h => hjk h.symm), Bool.or_false]
  · have hv' : v = false := by
      cases v with
      | false => rfl
      | true => exact absurd rfl hv
    rw [if_neg hv, BitVec.getLsbD_and, BitVec.getLsbD_not, hbit]
    simp only [show decide (j < 16) = true from by simp [hj], Bool.true_and]
    by_cases hjk : j = k
    · rw [if_pos hjk, htrue hjk.symm, Bool.not_true, Bool.and_false, hv']
    · rw [if_neg hjk, hfalse (fun h => hjk h.symm), Bool.not_false, Bool.and_true]

/-- **Flags.**  The machine's `setBit` flag write is the cut's `setFlag` write. -/
theorem setBit_eq_setFlag (f : BitVec 16) (i : Nat) (v : Bool) (hi : i < 16) :
    setBit f i v = Metronome.Glue.setFlag f (bv 4 i) v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [setBit_getLsbD f i j v hi hj, setFlag_getLsbD f i v j hi hj]

/-! ### The abstraction map for the control registers -/

/-- The machine's control-register inputs from the cut's `GlueInput`. -/
def ctrlInOf (i : Metronome.Glue.GlueInput) : CtrlIn where
  hostOut := if Metronome.Glue.hostOutWrite i then some (Metronome.Glue.hostOutData i).toNat else none
  hostInRead := Metronome.Glue.anyRead i.rdHin
  conflict := i.conflict
  memhaz := i.memhaz
  cwovr := i.cwOverrun

/-- The machine's flag-write input from the cut's `GlueInput`. -/
def unitsInOf (i : Metronome.Glue.GlueInput) : UnitsIn where
  flag := if Metronome.Glue.flagsWrite i then
    some (Metronome.Glue.flagsValue i, (Metronome.Glue.flagsIndex i).toNat) else none

/-- The machine state after one glue cycle's control and flag update. -/
def ctrlStep (hw : Option HostWr) (i : Metronome.Glue.GlueInput) (ms : Machine.State) :
    Machine.State :=
  { ms with
    ctrl := ctrlNext ms hw (ctrlInOf i) i.frz,
    units := unitsNext ms.cfg ms.units (unitsInOf i) i.frz }

/-- The five host-write bytes of the cut's `CTRL` strobes are the machine's. -/
structure CtrlWr (hw : Option HostWr) (i : Metronome.Glue.GlueInput) : Prop where
  run : hwByte hw "CTRL" 0 "RUN" = (if i.wrRun then some i.hWd.toNat else none)
  irqen : hwByte hw "CTRL" 0 "IRQEN" = (if i.wrIrqEn then some i.hWd.toNat else none)
  doorbell : hwByte hw "CTRL" 0 "DOORBELL" = (if i.wrDb then some i.hWd.toNat else none)
  hostin : hwByte hw "CTRL" 0 "HOSTIN" = (if i.wrHin then some i.hWd.toNat else none)
  hoststat : hwByte hw "CTRL" 0 "HOSTSTAT" = (if i.wrHst then some i.hWd.toNat else none)

/-- The cut's `ERR` leaves are the machine's §9 error terms. -/
structure ErrTerms (ms : Machine.State) (i : Metronome.Glue.GlueInput) : Prop where
  conflict : i.conflict = ms.ctrl.conflict
  memhaz : i.memhaz = ms.ctrl.memhaz
  cwovr : i.cwOverrun = ms.ctrl.cwovr
  tLate : Metronome.Glue.any6 i.tLate = ms.threads.toList.any (fun t => t.late)
  tOvr : Metronome.Glue.any6 i.tOvr = ms.threads.toList.any (fun t => t.ovr)
  lTap : Metronome.Glue.any4 i.lTapmiss = ms.lines.toList.any (fun l => l.tapmiss)
  sStarv : Metronome.Glue.any2 i.sStarved = ms.streams.toList.any (fun k => k.starved)

/-- The cut's glue registers hold the machine's control and flag registers. -/
structure CtrlRegs (ms : Machine.State) (s : Metronome.Glue.GlueState) : Prop where
  run : s.runG = ms.ctrl.run
  irqen : s.irqEn = ms.ctrl.irqen
  inb : s.inB = ms.ctrl.inb
  inv : s.inv = ms.ctrl.inv
  invp : s.invp = ms.ctrl.invp
  outb : s.outB = ms.ctrl.outb
  outv : s.outv = ms.ctrl.outv
  db : s.db = ms.ctrl.db
  irq : s.irq = ms.ctrl.irq
  fl : s.fl = ms.units.f
  flp : s.flp = ms.units.fp

/-- `l.any (fun x => f x || g x)` splits into the two reductions. -/
theorem list_any_or {α : Type} (l : List α) (f g : α → Bool) :
    l.any (fun x => f x || g x) = (l.any f || l.any g) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons, ih]
    cases f x <;> cases g x <;> simp

/-- The cut's `ERR` is the machine's `errAny`. -/
theorem err_bridge (ms : Machine.State) (i : Metronome.Glue.GlueInput) (h : ErrTerms ms i) :
    Metronome.Glue.err i = errAny ms := by
  obtain ⟨hc, hm, hw, hl, ho, ht, hs⟩ := h
  simp only [Metronome.Glue.err, errAny, hc, hm, hw, hl, ho, ht, hs, list_any_or,
    Bool.or_assoc]

/-- The mailbox output byte: the cut's `HOST.OUT` write is the machine's. -/
theorem ctrl_outb (hw : Option HostWr) (i : Metronome.Glue.GlueInput)
    (s : Metronome.Glue.GlueState) (ms : Machine.State) (h : CtrlRegs ms s)
    (reset : i.resetN = true) :
    (ctrlNext ms hw (ctrlInOf i) i.frz).outb = (Metronome.Glue.step s i).outB := by
  rw [Metronome.Glue.outB_next]
  simp only [ctrlNext, ctrlInOf, reset, if_true]
  by_cases hw' : Metronome.Glue.hostOutWrite i
  · simp [hw', bv_toNat]
  · simp [hw', h.outb]

theorem ctrl_outv (hw : Option HostWr) (i : Metronome.Glue.GlueInput)
    (s : Metronome.Glue.GlueState) (ms : Machine.State) (h : CtrlRegs ms s)
    (hb : CtrlWr hw i) (reset : i.resetN = true) :
    (ctrlNext ms hw (ctrlInOf i) i.frz).outv = (Metronome.Glue.step s i).outv := by
  rw [Metronome.Glue.outv_next]
  simp only [ctrlNext, ctrlInOf, reset, if_true]
  have hstat : nbit ((hwByte hw "CTRL" 0 "HOSTSTAT").getD 0) 1 =
      (i.wrHst && Metronome.Glue.bitAt i.hWd 1) := by
    rw [hb.hoststat]
    by_cases hh : i.wrHst
    · simp [hh, bitAt_eq_nbit]
    · simp [hh, nbit]
  by_cases hout : Metronome.Glue.hostOutWrite i
  · simp [hout]
  · simp [hout, hstat, Metronome.Glue.hostStatClear, h.outv]

theorem ctrl_run (hw : Option HostWr) (i : Metronome.Glue.GlueInput)
    (s : Metronome.Glue.GlueState) (ms : Machine.State) (h : CtrlRegs ms s)
    (hb : CtrlWr hw i) (reset : i.resetN = true) :
    (ctrlNext ms hw (ctrlInOf i) i.frz).run = (Metronome.Glue.step s i).runG := by
  rw [Metronome.Glue.runG_next]
  simp only [ctrlNext, reset, if_true]
  rw [hb.run]
  by_cases hw' : i.wrRun
  · simp [hw', bitAt_eq_nbit]
  · simp [hw', h.run]

theorem ctrl_irqen (hw : Option HostWr) (i : Metronome.Glue.GlueInput)
    (s : Metronome.Glue.GlueState) (ms : Machine.State) (h : CtrlRegs ms s)
    (hb : CtrlWr hw i) (reset : i.resetN = true) :
    (ctrlNext ms hw (ctrlInOf i) i.frz).irqen = (Metronome.Glue.step s i).irqEn := by
  rw [Metronome.Glue.irqEn_next]
  simp only [ctrlNext, reset, if_true]
  rw [hb.irqen]
  by_cases hw' : i.wrIrqEn
  · simp only [hw', if_true]
    exact bv_toNat_slice i.hWd 2
  · simp [hw', h.irqen]

theorem ctrl_db (hw : Option HostWr) (i : Metronome.Glue.GlueInput)
    (s : Metronome.Glue.GlueState) (ms : Machine.State) (h : CtrlRegs ms s)
    (hb : CtrlWr hw i) (reset : i.resetN = true) :
    (ctrlNext ms hw (ctrlInOf i) i.frz).db = (Metronome.Glue.step s i).db := by
  rw [Metronome.Glue.db_next]
  simp only [ctrlNext, reset, if_true]
  rw [hb.doorbell]
  have hX : (if i.wrDb then Metronome.Glue.doorbellBits i else 0).toNat =
      ((if i.wrDb then some i.hWd.toNat else none).getD 0) % 64 := by
    by_cases hw' : i.wrDb
    · simp [hw', Metronome.Glue.doorbellBits, slice_toNat, nbits]
    · simp [hw']
  by_cases hf : i.frz
  · rw [if_pos hf, if_pos hf]
    have hmain : bv 6 (((if i.wrDb then some i.hWd.toNat else none).getD 0) % 64 |||
        ms.ctrl.db.toNat) =
        ((if i.wrDb then Metronome.Glue.doorbellBits i else 0) ||| s.db) := by
      rw [← bv_toNat ((if i.wrDb then Metronome.Glue.doorbellBits i else 0) ||| s.db),
        BitVec.toNat_or, h.db, hX]
    exact hmain
  · rw [if_neg hf, if_neg hf]
    have hmain : bv 6 (((if i.wrDb then some i.hWd.toNat else none).getD 0) % 64) =
        (if i.wrDb then Metronome.Glue.doorbellBits i else 0) := by
      rw [← bv_toNat (if i.wrDb then Metronome.Glue.doorbellBits i else 0), hX]
    simpa using hmain

theorem ctrl_inb (hw : Option HostWr) (i : Metronome.Glue.GlueInput)
    (s : Metronome.Glue.GlueState) (ms : Machine.State) (h : CtrlRegs ms s)
    (hb : CtrlWr hw i) (reset : i.resetN = true) :
    (ctrlNext ms hw (ctrlInOf i) i.frz).inb = (Metronome.Glue.step s i).inB := by
  rw [Metronome.Glue.inB_next]
  simp only [ctrlNext, reset, if_true]
  rw [hb.hostin]
  by_cases hw' : i.wrHin
  · simp only [hw', if_true, Option.some.injEq]
    exact bv_toNat i.hWd
  · simp [hw', h.inb]

theorem ctrl_inv (hw : Option HostWr) (i : Metronome.Glue.GlueInput)
    (s : Metronome.Glue.GlueState) (ms : Machine.State) (h : CtrlRegs ms s)
    (hb : CtrlWr hw i) (reset : i.resetN = true) :
    (ctrlNext ms hw (ctrlInOf i) i.frz).inv = (Metronome.Glue.step s i).inv := by
  rw [Metronome.Glue.inv_next]
  simp only [ctrlNext, ctrlInOf, reset, if_true]
  rw [hb.hostin]
  by_cases hw' : i.wrHin
  · simp [hw']
  · by_cases hr : Metronome.Glue.anyRead i.rdHin
    · simp [hw', hr]
    · simp [hw', hr, h.inv]

theorem ctrl_invp (hw : Option HostWr) (i : Metronome.Glue.GlueInput)
    (s : Metronome.Glue.GlueState) (ms : Machine.State) (h : CtrlRegs ms s)
    (reset : i.resetN = true) :
    (ctrlNext ms hw (ctrlInOf i) i.frz).invp = (Metronome.Glue.step s i).invp := by
  rw [Metronome.Glue.invp_next]
  simp only [ctrlNext, reset, if_true]
  by_cases hf : i.frz
  · simp [hf, h.invp]
  · simp [hf, h.inv]

theorem ctrl_irq (hw : Option HostWr) (i : Metronome.Glue.GlueInput)
    (s : Metronome.Glue.GlueState) (ms : Machine.State) (h : CtrlRegs ms s)
    (he : ErrTerms ms i) (reset : i.resetN = true) :
    (ctrlNext ms hw (ctrlInOf i) i.frz).irq = (Metronome.Glue.step s i).irq := by
  rw [Metronome.Glue.irq_next]
  simp only [ctrlNext, reset, if_true, irqNext, err_bridge ms i he]
  rw [← h.irqen, ← h.outv]
  simp only [bit_eq_nbit, bitAt_eq_nbit]

theorem flags_f (_hw : Option HostWr) (i : Metronome.Glue.GlueInput)
    (s : Metronome.Glue.GlueState) (ms : Machine.State) (h : CtrlRegs ms s)
    (reset : i.resetN = true) :
    (unitsNext ms.cfg ms.units (unitsInOf i) i.frz).f = (Metronome.Glue.step s i).fl := by
  rw [Metronome.Glue.fl_next]
  simp only [unitsNext, unitsInOf, reset, if_true]
  have hidx : (Metronome.Glue.flagsIndex i).toNat % 16 = (Metronome.Glue.flagsIndex i).toNat :=
    Nat.mod_eq_of_lt (by simpa using (Metronome.Glue.flagsIndex i).isLt)
  by_cases hw' : Metronome.Glue.flagsWrite i
  · simp only [hw', if_true]
    rw [hidx, h.fl,
      setBit_eq_setFlag _ _ _ (by simpa using (Metronome.Glue.flagsIndex i).isLt), bv_toNat]
  · simp [hw', h.fl]

theorem flags_fp (_hw : Option HostWr) (i : Metronome.Glue.GlueInput)
    (s : Metronome.Glue.GlueState) (ms : Machine.State) (h : CtrlRegs ms s)
    (reset : i.resetN = true) :
    (unitsNext ms.cfg ms.units (unitsInOf i) i.frz).fp = (Metronome.Glue.step s i).flp := by
  rw [Metronome.Glue.flp_next]
  simp only [unitsNext, unitsInOf, reset, if_true]
  by_cases hf : i.frz
  · simp [hf, h.flp]
  · simp [hf, h.fl]

/-- **Control, flags and mailbox.**  One cut glue cycle on the control registers is one
machine cycle on `ctrl` and the flags pair `f`/`fp`, field by field. -/
theorem ctrl_bridge (hw : Option HostWr) (i : Metronome.Glue.GlueInput)
    (s : Metronome.Glue.GlueState) (ms : Machine.State)
    (hb : CtrlWr hw i) (he : ErrTerms ms i) (h : CtrlRegs ms s) (reset : i.resetN = true) :
    CtrlRegs (ctrlStep hw i ms) (Metronome.Glue.step s i) :=
  { run := (ctrl_run hw i s ms h hb reset).symm
    irqen := (ctrl_irqen hw i s ms h hb reset).symm
    inb := (ctrl_inb hw i s ms h hb reset).symm
    inv := (ctrl_inv hw i s ms h hb reset).symm
    invp := (ctrl_invp hw i s ms h reset).symm
    outb := (ctrl_outb hw i s ms h reset).symm
    outv := (ctrl_outv hw i s ms h hb reset).symm
    db := (ctrl_db hw i s ms h hb reset).symm
    irq := (ctrl_irq hw i s ms h he reset).symm
    fl := (flags_f hw i s ms h reset).symm
    flp := (flags_fp hw i s ms h reset).symm }

/-! ## Output pins: the packed configuration bytes (SPEC_V2 §8, §12.1, item 4N)

The cut's `OutCfg` holds the output-pin configuration as packed bytes decoded with
`slice`/`bitAt` at a per-line offset.  These lemmas are the packing half of the
output-pin bridge: `bindPack`/`selPack`/`segPack`/`commPack` build those bytes from
the machine's decoded fields, and each lemma reads one field back out (base-4 and
base-16 extraction via `bv_decide`, no `native_decide`).

They are proved but not yet used: the `out_bridge` assembly that needs them is a
remaining gap (see `BRIDGE_GLUE_DEBUG_NOTES.md`, glue gaps). -/

/-- One config bit as a one-bit vector. -/
def bitVec1 (b : Bool) : BitVec 1 := if b then 1 else 0

/-- Four bits `{d, c, b, a}`, `d` in bit 3. -/
def pack4b (d c b a : Bool) : BitVec 4 :=
  (if d then 8 else 0) ||| ((if c then 4 else 0) ||| ((if b then 2 else 0) ||| (if a then 1 else 0)))

/-- The cut's `BIND` byte: bits 1:0 `LINE`, bit 2 `BOUND`, bit 3 `LIVE[0]`, bit 4 `LIVE[1]`. -/
def bindPack (line : BitVec 2) (bound live0 live1 : Bool) : BitVec 8 :=
  (0 : BitVec 3) ++ bitVec1 live1 ++ bitVec1 live0 ++ bitVec1 bound ++ line

/-- The cut's `SEL` byte: `SEL0` bits 1:0, `SEL1` 3:2, `SEL2` 5:4. -/
def selPack (s0 s1 s2 : BitVec 2) : BitVec 8 :=
  (0 : BitVec 2) ++ s2 ++ s1 ++ s0

/-- The cut's per-line `SEG`, two bits per line. -/
def segPack (s0 s1 s2 s3 : BitVec 2) : BitVec 8 := s3 ++ s2 ++ s1 ++ s0

/-- The cut's per-line `COMMITTED`, four bits per line. -/
def commPack (c0 c1 c2 c3 : BitVec 4) : BitVec 16 := c3 ++ c2 ++ c1 ++ c0

theorem bindPack_line (line : BitVec 2) (bd l0 l1 : Bool) :
    Metronome.Glue.slice (bindPack line bd l0 l1) 0 2 = line := by
  unfold bindPack Metronome.Glue.slice bitVec1; bv_decide

theorem bindPack_bound (line : BitVec 2) (bd l0 l1 : Bool) :
    Metronome.Glue.bitAt (bindPack line bd l0 l1) 2 = bd := by
  unfold bindPack Metronome.Glue.bitAt bitVec1; bv_decide

theorem bindPack_live0 (line : BitVec 2) (bd l0 l1 : Bool) :
    Metronome.Glue.bitAt (bindPack line bd l0 l1) 3 = l0 := by
  unfold bindPack Metronome.Glue.bitAt bitVec1; bv_decide

theorem bindPack_live1 (line : BitVec 2) (bd l0 l1 : Bool) :
    Metronome.Glue.bitAt (bindPack line bd l0 l1) 4 = l1 := by
  unfold bindPack Metronome.Glue.bitAt bitVec1; bv_decide

theorem selPack_0 (s0 s1 s2 : BitVec 2) :
    Metronome.Glue.slice (selPack s0 s1 s2) 0 2 = s0 := by
  unfold selPack Metronome.Glue.slice; bv_decide

theorem selPack_1 (s0 s1 s2 : BitVec 2) :
    Metronome.Glue.slice (selPack s0 s1 s2) 2 2 = s1 := by
  unfold selPack Metronome.Glue.slice; bv_decide

theorem selPack_2 (s0 s1 s2 : BitVec 2) :
    Metronome.Glue.slice (selPack s0 s1 s2) 4 2 = s2 := by
  unfold selPack Metronome.Glue.slice; bv_decide

theorem segPack_0 (s0 s1 s2 s3 : BitVec 2) :
    Metronome.Glue.slice (segPack s0 s1 s2 s3) 0 2 = s0 := by
  unfold segPack Metronome.Glue.slice; bv_decide

theorem segPack_1 (s0 s1 s2 s3 : BitVec 2) :
    Metronome.Glue.slice (segPack s0 s1 s2 s3) 2 2 = s1 := by
  unfold segPack Metronome.Glue.slice; bv_decide

theorem segPack_2 (s0 s1 s2 s3 : BitVec 2) :
    Metronome.Glue.slice (segPack s0 s1 s2 s3) 4 2 = s2 := by
  unfold segPack Metronome.Glue.slice; bv_decide

theorem segPack_3 (s0 s1 s2 s3 : BitVec 2) :
    Metronome.Glue.slice (segPack s0 s1 s2 s3) 6 2 = s3 := by
  unfold segPack Metronome.Glue.slice; bv_decide

theorem commPack_0 (c0 c1 c2 c3 : BitVec 4) :
    Metronome.Glue.slice (commPack c0 c1 c2 c3) 0 4 = c0 := by
  unfold commPack Metronome.Glue.slice; bv_decide

theorem commPack_1 (c0 c1 c2 c3 : BitVec 4) :
    Metronome.Glue.slice (commPack c0 c1 c2 c3) 4 4 = c1 := by
  unfold commPack Metronome.Glue.slice; bv_decide

theorem commPack_2 (c0 c1 c2 c3 : BitVec 4) :
    Metronome.Glue.slice (commPack c0 c1 c2 c3) 8 4 = c2 := by
  unfold commPack Metronome.Glue.slice; bv_decide

theorem commPack_3 (c0 c1 c2 c3 : BitVec 4) :
    Metronome.Glue.slice (commPack c0 c1 c2 c3) 12 4 = c3 := by
  unfold commPack Metronome.Glue.slice; bv_decide

theorem pack4b_0 (d c b a : Bool) : Metronome.Glue.bitAt (pack4b d c b a) 0 = a := by
  unfold pack4b Metronome.Glue.bitAt; bv_decide

theorem pack4b_1 (d c b a : Bool) : Metronome.Glue.bitAt (pack4b d c b a) 1 = b := by
  unfold pack4b Metronome.Glue.bitAt; bv_decide

theorem pack4b_2 (d c b a : Bool) : Metronome.Glue.bitAt (pack4b d c b a) 2 = c := by
  unfold pack4b Metronome.Glue.bitAt; bv_decide

theorem pack4b_3 (d c b a : Bool) : Metronome.Glue.bitAt (pack4b d c b a) 3 = d := by
  unfold pack4b Metronome.Glue.bitAt; bv_decide

/-- The machine's output-pin configuration of pin `o`. -/
def ocOf (e : Env) (o : Nat) : Machine.OutCfg := vget e.cv.outs o

/-- The cut's per-output configuration from the machine's decoded configuration and the
line state its table reads. -/
def outCfgOf (e : Env) (o : Nat) : Metronome.Glue.OutCfg :=
  { bind := bindPack (bv 2 (ocOf e o).line) (ocOf e o).bound (nbit (ocOf e o).live 0)
      (nbit (ocOf e o).live 1)
    sel := selPack (bv 2 (ocOf e o).sel0) (bv 2 (ocOf e o).sel1) (bv 2 (ocOf e o).sel2)
    lut := bv 32 (ocOf e o).lut
    oe := bv 32 (ocOf e o).oe
    comm := commPack (vget e.ms.lines 0).committed (vget e.ms.lines 1).committed
      (vget e.ms.lines 2).committed (vget e.ms.lines 3).committed
    pinA := pack4b (e.p.pin (vget e.cv.lines 3).pina) (e.p.pin (vget e.cv.lines 2).pina)
      (e.p.pin (vget e.cv.lines 1).pina) (e.p.pin (vget e.cv.lines 0).pina)
    pinB := pack4b (e.p.pin (vget e.cv.lines 3).pinb) (e.p.pin (vget e.cv.lines 2).pinb)
      (e.p.pin (vget e.cv.lines 1).pinb) (e.p.pin (vget e.cv.lines 0).pinb)
    seg := segPack (bv 2 (seg (vget e.ms.lines 0))) (bv 2 (seg (vget e.ms.lines 1)))
      (bv 2 (seg (vget e.ms.lines 2))) (bv 2 (seg (vget e.ms.lines 3))) }

/-- Range facts of the decoded configuration: `LINE`, `SEL0`, `SEL1` and `SEL2` are
two-bit fields, so they are below 4.  `Env.cv` is an arbitrary decoded `CfgView`, so
this is an interface hypothesis; it holds for every `Machine.cfgView c`, where each
field is `Machine.Util.nbits bytes 0 2`. -/
structure CvRange (e : Env) : Prop where
  line : ∀ o, (ocOf e o).line < 4
  sel0 : ∀ o, (ocOf e o).sel0 < 4
  sel1 : ∀ o, (ocOf e o).sel1 < 4
  sel2 : ∀ o, (ocOf e o).sel2 < 4

theorem seg_lt (st : LineSt) : seg st < 4 := by
  unfold seg; exact Nat.mod_lt _ (by decide : 0 < 4)

theorem outCfgOf_bind (e : Env) (o : Nat) :
    (outCfgOf e o).bind = bindPack (bv 2 (ocOf e o).line) (ocOf e o).bound
      (nbit (ocOf e o).live 0) (nbit (ocOf e o).live 1) := rfl

theorem outCfgOf_sel (e : Env) (o : Nat) :
    (outCfgOf e o).sel = selPack (bv 2 (ocOf e o).sel0) (bv 2 (ocOf e o).sel1)
      (bv 2 (ocOf e o).sel2) := rfl

theorem outCfgOf_lut (e : Env) (o : Nat) : (outCfgOf e o).lut = bv 32 (ocOf e o).lut := rfl

theorem outCfgOf_oe (e : Env) (o : Nat) : (outCfgOf e o).oe = bv 32 (ocOf e o).oe := rfl

theorem outCfgOf_comm (e : Env) (o : Nat) :
    (outCfgOf e o).comm = commPack (vget e.ms.lines 0).committed (vget e.ms.lines 1).committed
      (vget e.ms.lines 2).committed (vget e.ms.lines 3).committed := rfl

theorem outCfgOf_pinA (e : Env) (o : Nat) :
    (outCfgOf e o).pinA = pack4b (e.p.pin (vget e.cv.lines 3).pina)
      (e.p.pin (vget e.cv.lines 2).pina) (e.p.pin (vget e.cv.lines 1).pina)
      (e.p.pin (vget e.cv.lines 0).pina) := rfl

theorem outCfgOf_pinB (e : Env) (o : Nat) :
    (outCfgOf e o).pinB = pack4b (e.p.pin (vget e.cv.lines 3).pinb)
      (e.p.pin (vget e.cv.lines 2).pinb) (e.p.pin (vget e.cv.lines 1).pinb)
      (e.p.pin (vget e.cv.lines 0).pinb) := rfl

theorem outCfgOf_seg (e : Env) (o : Nat) :
    (outCfgOf e o).seg = segPack (bv 2 (seg (vget e.ms.lines 0)))
      (bv 2 (seg (vget e.ms.lines 1))) (bv 2 (seg (vget e.ms.lines 2)))
      (bv 2 (seg (vget e.ms.lines 3))) := rfl

/-- The cut's `BIND[1:0]` is the machine's `LINE`. -/
theorem out_line (e : Env) (o : Nat) (hr : CvRange e) :
    (Metronome.Glue.outLine (outCfgOf e o)).toNat = (ocOf e o).line := by
  show (Metronome.Glue.slice (outCfgOf e o).bind 0 2).toNat = (ocOf e o).line
  rw [outCfgOf_bind, bindPack_line, bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hr.line o)]

/-- `BIND` bit 2 is `BOUND`. -/
theorem out_bound (e : Env) (o : Nat) :
    Metronome.Glue.outBound (outCfgOf e o) = (ocOf e o).bound := by
  show Metronome.Glue.bitAt (outCfgOf e o).bind 2 = (ocOf e o).bound
  rw [outCfgOf_bind, bindPack_bound]

/-- `BIND` bit 3 is `LIVE[0]`. -/
theorem out_live0 (e : Env) (o : Nat) :
    Metronome.Glue.outLiveB2 (outCfgOf e o) = nbit (ocOf e o).live 0 := by
  show Metronome.Glue.bitAt (outCfgOf e o).bind 3 = nbit (ocOf e o).live 0
  rw [outCfgOf_bind, bindPack_live0]

/-- `BIND` bit 4 is `LIVE[1]`. -/
theorem out_live1 (e : Env) (o : Nat) :
    Metronome.Glue.outLiveB1 (outCfgOf e o) = nbit (ocOf e o).live 1 := by
  show Metronome.Glue.bitAt (outCfgOf e o).bind 4 = nbit (ocOf e o).live 1
  rw [outCfgOf_bind, bindPack_live1]

theorem out_sel0 (e : Env) (o : Nat) (hr : CvRange e) :
    (Metronome.Glue.slice (outCfgOf e o).sel 0 2).toNat = (ocOf e o).sel0 := by
  rw [outCfgOf_sel, selPack_0, bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hr.sel0 o)]

theorem out_sel1 (e : Env) (o : Nat) (hr : CvRange e) :
    (Metronome.Glue.slice (outCfgOf e o).sel 2 2).toNat = (ocOf e o).sel1 := by
  rw [outCfgOf_sel, selPack_1, bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hr.sel1 o)]

theorem out_sel2 (e : Env) (o : Nat) (hr : CvRange e) :
    (Metronome.Glue.slice (outCfgOf e o).sel 4 2).toNat = (ocOf e o).sel2 := by
  rw [outCfgOf_sel, selPack_2, bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hr.sel2 o)]

/-- The cut's `COMMITTED(LINE)` nibble is the machine's. -/
theorem out_comm (e : Env) (o : Nat) (hr : CvRange e) :
    Metronome.Glue.outComm (outCfgOf e o) = (vget e.ms.lines (ocOf e o).line).committed := by
  show Metronome.Glue.slice (outCfgOf e o).comm
    (4 * (Metronome.Glue.outLine (outCfgOf e o)).toNat) 4 =
    (vget e.ms.lines (ocOf e o).line).committed
  rw [outCfgOf_comm, out_line e o hr]
  have hl := hr.line o
  rcases (by omega : (ocOf e o).line = 0 ∨ (ocOf e o).line = 1 ∨ (ocOf e o).line = 2 ∨
    (ocOf e o).line = 3) with h0 | h0 | h0 | h0
  · rw [h0]; exact commPack_0 _ _ _ _
  · rw [h0]; exact commPack_1 _ _ _ _
  · rw [h0]; exact commPack_2 _ _ _ _
  · rw [h0]; exact commPack_3 _ _ _ _

theorem seg_bv (e : Env) (k : Nat) :
    (bv 2 (seg (vget e.ms.lines k))).toNat = seg (vget e.ms.lines k) := by
  rw [bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (seg_lt _)]

/-- The cut's `SEG(LINE)` is the machine's. -/
theorem out_seg (e : Env) (o : Nat) (hr : CvRange e) :
    (Metronome.Glue.outSeg (outCfgOf e o)).toNat = seg (vget e.ms.lines (ocOf e o).line) := by
  show (Metronome.Glue.slice (outCfgOf e o).seg
    (2 * (Metronome.Glue.outLine (outCfgOf e o)).toNat) 2).toNat =
    seg (vget e.ms.lines (ocOf e o).line)
  rw [outCfgOf_seg, out_line e o hr]
  have hl := hr.line o
  rcases (by omega : (ocOf e o).line = 0 ∨ (ocOf e o).line = 1 ∨ (ocOf e o).line = 2 ∨
    (ocOf e o).line = 3) with h0 | h0 | h0 | h0
  · rw [h0, segPack_0, seg_bv e 0]
  · rw [h0, segPack_1, seg_bv e 1]
  · rw [h0, segPack_2, seg_bv e 2]
  · rw [h0, segPack_3, seg_bv e 3]

/-- The cut's `PIN[PINA(LINE)]` level is the machine's. -/
theorem out_pinA (e : Env) (o : Nat) (hr : CvRange e) :
    Metronome.Glue.bitAt (outCfgOf e o).pinA (Metronome.Glue.outLine (outCfgOf e o)).toNat =
      e.p.pin (vget e.cv.lines (ocOf e o).line).pina := by
  rw [outCfgOf_pinA, out_line e o hr]
  have hl := hr.line o
  rcases (by omega : (ocOf e o).line = 0 ∨ (ocOf e o).line = 1 ∨ (ocOf e o).line = 2 ∨
    (ocOf e o).line = 3) with h0 | h0 | h0 | h0
  · rw [h0, pack4b_0]
  · rw [h0, pack4b_1]
  · rw [h0, pack4b_2]
  · rw [h0, pack4b_3]

/-- The cut's `PIN[PINB(LINE)]` level is the machine's. -/
theorem out_pinB (e : Env) (o : Nat) (hr : CvRange e) :
    Metronome.Glue.bitAt (outCfgOf e o).pinB (Metronome.Glue.outLine (outCfgOf e o)).toNat =
      e.p.pin (vget e.cv.lines (ocOf e o).line).pinb := by
  rw [outCfgOf_pinB, out_line e o hr]
  have hl := hr.line o
  rcases (by omega : (ocOf e o).line = 0 ∨ (ocOf e o).line = 1 ∨ (ocOf e o).line = 2 ∨
    (ocOf e o).line = 3) with h0 | h0 | h0 | h0
  · rw [h0, pack4b_0]
  · rw [h0, pack4b_1]
  · rw [h0, pack4b_2]
  · rw [h0, pack4b_3]

/-- The table read of the cut's `LUT` is the machine's `nbit` of the same word. -/
theorem readBit_bv (v k : Nat) (hk : k < 32) :
    Metronome.Glue.readBit (bv 32 v) k = nbit v k := by
  have hone : BitVec.toNat (1 : BitVec 32) = 1 := by decide
  have hbne : ∀ y : BitVec 32, (y != 0) = (y.toNat != 0) := fun _ => rfl
  have hmod : nbit (v % 2 ^ 32) k = nbit v k := by
    rw [nbit_eq_testBit, nbit_eq_testBit, Nat.testBit_mod_two_pow,
      show decide (k < 32) = true from by simp [hk], Bool.true_and]
  rw [← hmod]
  show (((bv 32 v) >>> k) &&& 1 != 0) = nbit (v % 2 ^ 32) k
  rw [hbne, BitVec.toNat_and, BitVec.toNat_ushiftRight, hone,
    show (bv 32 v).toNat = v % 2 ^ 32 from by simp [bv, BitVec.toNat_ofNat],
    Nat.and_one_is_mod]
  simp only [nbit]
  rcases Nat.mod_two_eq_zero_or_one ((v % 2 ^ 32) >>> k) with h | h <;> simp [h]

/-- The cut's `b0` is the machine's. -/
theorem out_b0 (e : Env) (o : Nat) (hr : CvRange e) :
    Metronome.Glue.outB0 (outCfgOf e o) =
      bit (vget e.ms.lines (ocOf e o).line).committed (ocOf e o).sel0 := by
  unfold Metronome.Glue.outB0
  rw [out_comm e o hr, out_sel0 e o hr, bitAt_eq_nbit, bit_eq_nbit]

/-- The cut's `b1` is the machine's (with the `LIVE[1]` substitution). -/
theorem out_b1 (e : Env) (o : Nat) (hr : CvRange e) :
    Metronome.Glue.outB1 (outCfgOf e o) =
      if nbit (ocOf e o).live 1 then e.p.pin (vget e.cv.lines (ocOf e o).line).pinb
      else bit (vget e.ms.lines (ocOf e o).line).committed (ocOf e o).sel1 := by
  unfold Metronome.Glue.outB1
  rw [out_live1 e o]
  by_cases hl : nbit (ocOf e o).live 1
  · rw [if_pos hl, if_pos hl, out_pinB e o hr]
  · rw [if_neg hl, if_neg hl, out_comm e o hr, out_sel1 e o hr, bitAt_eq_nbit, bit_eq_nbit]

/-- The cut's `b2` is the machine's (with the `LIVE[0]` substitution). -/
theorem out_b2 (e : Env) (o : Nat) (hr : CvRange e) :
    Metronome.Glue.outB2 (outCfgOf e o) =
      if nbit (ocOf e o).live 0 then e.p.pin (vget e.cv.lines (ocOf e o).line).pina
      else bit (vget e.ms.lines (ocOf e o).line).committed (ocOf e o).sel2 := by
  unfold Metronome.Glue.outB2
  rw [out_live0 e o]
  by_cases hl : nbit (ocOf e o).live 0
  · rw [if_pos hl, if_pos hl, out_pinA e o hr]
  · rw [if_neg hl, if_neg hl, out_comm e o hr, out_sel2 e o hr, bitAt_eq_nbit, bit_eq_nbit]

/-- `k ||| s * 2 ^ i = s * 2 ^ i + k` when `k` fits below bit `i`. -/
theorem or_shift (k s i : Nat) (hk : k < 2 ^ i) : k ||| (s * 2 ^ i) = s * 2 ^ i + k := by
  have h := Nat.shiftLeft_add_eq_or_of_lt (i := i) (b := k) (a := s) hk
  rw [Nat.shiftLeft_eq] at h
  rw [Nat.or_comm, ← h]

/-- The cut's five-bit OR-packed `outIdx` value. -/
theorem pack5_toNat (b0 b1 b2 : Bool) (sg : BitVec 2) :
    ((((if b0 then (1 : BitVec 5) else 0) ||| (if b1 then 2 else 0)) |||
        (if b2 then 4 else 0)) |||
      (BitVec.shiftLeft (BitVec.setWidth 5 sg) 3)).toNat =
      sg.toNat * 8 + b2n b2 * 4 + b2n b1 * 2 + b2n b0 := by
  have h0 : ((if b0 then (1 : BitVec 5) else 0)).toNat = b2n b0 := by
    cases b0 <;> rfl
  have h1 : ((if b1 then (2 : BitVec 5) else 0)).toNat = b2n b1 * 2 := by
    cases b1 <;> rfl
  have h2 : ((if b2 then (4 : BitVec 5) else 0)).toNat = b2n b2 * 4 := by
    cases b2 <;> rfl
  have h3 : (BitVec.shiftLeft (BitVec.setWidth 5 sg) 3).toNat = sg.toNat * 8 := by
    show ((BitVec.setWidth 5 sg) <<< 3).toNat = sg.toNat * 8
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
    have hs : sg.toNat < 4 := sg.isLt
    omega
  have hb0 : b2n b0 < 2 := b2n_lt b0
  have hb1 : b2n b1 * 2 < 4 := by have := b2n_lt b1; omega
  have hb2 : b2n b2 * 4 < 8 := by have := b2n_lt b2; omega
  have e1 : sg.toNat * 8 + b2n b2 * 4 = (sg.toNat * 2 + b2n b2) * 4 := by omega
  have e2 : (sg.toNat * 2 + b2n b2) * 4 + b2n b1 * 2 =
      ((sg.toNat * 2 + b2n b2) * 2 + b2n b1) * 2 := by omega
  rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or, h0, h1, h2, h3,
    Nat.or_assoc, Nat.or_assoc, or_shift (b2n b2 * 4) (sg.toNat) 3 hb2, e1,
    or_shift (b2n b1 * 2) (sg.toNat * 2 + b2n b2) 2 hb1, e2,
    or_shift (b2n b0) ((sg.toNat * 2 + b2n b2) * 2 + b2n b1) 1 hb0]

/-- The machine's output-pin table index in the cut's shape. -/
def idxNat (e : Env) (o : Nat) : Nat :=
  if (ocOf e o).bound then
    seg (vget e.ms.lines (ocOf e o).line) * 8 +
      b2n (if nbit (ocOf e o).live 0 then e.p.pin (vget e.cv.lines (ocOf e o).line).pina
        else bit (vget e.ms.lines (ocOf e o).line).committed (ocOf e o).sel2) * 4 +
      b2n (if nbit (ocOf e o).live 1 then e.p.pin (vget e.cv.lines (ocOf e o).line).pinb
        else bit (vget e.ms.lines (ocOf e o).line).committed (ocOf e o).sel1) * 2 +
      b2n (bit (vget e.ms.lines (ocOf e o).line).committed (ocOf e o).sel0)
  else 0

/-- The machine's `outIdx` is `idxNat`. -/
theorem outIdx_machine (e : Env) (o : Nat) : Machine.outIdx e.ms e.cv e.p o = idxNat e o := rfl

/-- The cut's `outIdx` value is `idxNat`. -/
theorem outIdx_cut (e : Env) (o : Nat) (hr : CvRange e) :
    (Metronome.Glue.outIdx (outCfgOf e o)).toNat = idxNat e o := by
  unfold Metronome.Glue.outIdx idxNat
  rw [out_bound e o]
  by_cases hb : (ocOf e o).bound
  · rw [if_pos hb, if_pos hb, pack5_toNat, out_seg e o hr, out_b2 e o hr, out_b1 e o hr,
      out_b0 e o hr, bit_eq_nbit]
  · rw [if_neg hb, if_neg hb]
    rfl

/-- The cut's five-bit table index has the machine's `outIdx` value. -/
theorem outIdx_bridge (e : Env) (o : Nat) (hr : CvRange e) :
    Machine.outIdx e.ms e.cv e.p o = (Metronome.Glue.outIdx (outCfgOf e o)).toNat := by
  rw [outIdx_machine, outIdx_cut e o hr]

/-! ### The output registers and the pin buses -/

/-- `packBits` is below `2 ^ length`. -/
theorem packBits_lt (l : List Bool) : packBits l < 2 ^ l.length := by
  induction l with
  | nil => simp [packBits]
  | cons b rest ih =>
    have hb := b2n_lt b
    rw [show packBits (b :: rest) = packBits rest * 2 + b2n b from rfl,
      List.length_cons, Nat.pow_succ]
    omega

/-- Bit `k` of `packBits` is list element `k`. -/
theorem packBits_testBit (bs : List Bool) (k : Nat) (hk : k < bs.length) :
    (packBits bs).testBit k = bs[k] := by
  induction bs generalizing k with
  | nil => simp at hk
  | cons b rest ih =>
    rw [show packBits (b :: rest) = packBits rest * 2 + b2n b from rfl]
    cases k with
    | zero =>
      rw [Nat.testBit_zero, List.getElem_cons_zero]
      have hmod : (packBits rest * 2 + b2n b) % 2 = b2n b := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (b2n_lt b)]
      rw [hmod]
      cases b <;> rfl
    | succ k' =>
      rw [Nat.testBit_add_one,
        show (packBits rest * 2 + b2n b) / 2 = packBits rest from by
          rw [Nat.add_comm, Nat.add_mul_div_right (b2n b) (packBits rest) (by decide : 0 < 2),
            Nat.div_eq_of_lt (b2n_lt b), Nat.zero_add],
        ih k' (by simpa using hk), List.getElem_cons_succ]

/-- `(l.zip l).map g` with the diagonal entry. -/
theorem zip_self_map {α : Type} {β : Type} (l : List α) (g : α → α → β) :
    (l.zip l).map (fun (i, o) => g i o) = l.map (fun o => g o o) := by
  induction l with
  | nil => rfl
  | cons x rest ih => simp only [List.zip_cons_cons, List.map_cons, ih]

/-- Bit `k` of a packed `n`-entry table is entry `k`. -/
theorem packBits_map_testBit (n : Nat) (g : Nat → Bool) (k : Nat) (hk : k < n) :
    (packBits ((List.range n).map g)).testBit k = g k := by
  rw [packBits_testBit _ k (by simpa using hk), List.getElem_map, List.getElem_range]

/-- The machine's OUT entries are the cut's per-pin registers. -/
theorem outsOf_eq (e : Env) :
    (((List.range Tables.N_OUT_PINS).map (Machine.outIdx e.ms e.cv e.p)).zip
        (List.range Tables.N_OUT_PINS)).map (fun (i, o) => nbit (vget e.cv.outs o).lut i) =
      (List.range Tables.N_OUT_PINS).map
        (fun o => nbit (ocOf e o).lut (Machine.outIdx e.ms e.cv e.p o)) := by
  induction (List.range Tables.N_OUT_PINS) with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons, List.zip_cons_cons] at ih ⊢
    rw [ih]
    simp only [ocOf]

/-- The machine's OEN entries are the cut's per-pin registers. -/
theorem outsOf_oe (e : Env) :
    (((List.range Tables.N_OUT_PINS).map (Machine.outIdx e.ms e.cv e.p)).zip
        (List.range Tables.N_OUT_PINS)).map (fun (i, o) => nbit (vget e.cv.outs o).oe i) =
      (List.range Tables.N_OUT_PINS).map
        (fun o => nbit (ocOf e o).oe (Machine.outIdx e.ms e.cv e.p o)) := by
  induction (List.range Tables.N_OUT_PINS) with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons, List.zip_cons_cons] at ih ⊢
    rw [ih]
    simp only [ocOf]

theorem take_range : (List.range Tables.N_OUT_PINS).take Tables.N_OE_PINS =
    List.range Tables.N_OE_PINS := by decide

theorem oensOf_eq (e : Env) :
    ((((List.range Tables.N_OUT_PINS).map (Machine.outIdx e.ms e.cv e.p)).zip
        (List.range Tables.N_OUT_PINS)).take Tables.N_OE_PINS).map
        (fun (i, o) => nbit (vget e.cv.outs o).oe i) =
      (List.range Tables.N_OE_PINS).map
        (fun o => nbit (ocOf e o).oe (Machine.outIdx e.ms e.cv e.p o)) := by
  rw [List.map_take, outsOf_oe e, ← List.map_take, take_range]

theorem getLsbD_bv (n X k : Nat) (hk : k < n) : (bv n X).getLsbD k = X.testBit k := by
  rw [show bv n X = BitVec.ofNat n X from rfl, BitVec.getLsbD_ofNat]
  simp [hk]

theorem nbit_bv (n X o : Nat) (ho : o < n) : nbit (bv n X).toNat o = X.testBit o := by
  rw [nbit_eq_testBit, show (bv n X).toNat = X % 2 ^ n from by simp [bv, BitVec.toNat_ofNat],
    Nat.testBit_mod_two_pow, show decide (o < n) = true from by simp [ho], Bool.true_and]

/-- The machine's OUT register bit is the cut's per-pin `OUT` register. -/
theorem out_reg (e : Env) (o : Nat) (hr : CvRange e) (frz : Bool)
    (ho : o < Tables.N_OUT_PINS) :
    nbit (Machine.outNext e.ms e.cv e.p frz).1.toNat o =
      Metronome.Glue.outNext (outCfgOf e o) (bit e.ms.out o) true frz := by
  unfold Machine.outNext
  by_cases hf : frz
  · rw [if_pos hf, hf, Metronome.Glue.outNext_frozen, bit_eq_nbit]
  · rw [if_neg hf, Metronome.Glue.outNext, if_pos rfl, if_neg hf]
    rw [outCfgOf_lut, readBit_bv (ocOf e o).lut _ (by
        have h := (Metronome.Glue.outIdx (outCfgOf e o)).isLt
        simpa using h : (Metronome.Glue.outIdx (outCfgOf e o)).toNat < 32)]
    rw [← outIdx_bridge e o hr, nbit_bv 14 _ o (show o < 14 from ho), outsOf_eq e,
      packBits_map_testBit Tables.N_OUT_PINS _ o (show o < Tables.N_OUT_PINS from ho)]

/-- The machine's OEN register bit is the cut's per-pin `OEN` register. -/
theorem oe_reg (e : Env) (o : Nat) (hr : CvRange e) (frz : Bool)
    (ho : o < Tables.N_OE_PINS) :
    nbit (Machine.outNext e.ms e.cv e.p frz).2.toNat o =
      Metronome.Glue.oeNext (outCfgOf e o) (bit e.ms.oen o) true frz := by
  unfold Machine.outNext
  by_cases hf : frz
  · rw [if_pos hf, hf, Metronome.Glue.oeNext_frozen, bit_eq_nbit]
  · rw [if_neg hf, Metronome.Glue.oeNext, if_pos rfl, if_neg hf]
    rw [outCfgOf_oe, readBit_bv (ocOf e o).oe _ (by
        have h := (Metronome.Glue.outIdx (outCfgOf e o)).isLt
        simpa using h : (Metronome.Glue.outIdx (outCfgOf e o)).toNat < 32)]
    rw [← outIdx_bridge e o hr, nbit_bv 8 _ o (show o < 8 from ho), oensOf_eq e,
      packBits_map_testBit Tables.N_OE_PINS _ o (show o < Tables.N_OE_PINS from ho)]

/-- **Output registers.**  The machine's `OUT` vector is the cut's fourteen per-pin
`OUT` registers packed, and `OEN` is the cut's eight `OEN` registers packed. -/
theorem out_bridge (e : Env) (hr : CvRange e) (frz : Bool) :
    (Machine.outNext e.ms e.cv e.p frz).1 =
        bv 14 (packBits ((List.range Tables.N_OUT_PINS).map
          (fun o => Metronome.Glue.outNext (outCfgOf e o) (bit e.ms.out o) true frz))) ∧
      (Machine.outNext e.ms e.cv e.p frz).2 =
        bv 8 (packBits ((List.range Tables.N_OE_PINS).map
          (fun o => Metronome.Glue.oeNext (outCfgOf e o) (bit e.ms.oen o) true frz))) := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [show ((Machine.outNext e.ms e.cv e.p frz).1).getLsbD k =
        nbit ((Machine.outNext e.ms e.cv e.p frz).1).toNat k from by
      rw [getLsbD_eq_testBit, nbit_eq_testBit]]
    rw [out_reg e k hr frz (show k < Tables.N_OUT_PINS from hk), getLsbD_bv 14 _ k hk,
      packBits_map_testBit Tables.N_OUT_PINS _ k (show k < Tables.N_OUT_PINS from hk)]
  · apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [show ((Machine.outNext e.ms e.cv e.p frz).2).getLsbD k =
        nbit ((Machine.outNext e.ms e.cv e.p frz).2).toNat k from by
      rw [getLsbD_eq_testBit, nbit_eq_testBit]]
    rw [oe_reg e k hr frz (show k < Tables.N_OE_PINS from hk), getLsbD_bv 8 _ k hk,
      packBits_map_testBit Tables.N_OE_PINS _ k (show k < Tables.N_OE_PINS from hk)]

/-- **Pin buses** (§2, §8): `uo_out = {OUT[13:8], IRQ, MISO}`, `uio_out = OUT[7:0]`,
`uio_oe = OEN`, with `MISO = TX[7]`. -/
theorem pins_bridge (e : Env) :
    Machine.pinsOut e.ms =
      ((Metronome.Glue.pins e.ms.out e.ms.oen e.ms.ctrl.irq (bit e.ms.host.tx 7)).1.toNat,
       (Metronome.Glue.pins e.ms.out e.ms.oen e.ms.ctrl.irq (bit e.ms.host.tx 7)).2.1.toNat,
       (Metronome.Glue.pins e.ms.out e.ms.oen e.ms.ctrl.irq (bit e.ms.host.tx 7)).2.2.toNat) := by
  have hbit : (Metronome.Glue.bitByte (bit e.ms.host.tx 7)).toNat = b2n (bit e.ms.host.tx 7) :=
    bitByte_toNat _
  have hirq : ((if e.ms.ctrl.irq then (2 : BitVec 8) else 0)).toNat = b2n e.ms.ctrl.irq * 2 := by
    cases e.ms.ctrl.irq <;> rfl
  have hseg : (BitVec.shiftLeft (BitVec.setWidth 8 (Metronome.Glue.slice e.ms.out 8 6)) 2).toNat =
      (e.ms.out.toNat >>> 8) * 4 := by
    have ho : e.ms.out.toNat < 2 ^ 14 := e.ms.out.isLt
    show ((BitVec.setWidth 8 (Metronome.Glue.slice e.ms.out 8 6)) <<< 2).toNat =
      e.ms.out.toNat >>> 8 * 4
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, slice_toNat, nbits,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
      show (2 : Nat) ^ 8 = 256 from rfl, show (2 : Nat) ^ 6 = 64 from rfl,
      show (2 : Nat) ^ 2 = 4 from rfl]
    have h64 : e.ms.out.toNat / 256 < 64 := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 256)]
      omega
    generalize e.ms.out.toNat / 256 = N at *
    omega
  have hlow : (Metronome.Glue.slice e.ms.out 0 8).toNat = e.ms.out.toNat % 256 := by
    rw [slice_toNat, nbits, Nat.shiftRight_zero, show (2 : Nat) ^ 8 = 256 from rfl]
  have hb : b2n e.ms.ctrl.irq < 2 := b2n_lt e.ms.ctrl.irq
  have hm : b2n (bit e.ms.host.tx 7) < 2 := b2n_lt (bit e.ms.host.tx 7)
  have h1 : (e.ms.out.toNat >>> 8) * 4 + b2n e.ms.ctrl.irq * 2 + b2n (bit e.ms.host.tx 7) =
      ((Metronome.Glue.bitByte (bit e.ms.host.tx 7) |||
        (if e.ms.ctrl.irq then (2 : BitVec 8) else 0)) |||
        BitVec.shiftLeft (BitVec.setWidth 8 (Metronome.Glue.slice e.ms.out 8 6)) 2).toNat := by
    rw [BitVec.toNat_or, BitVec.toNat_or, hbit, hirq, hseg,
      or_shift (b2n (bit e.ms.host.tx 7)) (b2n e.ms.ctrl.irq) 1 (by omega),
      or_shift (b2n e.ms.ctrl.irq * 2 + b2n (bit e.ms.host.tx 7)) (e.ms.out.toNat >>> 8) 2
        (by omega)]
    omega
  unfold Machine.pinsOut Metronome.Glue.pins
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact h1
  · exact hlow.symm
  · rfl

end Metronome.Bridge.Glue