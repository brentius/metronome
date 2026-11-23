import Metronome.Units
import Metronome.Machine

/-!
# Bridge: the per-cut unit spec `Metronome.Units` and the machine units `Metronome.Machine.Units`

`Metronome/Units.lean` is the specification of SPEC_V2 §6.1 that `units_check.py`
proves the extracted RTL equal to, register by register and cycle by cycle.  The
independent whole-chip machine `Metronome.Machine` states the same §6.1 in `Nat`
style (`cntNext`, `shNext`, `lfNext`, `accNext`).  This file maps the cut's
sampled per-unit inputs onto the machine's `Option`-shaped `UnitsIn` fields and
proves the one-step functions equal, so "RTL = cut spec" composes with
"cut spec = machine unit" into "RTL = machine unit".

## Conventions

* The cut has one sampled input record per unit; the machine takes one `Option`
  per write group (the winning move of the cycle, §6).  `absIn` below is the
  map: `none` for "the cut says no write", `some (code, value)` otherwise.
* The machine has no reset input (`unitsNext` is only reached with `rst_q` high),
  so `resetN = true` is a hypothesis of every step theorem, not part of the map.
* Freeze is irrelevant to these fields in the machine (`unitsNext` uses it only
  for `FP`, §12.3) and no move can occur in a frozen cycle (§12.3), so no side
  condition on freeze appears.

The bit-vector work is `bv_decide` certificates; the byte assembly is `Nat`
division/modulo (`omega`) against the core library's `Nat` bitwise lemmas.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Metronome.Bridge

open Metronome
open Metronome.Units

universe u

/-! ## Plumbing: one bit, and Bool ↔ Nat comparisons -/

/-- The cut's `x[b]` (a one-bit part-select) is the machine's `bit`. -/
theorem bitAt_eq_bit {w : Nat} (x : BitVec w) (i : Nat) :
    Units.bitAt x i = Machine.Util.bit x i := by
  rw [Bool.eq_iff_iff]
  simp only [Units.bitAt, Machine.Util.bit, BitVec.getLsbD, bne_iff_ne, ne_eq,
    BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod, Nat.reducePow,
    BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  rw [show BitVec.ushiftRight x i = (x >>> i) from rfl, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [show ((0 : BitVec 1)).toNat = 0 from by decide]
  omega

/-- The machine's `bit` is `nbit` of the `Nat` value. -/
theorem bit_eq_nbit {w : Nat} (x : BitVec w) (i : Nat) :
    Machine.Util.bit x i = Machine.Util.nbit x.toNat i := by
  rw [Bool.eq_iff_iff]
  simp only [Machine.Util.bit, Machine.Util.nbit, BitVec.getLsbD,
    Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, decide_eq_true_eq,
    beq_iff_eq]

/-- The cut's `x[b]` is the machine's `nbit` of the `Nat` value. -/
theorem bitAt_eq_nbit {w : Nat} (x : BitVec w) (i : Nat) :
    Units.bitAt x i = Machine.Util.nbit x.toNat i := by
  rw [bitAt_eq_bit, bit_eq_nbit]

/-- `x == 0` is `x.toNat == 0`: the machine compares `Nat` values. -/
theorem beq_zero_nat {w : Nat} (x : BitVec w) : (x == 0#w) = (x.toNat == 0) := by
  rw [Bool.eq_iff_iff]
  simp [BitVec.toNat_eq]

/-- A one-bit value as a `Nat` is the low bit of the byte. -/
theorem bit_val (d : BitVec 8) :
    (if Units.bitAt d 0 then (1 : Nat) else 0) = d.toNat % 2 := by
  rw [bitAt_eq_nbit]
  simp only [Machine.Util.nbit, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.div_one]
  by_cases h : d.toNat % 2 = 1
  · have hb : (d.toNat % 2 == 1) = true := by simp [h]
    rw [hb]; simp; omega
  · have hb : (d.toNat % 2 == 1) = false := by
      simp only [Bool.eq_false_iff, ne_eq, beq_iff_eq]; omega
    rw [hb]; simp; omega

/-- The low bit of `d` as a `BitVec` unit is `bv 8 (d.toNat % 2)`. -/
theorem bit1_val (d : BitVec 8) :
    (if Units.bitAt d 0 then (1 : BitVec 8) else 0) =
      Machine.Util.bv 8 (d.toNat % 2) := by
  have hv := bit_val d
  by_cases h : Units.bitAt d 0 = true
  · have h1 : (if Units.bitAt d 0 then (1 : BitVec 8) else 0) = 1 := by simp [h]
    have h2 : d.toNat % 2 = 1 := by rw [← hv]; simp [h]
    rw [h1, h2]
    simp [Machine.Util.bv, BitVec.ofNat_toNat]
  · have h1 : (if Units.bitAt d 0 then (1 : BitVec 8) else 0) = 0 := by simp [h]
    have h2 : d.toNat % 2 = 0 := by rw [← hv]; simp [h]
    rw [h1, h2]
    simp [Machine.Util.bv]

/-- The bit of `d` the LSB-first shifter shifts in, as a `Nat`. -/
theorem bit80_val (d : BitVec 8) :
    (if Units.bitAt d 0 then (0x80 : BitVec 8) else 0) =
      Machine.Util.bv 8 (128 * (d.toNat % 2)) := by
  have hv := bit_val d
  by_cases h : Units.bitAt d 0 = true
  · have h1 : (if Units.bitAt d 0 then (0x80 : BitVec 8) else 0) = 0x80 := by simp [h]
    have h2 : d.toNat % 2 = 1 := by rw [← hv]; simp [h]
    rw [h1, h2]
    simp [Machine.Util.bv, BitVec.ofNat_toNat]
  · have h1 : (if Units.bitAt d 0 then (0x80 : BitVec 8) else 0) = 0 := by simp [h]
    have h2 : d.toNat % 2 = 0 := by rw [← hv]; simp [h]
    rw [h1, h2]
    simp [Machine.Util.bv]

/-! ## Byte assembly: `setByte` against the cut's mask-and-or forms

The machine's counter and LFSR write a byte with `Util.setByte x k b` (a `Nat`
expression reduced mod `2^n`); the cut writes `(x &&& mask) ||| (b <<< 8k)`.  The
bridge lemmas put the machine form in `Nat` arithmetic (the `x` with byte `k`
cleared, plus `b * 2^(8k)`) and the mask lemmas read the cleared byte off
`Nat.and_two_pow_sub_one_eq_mod`. -/

/-- 16-bit: clear the low byte. -/
theorem land16_ff00 (x : Nat) (hx : x < 65536) : x &&& 65280 = (x / 256) * 256 := by
  have hmask : (65280 : Nat) = 2 ^ 16 - 1 - 255 := by decide
  have hdiv : (x &&& 65280) / 256 = x / 256 := by
    rw [hmask, show (256 : Nat) = 2 ^ 8 from by decide, Nat.and_div_two_pow]
    rw [show (2 ^ 16 - 1 - 255) / 2 ^ 8 = 2 ^ 8 - 1 from by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hmod : (x &&& 65280) % 256 = 0 := by
    rw [show (256 : Nat) = 2 ^ 8 from by decide, Nat.and_mod_two_pow]
    rw [show (2 ^ 16 - 1 - 255) % 2 ^ 8 = 0 from by decide]
    simp
  have h := Nat.div_add_mod (x &&& 65280) 256
  omega

/-- 16-bit: keep the low byte. -/
theorem land16_00ff (x : Nat) : x &&& 255 = x % 256 := by
  rw [show (255 : Nat) = 2 ^ 8 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]

/-- 32-bit: clear byte 0. -/
theorem land32_p0 (x : Nat) (hx : x < 2 ^ 32) : x &&& 4294967040 = (x / 256) * 256 := by
  have hmask : (4294967040 : Nat) = 2 ^ 32 - 1 - 255 := by decide
  have hdiv : (x &&& 4294967040) / 256 = x / 256 := by
    rw [hmask, show (256 : Nat) = 2 ^ 8 from by decide, Nat.and_div_two_pow]
    rw [show (2 ^ 32 - 1 - 255) / 2 ^ 8 = 2 ^ 24 - 1 from by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hmod : (x &&& 4294967040) % 256 = 0 := by
    rw [show (256 : Nat) = 2 ^ 8 from by decide, Nat.and_mod_two_pow]
    rw [show (2 ^ 32 - 1 - 255) % 2 ^ 8 = 0 from by decide]
    simp
  have h := Nat.div_add_mod (x &&& 4294967040) 256
  omega

/-- 32-bit: clear byte 1. -/
theorem land32_p8 (x : Nat) (hx : x < 2 ^ 32) :
    x &&& 4294902015 = (x / 65536) * 65536 + x % 256 := by
  have hmask : (4294902015 : Nat) = 2 ^ 32 - 1 - 65280 := by decide
  have hdiv : (x &&& 4294902015) / 65536 = x / 65536 := by
    rw [hmask, show (65536 : Nat) = 2 ^ 16 from by decide, Nat.and_div_two_pow]
    rw [show (2 ^ 32 - 1 - 65280) / 2 ^ 16 = 2 ^ 16 - 1 from by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hmod : (x &&& 4294902015) % 65536 = x % 256 := by
    rw [show (65536 : Nat) = 2 ^ 16 from by decide, Nat.and_mod_two_pow]
    rw [show (2 ^ 32 - 1 - 65280) % 2 ^ 16 = 2 ^ 8 - 1 from by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  have h := Nat.div_add_mod (x &&& 4294902015) 65536
  omega

/-- 32-bit: clear byte 2. -/
theorem land32_p16 (x : Nat) (hx : x < 2 ^ 32) :
    x &&& 4278255615 = (x / 16777216) * 16777216 + x % 65536 := by
  have hdiv : (x &&& 4278255615) / 16777216 = x / 16777216 := by
    rw [show (16777216 : Nat) = 2 ^ 24 from by decide, Nat.and_div_two_pow]
    rw [show (4278255615 : Nat) / 2 ^ 24 = 2 ^ 8 - 1 from by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hmod : (x &&& 4278255615) % 16777216 = x % 65536 := by
    rw [show (16777216 : Nat) = 2 ^ 24 from by decide, Nat.and_mod_two_pow]
    rw [show (4278255615 : Nat) % 2 ^ 24 = 2 ^ 16 - 1 from by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  have h := Nat.div_add_mod (x &&& 4278255615) 16777216
  omega

/-- 32-bit: keep the low three bytes. -/
theorem land32_p24 (x : Nat) : x &&& 16777215 = x % 16777216 := by
  rw [show (16777215 : Nat) = 2 ^ 24 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]

/-- The `Nat` value of the 9-bit sum of two bytes. -/
theorem toNat_sum9 (a v : BitVec 8) :
    (BitVec.setWidth 9 a + BitVec.setWidth 9 v).toNat = a.toNat + v.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have ha := a.isLt
  have hv := v.isLt
  omega

/-! ## Counter (SPEC v1 §6.1)

`LO: V[7:0]' = v`, `HI: V[15:8]' = v`, `DEC: V' = V ? V-1 : 0`; `Z = (V == 0)`.
The machine's `cntNext x (some (0|1|2, v))` performs the same three writes. -/

namespace CounterB

/-- The abstraction: the cut's 16-bit `V` is the machine counter cell. -/
def abs (s : Counter.State) : BitVec 16 := s.v

/-- The abstraction of the sampled move: `LO` = code 0, `HI` = code 1, `DEC`
(and the undocumented code 3, which the RTL also decodes as `DEC`) = code 2. -/
def absIn (i : Counter.Input) : Option (Nat × Nat) :=
  if !i.we then none
  else if i.sel = Counter.SEL_LO then some (0, i.d.toNat)
  else if i.sel = Counter.SEL_HI then some (1, i.d.toNat)
  else some (2, i.d.toNat)

/-- `LO` is `setByte x 0 v`. -/
theorem setByte_lo (x : BitVec 16) (d : BitVec 8) :
    Machine.Util.setByte x 0 d.toNat = ((x &&& (0xFF00 : BitVec 16)) ||| d.setWidth 16) := by
  have hor : ((x &&& (0xFF00 : BitVec 16)) ||| d.setWidth 16) =
      (x &&& (0xFF00 : BitVec 16)) + d.setWidth 16 := by bv_decide
  rw [hor]
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hd := d.isLt
  simp only [Machine.Util.setByte, Machine.Util.nbits, Machine.Util.bv, BitVec.toNat_ofNat,
    BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.div_one, Nat.mul_one]
  simp
  rw [land16_ff00 x.toNat hx]
  rw [show x.toNat - x.toNat % 256 = x.toNat / 256 * 256 from by omega]
  omega

/-- `HI` is `setByte x 1 v`. -/
theorem setByte_hi (x : BitVec 16) (d : BitVec 8) :
    Machine.Util.setByte x 1 d.toNat =
      ((x &&& (0x00FF : BitVec 16)) ||| (d.setWidth 16 <<< 8)) := by
  have hor : ((x &&& (0x00FF : BitVec 16)) ||| (d.setWidth 16 <<< 8)) =
      (x &&& (0x00FF : BitVec 16)) + (d.setWidth 16 <<< 8) := by bv_decide
  rw [hor]
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hd := d.isLt
  simp only [Machine.Util.setByte, Machine.Util.nbits, Machine.Util.bv, BitVec.toNat_ofNat,
    BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_shiftLeft]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.div_one, Nat.mul_one]
  simp
  rw [land16_00ff x.toNat]
  simp only [Nat.shiftLeft_eq]
  omega

/-- `DEC` saturates at zero, as the machine writes it. -/
theorem dec_eq (x : BitVec 16) :
    (if x = 0 then (0 : BitVec 16) else x - 1) = (if x.toNat = 0 then 0 else x - 1) := by
  by_cases h : x = 0
  · have h' : x.toNat = 0 := by rw [h]; rfl
    rw [if_pos h]
    simp [h']
  · have h' : x.toNat ≠ 0 := by
      intro h0
      exact h (BitVec.eq_of_toNat_eq (by simpa using h0))
    rw [if_neg h]
    simp only [h', if_false]

/-- **Counter bridge.**  The cut's `V'` is the machine's `cntNext` on the mapped
move, for every state and every move, with `rst_q` high. -/
theorem abs_step (s : Counter.State) (i : Counter.Input) (hreset : i.resetN = true) :
    abs (Counter.step s i) = Machine.cntNext (abs s) (absIn i) := by
  unfold abs
  by_cases hw : i.we = true <;> by_cases hlo : i.sel = Counter.SEL_LO <;>
    by_cases hhi : i.sel = Counter.SEL_HI
  all_goals
    simp only [Counter.step, Counter.vNext, Machine.cntNext, absIn, hreset, hw, hlo, hhi,
      Bool.not_true, Bool.not_false]
    simp
    try (first
      | exact (setByte_lo s.v i.d).symm
      | exact (setByte_hi s.v i.d).symm
      | exact dec_eq s.v
      | rfl)

/-- The cut's `Z` output is the machine guard `CNT.Z`. -/
theorem zOut_eq (s : Counter.State) : Counter.zOut s = (s.v.toNat == 0) :=
  beq_zero_nat s.v

end CounterB

/-! ## Shifter (SPEC v1 §6.1)

`LD: D' = v, CNT' = LEN ? LEN : 8`; `SH: D' = MSB ? {D[6:0], v[0]} : {v[0], D[7:1]},
CNT' = CNT ? CNT-1 : 0`; `CFG: LEN' = v[3:0], MSB' = v[4]`; `O = MSB ? D[7] : D[0]`,
`DONE = (CNT == 0)`.  The cut takes the data move and the `SHk.CFG` move as two
write groups of one cycle; the machine's `shNext` takes both as two `Option`s. -/

namespace ShifterB

/-- The abstraction: the cut's `D`, `CNT`, `LEN`, `MSB` are the machine `ShSt`. -/
def abs (s : Shifter.State) : Machine.ShSt := ⟨s.dr, s.cnt, s.len, s.msb⟩

/-- The data move: `sel = 0` is `LD` (`true`), `sel = 1` is `SH` (`false`). -/
def absOp (i : Shifter.Input) : Option (Bool × Nat) :=
  if !i.we then none else some (!i.sel, i.d.toNat)

/-- The `SHk.CFG` move. -/
def absCfg (i : Shifter.Input) : Option Nat :=
  if i.cfgWe then some i.cfgD.toNat else none

/-- `LD`'s `CNT' = LEN ? LEN : 8`, in the shape `simp` produces. -/
theorem loadCount_eq (s : Shifter.State) :
    Shifter.loadCount s = (if s.len.toNat = 0 then (8 : BitVec 4) else s.len) := by
  unfold Shifter.loadCount
  by_cases h : s.len = 0
  · have h' : s.len.toNat = 0 := by rw [h]; rfl
    rw [if_pos h, if_pos h']
  · have h' : s.len.toNat ≠ 0 := by
      intro h0
      exact h (BitVec.eq_of_toNat_eq (by simpa using h0))
    rw [if_neg h, if_neg h']

/-- `SH`'s `CNT' = CNT ? CNT-1 : 0`, in the shape `simp` produces. -/
theorem shiftCount_eq (s : Shifter.State) :
    Shifter.shiftCount s = (if s.cnt.toNat = 0 then (0 : BitVec 4) else s.cnt - 1) := by
  unfold Shifter.shiftCount
  by_cases h : s.cnt = 0
  · have h' : s.cnt.toNat = 0 := by rw [h]; rfl
    rw [if_pos h, if_pos h']
  · have h' : s.cnt.toNat ≠ 0 := by
      intro h0
      exact h (BitVec.eq_of_toNat_eq (by simpa using h0))
    rw [if_neg h, if_neg h']

/-- A byte is the `bv` of its `Nat` value. -/
theorem bv_toNat (d : BitVec 8) : Machine.Util.bv 8 d.toNat = d := by
  simp [Machine.Util.bv, BitVec.ofNat_toNat 8 d]

/-- `MSB`-first `SH`: `{D[6:0], v[0]}`. -/
theorem sh_msb (dr : BitVec 8) (d : BitVec 8) :
    Machine.Util.bv 8 (dr.toNat * 2 % 256 + d.toNat % 2) =
      ((dr <<< 1) ||| (if Units.bitAt d 0 then (1 : BitVec 8) else 0)) := by
  rw [bit1_val]
  generalize hb : d.toNat % 2 = b
  rcases (show b = 0 ∨ b = 1 by omega) with h | h
  · subst h
    simp only [Machine.Util.bv, Nat.zero_mod, Nat.add_zero]
    simp only [BitVec.or_zero]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.reducePow]
    rw [Nat.shiftLeft_eq]
    omega
  · subst h
    simp only [Machine.Util.bv]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, BitVec.toNat_or, Nat.reducePow]
    have h2 : dr.toNat * 2 % 256 = (dr.toNat % 128) <<< 1 := by
      rw [Nat.shiftLeft_eq]
      omega
    rw [h2]
    rw [show dr.toNat <<< 1 % 256 = (dr.toNat % 128) <<< 1 from by
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
      omega]
    rw [show (1 : Nat) % 256 = 1 from by decide]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 1) (b := 1) (by decide)]
    rw [Nat.shiftLeft_eq]
    omega

/-- LSB-first `SH`: `{v[0], D[7:1]}`. -/
theorem sh_lsb (dr : BitVec 8) (d : BitVec 8) :
    Machine.Util.bv 8 (128 * (d.toNat % 2) + dr.toNat / 2) =
      ((dr >>> 1) ||| (if Units.bitAt d 0 then (0x80 : BitVec 8) else 0)) := by
  rw [bit80_val]
  generalize hb : d.toNat % 2 = b
  rcases (show b = 0 ∨ b = 1 by omega) with h | h
  · subst h
    simp only [Machine.Util.bv, Nat.zero_mod, Nat.mul_zero, Nat.zero_add]
    simp only [BitVec.or_zero]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  · subst h
    simp only [Machine.Util.bv, Nat.mul_one]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_or]
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [Nat.or_two_pow_eq_add_of_lt (a := dr.toNat / 2) (n := 7) (by omega)]
    have hb2 := dr.isLt
    omega

/-- `LEN`/`MSB` configuration: `slice v 0 4` and bit 4. -/
theorem slice_eq (x : BitVec 5) : Units.slice x 0 4 = Machine.Util.bv 4 x.toNat := by
  unfold Units.slice Machine.Util.bv
  rw [BitVec.ofNat_toNat 4 x, BitVec.truncate_eq_setWidth]
  simp

/-- The cut's `SH` data path with `MSB` set. -/
theorem shifted_msb (s : Shifter.State) (i : Shifter.Input) (hm : s.msb = true) :
    Shifter.shifted s i =
      Machine.Util.bv 8 (s.dr.toNat * 2 % 256 + i.d.toNat % 2) := by
  unfold Shifter.shifted
  rw [if_pos hm]
  exact (sh_msb s.dr i.d).symm

/-- The cut's `SH` data path with `MSB` clear. -/
theorem shifted_lsb (s : Shifter.State) (i : Shifter.Input) (hm : ¬ s.msb = true) :
    Shifter.shifted s i =
      Machine.Util.bv 8 (i.d.toNat % 2 * 128 + s.dr.toNat / 2) := by
  unfold Shifter.shifted
  rw [if_neg hm]
  rw [show i.d.toNat % 2 * 128 = 128 * (i.d.toNat % 2) from by omega]
  exact (sh_lsb s.dr i.d).symm

/-- `x &&& 2^7` is non-zero exactly when bit 7 is set. -/
theorem and_bit7 (x : BitVec 8) :
    ((x &&& (0x80 : BitVec 8)) != 0) = Units.bitAt x 7 := by
  rw [show (0x80 : BitVec 8) = BitVec.twoPow 8 7 from by decide, BitVec.and_twoPow]
  rw [bitAt_eq_bit, Machine.Util.bit]
  by_cases h : x.getLsbD 7 = true
  · rw [if_pos h, h]
    decide
  · have hf : x.getLsbD 7 = false := by cases hv : x.getLsbD 7 <;> simp_all
    rw [if_neg h, hf]
    decide

/-- `x &&& 2^0` is non-zero exactly when bit 0 is set. -/
theorem and_bit0 (x : BitVec 8) :
    ((x &&& (0x01 : BitVec 8)) != 0) = Units.bitAt x 0 := by
  rw [show (0x01 : BitVec 8) = BitVec.twoPow 8 0 from by decide, BitVec.and_twoPow]
  rw [bitAt_eq_bit, Machine.Util.bit]
  by_cases h : x.getLsbD 0 = true
  · rw [if_pos h, h]
    decide
  · have hf : x.getLsbD 0 = false := by cases hv : x.getLsbD 0 <;> simp_all
    rw [if_neg h, hf]
    decide

/-- **Shifter bridge.**  The cut's four registers are the machine's `shNext` on
the mapped data move and `SHk.CFG` move. -/
theorem abs_step (s : Shifter.State) (i : Shifter.Input) (hreset : i.resetN = true) :
    abs (Shifter.step s i) = Machine.shNext (abs s) (absOp i) (absCfg i) := by
  unfold abs
  by_cases hw : i.we = true <;> by_cases hs : i.sel = true <;> by_cases hc : i.cfgWe = true <;>
    by_cases hm : s.msb = true
  all_goals
    simp only [Shifter.step, Shifter.drNext, Shifter.cntNext, Shifter.lenNext, Shifter.msbNext,
      Machine.shNext, absOp, absCfg, hreset, hw, hs, hc, hm, Bool.not_true, Bool.not_false]
    simp
    try (repeat' apply And.intro
         all_goals
           first
           | exact shifted_msb s i hm
           | exact shifted_lsb s i hm
           | exact loadCount_eq s
           | exact shiftCount_eq s
           | exact slice_eq i.cfgD
           | exact bv_toNat i.d
           | exact (bv_toNat i.d).symm
           | exact bitAt_eq_nbit i.cfgD 4
           | rfl)

/-- The cut's `O = MSB ? D[7] : D[0]` is the machine's `shOut`. -/
theorem out_eq (s : Shifter.State) : Shifter.out s = Machine.shOut (abs s) := by
  unfold Shifter.out Machine.shOut abs
  dsimp only
  rw [← bitAt_eq_bit, ← bitAt_eq_bit]
  by_cases hm : s.msb = true
  · rw [if_pos hm, if_pos hm]
    exact and_bit7 s.dr
  · rw [if_neg hm, if_neg hm]
    exact and_bit0 s.dr

/-- The cut's `DONE = (CNT == 0)` is the machine guard `SH.DONE`. -/
theorem done_eq (s : Shifter.State) : Shifter.done s = ((abs s).cnt.toNat == 0) :=
  beq_zero_nat s.cnt

end ShifterB

/-! ## LFSR / CRC (SPEC v1 §6.1)

`ST: fb = S[0] ^ v[0]; S' = (S >> 1) ^ (fb ? POLY : 0)`; `Bk: S[8k+7:8k]' = v`;
`OUT = S[0]`.  Codes 5..7 are not documented destinations; the cut and the
machine both hold. -/

namespace LfsrB

/-- The abstraction: the cut's 32-bit `S` is the machine LFSR cell. -/
def abs (s : Lfsr.State) : BitVec 32 := s.s

/-- The abstraction of the sampled move: `ST` = code `none`, `B0..B3` = codes
`0..3`; codes 5..7 hold. -/
def absIn (i : Lfsr.Input) : Option (Option Nat × Nat) :=
  if !i.we then none
  else if i.sel = 0 then some (none, i.d.toNat)
  else if i.sel = 1 then some (some 0, i.d.toNat)
  else if i.sel = 2 then some (some 1, i.d.toNat)
  else if i.sel = 3 then some (some 2, i.d.toNat)
  else if i.sel = 4 then some (some 3, i.d.toNat)
  else none

/-- The eight op codes of a 3-bit selector. -/
theorem sel3_cases (sel : BitVec 3) :
    sel = 0 ∨ sel = 1 ∨ sel = 2 ∨ sel = 3 ∨ sel = 4 ∨ sel = 5 ∨ sel = 6 ∨ sel = 7 := by
  have hlt := sel.isLt
  have hsel : sel = BitVec.ofNat 3 sel.toNat := by
    rw [BitVec.ofNat_toNat 3 sel]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth]
    omega
  have hc : sel.toNat = 0 ∨ sel.toNat = 1 ∨ sel.toNat = 2 ∨ sel.toNat = 3 ∨
      sel.toNat = 4 ∨ sel.toNat = 5 ∨ sel.toNat = 6 ∨ sel.toNat = 7 := by omega
  rcases hc with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 <;>
    (first
      | exact Or.inl (by rw [hsel, h0]; decide)
      | exact Or.inr (Or.inl (by rw [hsel, h0]; decide))
      | exact Or.inr (Or.inr (Or.inl (by rw [hsel, h0]; decide)))
      | exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hsel, h0]; decide))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hsel, h0]; decide)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hsel, h0]; decide))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (by rw [hsel, h0]; decide)))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (by rw [hsel, h0]; decide))))))))

/-- `ST`: the reflected Galois step. -/
theorem st_eq (s : BitVec 32) (poly : BitVec 32) (d : BitVec 8) :
    Machine.lfNext s poly.toNat (some (none, d.toNat)) =
      (s >>> 1) ^^^ (if (Units.bitAt s 0 != Units.bitAt d 0) then poly else 0) := by
  dsimp only [Machine.lfNext, Machine.Util.bv]
  rw [BitVec.ofNat_xor]
  have h1 : BitVec.ofNat 32 (s.toNat >>> 1) = s >>> 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by have hs := s.isLt; omega)]
  have h2 : BitVec.ofNat 32 (if (Machine.Util.bit s 0 != Machine.Util.nbit d.toNat 0) = true then
        poly.toNat else 0) =
      (if (Machine.Util.bit s 0 != Machine.Util.nbit d.toNat 0) = true then poly else 0) := by
    by_cases hb : (Machine.Util.bit s 0 != Machine.Util.nbit d.toNat 0) = true
    · rw [if_pos hb, if_pos hb]
      simp [BitVec.ofNat_toNat]
    · rw [if_neg hb, if_neg hb]
      simp
  rw [h1, h2]
  rw [← bitAt_eq_bit, ← bitAt_eq_nbit]

/-- `B0` = `setByte x 0 v`. -/
theorem setByte_p0 (x : BitVec 32) (d : BitVec 8) :
    Machine.Util.setByte x 0 d.toNat = ((x &&& (0xFFFFFF00 : BitVec 32)) ||| d.setWidth 32) := by
  have hor : ((x &&& (0xFFFFFF00 : BitVec 32)) ||| d.setWidth 32) =
      (x &&& (0xFFFFFF00 : BitVec 32)) + d.setWidth 32 := by bv_decide
  rw [hor]
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hd := d.isLt
  simp only [Machine.Util.setByte, Machine.Util.nbits, Machine.Util.bv, BitVec.toNat_ofNat,
    BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.div_one, Nat.mul_one]
  simp
  rw [land32_p0 x.toNat hx]
  rw [show x.toNat - x.toNat % 256 = x.toNat / 256 * 256 from by omega]
  omega

/-- `B1` = `setByte x 1 v`. -/
theorem setByte_p1 (x : BitVec 32) (d : BitVec 8) :
    Machine.Util.setByte x 1 d.toNat =
      ((x &&& (0xFFFF00FF : BitVec 32)) ||| (d.setWidth 32 <<< 8)) := by
  have hor : ((x &&& (0xFFFF00FF : BitVec 32)) ||| (d.setWidth 32 <<< 8)) =
      (x &&& (0xFFFF00FF : BitVec 32)) + (d.setWidth 32 <<< 8) := by bv_decide
  rw [hor]
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hd := d.isLt
  simp only [Machine.Util.setByte, Machine.Util.nbits, Machine.Util.bv, BitVec.toNat_ofNat,
    BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_shiftLeft]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.div_one, Nat.mul_one]
  simp
  rw [land32_p8 x.toNat hx]
  simp only [Nat.shiftLeft_eq]
  omega

/-- `B2` = `setByte x 2 v`. -/
theorem setByte_p2 (x : BitVec 32) (d : BitVec 8) :
    Machine.Util.setByte x 2 d.toNat =
      ((x &&& (0xFF00FFFF : BitVec 32)) ||| (d.setWidth 32 <<< 16)) := by
  have hor : ((x &&& (0xFF00FFFF : BitVec 32)) ||| (d.setWidth 32 <<< 16)) =
      (x &&& (0xFF00FFFF : BitVec 32)) + (d.setWidth 32 <<< 16) := by bv_decide
  rw [hor]
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hd := d.isLt
  simp only [Machine.Util.setByte, Machine.Util.nbits, Machine.Util.bv, BitVec.toNat_ofNat,
    BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_shiftLeft]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.div_one, Nat.mul_one]
  simp
  rw [land32_p16 x.toNat hx]
  simp only [Nat.shiftLeft_eq]
  omega

/-- `B3` = `setByte x 3 v`. -/
theorem setByte_p3 (x : BitVec 32) (d : BitVec 8) :
    Machine.Util.setByte x 3 d.toNat =
      ((x &&& (0x00FFFFFF : BitVec 32)) ||| (d.setWidth 32 <<< 24)) := by
  have hor : ((x &&& (0x00FFFFFF : BitVec 32)) ||| (d.setWidth 32 <<< 24)) =
      (x &&& (0x00FFFFFF : BitVec 32)) + (d.setWidth 32 <<< 24) := by bv_decide
  rw [hor]
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hd := d.isLt
  simp only [Machine.Util.setByte, Machine.Util.nbits, Machine.Util.bv, BitVec.toNat_ofNat,
    BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_shiftLeft]
  simp only [Nat.reducePow, Nat.reduceMul, Nat.div_one, Nat.mul_one]
  simp
  rw [land32_p24 x.toNat]
  simp only [Nat.shiftLeft_eq]
  omega

/-- **LFSR bridge.**  The cut's `S'` is the machine's `lfNext` on the mapped move
and the configuration `POLY`. -/
theorem abs_step (s : Lfsr.State) (i : Lfsr.Input) (hreset : i.resetN = true) :
    abs (Lfsr.step s i) = Machine.lfNext (abs s) i.poly.toNat (absIn i) := by
  unfold abs
  by_cases hw : i.we = true
  · rcases sel3_cases i.sel with h | h | h | h | h | h | h | h
    all_goals
      simp only [Lfsr.step, Lfsr.sNext, absIn, hw, h, hreset, Bool.not_true, Bool.not_false,
        Machine.lfNext, Machine.Util.bv]
      try (first
        | (unfold Lfsr.stepBit Lfsr.feedback
           exact (st_eq s.s i.poly i.d).symm)
        | (unfold Lfsr.loadByte0
           exact (setByte_p0 s.s i.d).symm)
        | (unfold Lfsr.loadByte1
           exact (setByte_p1 s.s i.d).symm)
        | (unfold Lfsr.loadByte2
           exact (setByte_p2 s.s i.d).symm)
        | (unfold Lfsr.loadByte3
           exact (setByte_p3 s.s i.d).symm)
        | rfl)
  · have hw' : i.we = false := by simpa using hw
    simp only [Lfsr.step, Lfsr.sNext, absIn, hw', hreset, Bool.not_true, Bool.not_false,
      Machine.lfNext, Machine.Util.bv]
    rfl

/-- The cut's `OUT = S[0]` is the machine's `LFk.OUT`. -/
theorem out_eq (s : Lfsr.State) : Lfsr.out s = Machine.Util.bit (abs s) 0 :=
  bitAt_eq_bit s.s 0

end LfsrB

/-! ## Accumulator (SPEC v1 §6.1): the scratch bank `R0..R3`

The accumulator's four scratch bytes are one write group each in both readings, so
they bridge byte-wise: the cut packs them little-endian in `r`, the machine keeps a
`Vector (BitVec 8) 4`.  `rNext_bytes` proves byte `k` of the cut's `Rk'` is the
machine's per-register update; `rNext_eq` lifts it to the vector.

`A`, `Z`, `C`, `N` are a reported gap: the bridge needs the machine's `Nat`-styled
tuple lemma against the cut's `BitVec` ALU, whose `&&&`/`|||`/`^^^` cases remain
open (see BRIDGE_UNITS_STREAM_NOTES.md).  The unused op code 7 is a real
disagreement and is reported with a witness below. -/

namespace AccB

/-- The abstraction of the scratch bank: byte `k` is bits `8k+7..8k`. -/
def rbyte (x : BitVec 32) (k : Nat) : BitVec 8 :=
  BitVec.truncate 8 (BitVec.ushiftRight x (8 * k))

/-- Byte `k` of the cut's `Rk'` is the machine's per-register update. -/
theorem rNext_bytes (s : Acc.State) (i : Acc.Input) (hreset : i.resetN = true)
    (k : Nat) (hk : k < 4) :
    rbyte (Acc.rNext s i) k =
      (if Units.bitAt i.rWe k then rbyte i.rD k else rbyte s.r k) := by
  unfold rbyte Acc.rNext
  rw [hreset]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk4 with rfl | rfl | rfl | rfl
  · by_cases hb : Units.bitAt i.rWe 0 = true <;> simp only [hb, if_true, if_false] <;> bv_decide
  · by_cases hb : Units.bitAt i.rWe 1 = true <;> simp only [hb, if_true, if_false] <;> bv_decide
  · by_cases hb : Units.bitAt i.rWe 2 = true <;> simp only [hb, if_true, if_false] <;> bv_decide
  · by_cases hb : Units.bitAt i.rWe 3 = true <;> simp only [hb, if_true, if_false] <;> bv_decide

/-- The cut's `Rk'` bank is the abstraction of the machine's per-byte update. -/
theorem rNext_eq (s : Acc.State) (i : Acc.Input) (hreset : i.resetN = true) :
    Vector.ofFn (fun k : Fin 4 => rbyte (Acc.rNext s i) k.val) =
      Vector.ofFn (fun k : Fin 4 =>
        if Units.bitAt i.rWe k.val then rbyte i.rD k.val else rbyte s.r k.val) := by
  apply Vector.ext
  intro k hk
  simp only [Vector.getElem_ofFn]
  exact rNext_bytes s i hreset k hk

/-- The unused op code 7: witness that the cut's `alu` and the machine's `accNext`
disagree on `Z` there, which is why every `Z`/`N` bridge carries `opSel ≠ 7`. -/
theorem code7_z_disagrees :
    Units.Acc.zNext ⟨0, false, false, false, 0⟩ ⟨true, 1, 7, 0, 0, 0⟩ = true ∧
      (Machine.accNext 0 false false false 7 0).2.1 = false := by
  decide

/-! ### The flag and bank bridge

`accNext_eq` is the per-op equality: for every op code except 7, the machine's
`accNext` tuple is the cut's ALU record, with the same `A` write enable, `Z`,
`C` write enable, `N`, and result.  The `A`/`Z`/`C`/`N` clauses then follow by
unfolding the one-hot winner, and the scratch bank clause is the existing
`rNext_bytes` against the machine's `reg` write group. -/

/-! #### `Nat` bitwise helpers for the byte results -/

/-- A byte is already reduced mod 256. -/
theorem mod256 (x : BitVec 8) : x.toNat % 256 = x.toNat :=
  Nat.mod_eq_of_lt x.isLt

/-- `Nat.land` of two bytes stays below 256. -/
theorem land_lt (x y : Nat) (hy : y < 256) : x &&& y < 256 :=
  Nat.and_lt_two_pow x (n := 8) (by simpa using hy)

/-- `Nat.lor` of two bytes stays below 256. -/
theorem lor_lt (x y : Nat) (hx : x < 256) (hy : y < 256) : x ||| y < 256 :=
  Nat.or_lt_two_pow (n := 8) (by simpa using hx) (by simpa using hy)

/-- `Nat.xor` of two bytes stays below 256. -/
theorem lxor_lt (x y : Nat) (hx : x < 256) (hy : y < 256) : x ^^^ y < 256 :=
  Nat.xor_lt_two_pow (n := 8) (by simpa using hx) (by simpa using hy)

/-- `v.ule a` is `a ≥ v` on the values. -/
theorem ule_eq (a v : BitVec 8) : (v.ule a) = decide (a.toNat ≥ v.toNat) := rfl

/-- The cut's `a - v` value is the machine's `(a + 256 - v) % 256`. -/
theorem sub_val (a v : BitVec 8) :
    (a - v).toNat = (a.toNat + 256 - v.toNat) % 256 := by
  rw [BitVec.toNat_sub]
  simp only [Nat.reducePow]
  omega

/-- The two spellings of the subtraction modulus. -/
theorem sub_form (a v : BitVec 8) :
    (256 - v.toNat + a.toNat) % 256 = (a.toNat + 256 - v.toNat) % 256 := by
  have hv := v.isLt
  simp only [Nat.reducePow] at hv
  omega

/-- The 9-bit sum stays below 512. -/
theorem sum9_lt (a v : BitVec 8) : a.toNat + v.toNat < 512 := by
  have ha := a.isLt
  have hv := v.isLt
  simp only [Nat.reducePow] at ha hv
  omega

/-- The low byte of the 9-bit sum, as the machine takes it. -/
theorem add_val (a v : BitVec 8) :
    (BitVec.truncate 8 (BitVec.setWidth 9 a + BitVec.setWidth 9 v)).toNat =
      (a.toNat + v.toNat) % 256 := by
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, toNat_sum9]

/-- The `Nat` value of `a &&& v`. -/
theorem and_val (a v : BitVec 8) :
    (a &&& v).toNat = a.toNat &&& v.toNat := BitVec.toNat_and a v

/-- The `Nat` value of `a ||| v`. -/
theorem or_val (a v : BitVec 8) :
    (a ||| v).toNat = a.toNat ||| v.toNat := BitVec.toNat_or a v

/-- The `Nat` value of `a ^^^ v`. -/
theorem xor_val (a v : BitVec 8) :
    (a ^^^ v).toNat = a.toNat ^^^ v.toNat := BitVec.toNat_xor a v

/-- **Per-op accumulator bridge.**  For every op code except the unused 7, the
machine's `accNext` tuple is the cut's ALU record: the same `A` write enable and
result, the same `Z`/`N` of the result, and the same `C` write enable and carry.
`LD`, `ADD`, `SUB`, `AND`, `OR`, `XOR`, `CMP` are the seven cases. -/
theorem accNext_eq (a v : BitVec 8) (c z n : Bool) (sel : BitVec 3) (h7 : sel ≠ 7) :
    Machine.accNext a.toNat z c n sel.toNat v.toNat =
      ((if (Acc.alu a c sel v).wa then (Acc.alu a c sel v).res else a).toNat,
       (Acc.alu a c sel v).z,
       if (Acc.alu a c sel v).wc then (Acc.alu a c sel v).cy else c,
       (Acc.alu a c sel v).n) := by
  rcases LfsrB.sel3_cases sel with h | h | h | h | h | h | h | h
  · subst h
    simp only [Machine.accNext, Acc.alu, Acc.aluWa, Acc.aluWc, Acc.aluCy, Acc.aluZ,
      Acc.aluN, Acc.aluRes, Prod.mk.injEq]
    simp [mod256, beq_zero_nat, bitAt_eq_nbit]
  · subst h
    simp only [Machine.accNext, Acc.alu, Acc.aluWa, Acc.aluWc, Acc.aluCy, Acc.aluZ,
      Acc.aluN, Acc.aluRes, Prod.mk.injEq]
    simp [add_val, beq_zero_nat, bitAt_eq_nbit, toNat_sum9,
      Nat.mod_eq_of_lt (sum9_lt a v)]
  · subst h
    simp only [Machine.accNext, Acc.alu, Acc.aluWa, Acc.aluWc, Acc.aluCy, Acc.aluZ,
      Acc.aluN, Acc.aluRes, Prod.mk.injEq]
    simp [sub_val, sub_form, beq_zero_nat, bitAt_eq_nbit, ule_eq]
  · subst h
    simp only [Machine.accNext, Acc.alu, Acc.aluWa, Acc.aluWc, Acc.aluCy, Acc.aluZ,
      Acc.aluN, Acc.aluRes, Prod.mk.injEq]
    simp [and_val, beq_zero_nat, bitAt_eq_nbit, Nat.mod_eq_of_lt (land_lt _ _ v.isLt)]
  · subst h
    simp only [Machine.accNext, Acc.alu, Acc.aluWa, Acc.aluWc, Acc.aluCy, Acc.aluZ,
      Acc.aluN, Acc.aluRes, Prod.mk.injEq]
    simp [or_val, beq_zero_nat, bitAt_eq_nbit, Nat.mod_eq_of_lt (lor_lt _ _ a.isLt v.isLt)]
  · subst h
    simp only [Machine.accNext, Acc.alu, Acc.aluWa, Acc.aluWc, Acc.aluCy, Acc.aluZ,
      Acc.aluN, Acc.aluRes, Prod.mk.injEq]
    simp [xor_val, beq_zero_nat, bitAt_eq_nbit, Nat.mod_eq_of_lt (lxor_lt _ _ a.isLt v.isLt)]
  · subst h
    simp only [Machine.accNext, Acc.alu, Acc.aluWa, Acc.aluWc, Acc.aluCy, Acc.aluZ,
      Acc.aluN, Acc.aluRes, Prod.mk.injEq]
    simp [sub_val, sub_form, beq_zero_nat, bitAt_eq_nbit, ule_eq]
  · exact absurd h h7

/-- The winner slot's op code: the same `if` chain as the cut's `winnerWa`. -/
def winnerSel (i : Acc.Input) : BitVec 3 :=
  if i.hit = 0 then 0
  else if bitAt i.hit 0 then Acc.opSel i 0
  else if bitAt i.hit 1 then Acc.opSel i 1
  else if bitAt i.hit 2 then Acc.opSel i 2
  else if bitAt i.hit 3 then Acc.opSel i 3
  else if bitAt i.hit 4 then Acc.opSel i 4
  else Acc.opSel i 5

/-- The winner slot's data. -/
def winnerData (i : Acc.Input) : BitVec 8 :=
  if i.hit = 0 then 0
  else if bitAt i.hit 0 then Acc.opData i 0
  else if bitAt i.hit 1 then Acc.opData i 1
  else if bitAt i.hit 2 then Acc.opData i 2
  else if bitAt i.hit 3 then Acc.opData i 3
  else if bitAt i.hit 4 then Acc.opData i 4
  else Acc.opData i 5

theorem winnerSel_eq_slot (i : Acc.Input) (m : Nat) (hm : m < 6)
    (h : i.hit = (1 : BitVec 6) <<< m) : winnerSel i = Acc.opSel i m := by
  have hc : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [winnerSel, h, bitAt]

theorem winnerData_eq_slot (i : Acc.Input) (m : Nat) (hm : m < 6)
    (h : i.hit = (1 : BitVec 6) <<< m) : winnerData i = Acc.opData i m := by
  have hc : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [winnerData, h, bitAt]

/-- A one-hot hit vector is not zero. -/
theorem onehot_ne_zero (m : Nat) (hm : m < 6) : ((1 : BitVec 6) <<< m) ≠ 0 := by
  have hc : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The machine unit state carrying the cut's `A`, flags and scratch bytes. -/
def absUnits (s : Acc.State) : Machine.UnitsSt :=
  { a := s.a, z := s.z, c := s.c, n := s.n, r := Vector.ofFn fun k => rbyte s.r k.val }

/-- The cut's four `Rk` write groups as the machine's `reg` group. -/
def absReg (i : Acc.Input) : Vector (Option Nat) 4 :=
  Vector.ofFn fun k => if bitAt i.rWe k.val then some (rbyte i.rD k.val).toNat else none

/-- The write groups with no accumulator move. -/
def absInNone (i : Acc.Input) : Machine.UnitsIn := { acc := none, reg := absReg i }

/-- The write groups with slot `m`'s accumulator move. -/
def absInSlot (i : Acc.Input) (m : Nat) : Machine.UnitsIn :=
  { acc := some ((Acc.opSel i m).toNat, (Acc.opData i m).toNat), reg := absReg i }

/-- The write groups with the winner's accumulator move. -/
def absIn (i : Acc.Input) : Machine.UnitsIn :=
  { acc := if i.hit = 0 then none else some ((winnerSel i).toNat, (winnerData i).toNat),
    reg := absReg i }

theorem absIn_none (i : Acc.Input) (h : i.hit = 0) : absIn i = absInNone i := by
  simp [absIn, absInNone, h]

theorem absIn_slot (i : Acc.Input) (m : Nat) (hm : m < 6)
    (h : i.hit = (1 : BitVec 6) <<< m) : absIn i = absInSlot i m := by
  have hs := winnerSel_eq_slot i m hm h
  have hd := winnerData_eq_slot i m hm h
  have hz : i.hit ≠ 0 := by rw [h]; exact onehot_ne_zero m hm
  simp only [absIn, absInSlot]
  rw [if_neg hz, hs, hd]

/-- One machine `unitsNext` step on the mapped write groups. -/
def mstep (cfg : Machine.Config) (s : Acc.State) (i : Machine.UnitsIn) : Machine.UnitsSt :=
  Machine.unitsNext cfg (absUnits s) i false

/-- Five-field agreement of one machine step with the cut's accumulator step:
`A`, `Z`, `C`, `N` and the four `Rk` bytes. -/
def Agrees (u : Machine.UnitsSt) (s : Acc.State) (i : Acc.Input) : Prop :=
  u.a = Acc.aNext s i ∧ u.z = Acc.zNext s i ∧ u.c = Acc.cNext s i ∧
    u.n = Acc.nNext s i ∧
    Vector.ofFn (fun k : Fin 4 => rbyte (Acc.rNext s i) k.val) = u.r

/-- The scratch bank clause: the `reg` group is the cut's four `Rk` groups. -/
theorem r_eq_units (cfg : Machine.Config) (s : Acc.State) (i : Acc.Input)
    (hreset : i.resetN = true) (g : Machine.UnitsIn) (hreg : g.reg = absReg i) :
    Vector.ofFn (fun k : Fin 4 => rbyte (Acc.rNext s i) k.val) =
      (Machine.unitsNext cfg (absUnits s) g false).r := by
  rcases g with ⟨flag, acc, reg, sh, shCfg, cnt, lf⟩
  simp only at hreg
  subst hreg
  apply Vector.ext
  intro k hk
  simp only [Vector.getElem_ofFn, Machine.unitsNext, absUnits, absReg]
  rw [rNext_bytes s i hreset k hk]
  by_cases hb : bitAt i.rWe k = true <;> simp [hb, ShifterB.bv_toNat]

/-! #### The winner's ALU fields -/

theorem winnerWa_eq_slot (s : Acc.State) (i : Acc.Input) (m : Nat) (hm : m < 6)
    (h : i.hit = (1 : BitVec 6) <<< m) :
    Acc.winnerWa s i = (Acc.alu s.a s.c (Acc.opSel i m) (Acc.opData i m)).wa := by
  have hh := congrArg Acc.Alu.wa (Acc.winnerResult_eq_slot s i m hm h)
  simpa only [Acc.winnerResult, Acc.slot] using hh

theorem winnerWc_eq_slot (s : Acc.State) (i : Acc.Input) (m : Nat) (hm : m < 6)
    (h : i.hit = (1 : BitVec 6) <<< m) :
    Acc.winnerWc s i = (Acc.alu s.a s.c (Acc.opSel i m) (Acc.opData i m)).wc := by
  have hh := congrArg Acc.Alu.wc (Acc.winnerResult_eq_slot s i m hm h)
  simpa only [Acc.winnerResult, Acc.slot] using hh

theorem winnerCy_eq_slot (s : Acc.State) (i : Acc.Input) (m : Nat) (hm : m < 6)
    (h : i.hit = (1 : BitVec 6) <<< m) :
    Acc.winnerCy s i = (Acc.alu s.a s.c (Acc.opSel i m) (Acc.opData i m)).cy := by
  have hh := congrArg Acc.Alu.cy (Acc.winnerResult_eq_slot s i m hm h)
  simpa only [Acc.winnerResult, Acc.slot] using hh

theorem winnerZ_eq_slot (s : Acc.State) (i : Acc.Input) (m : Nat) (hm : m < 6)
    (h : i.hit = (1 : BitVec 6) <<< m) :
    Acc.winnerZ s i = (Acc.alu s.a s.c (Acc.opSel i m) (Acc.opData i m)).z := by
  have hh := congrArg Acc.Alu.z (Acc.winnerResult_eq_slot s i m hm h)
  simpa only [Acc.winnerResult, Acc.slot] using hh

theorem winnerN_eq_slot (s : Acc.State) (i : Acc.Input) (m : Nat) (hm : m < 6)
    (h : i.hit = (1 : BitVec 6) <<< m) :
    Acc.winnerN s i = (Acc.alu s.a s.c (Acc.opSel i m) (Acc.opData i m)).n := by
  have hh := congrArg Acc.Alu.n (Acc.winnerResult_eq_slot s i m hm h)
  simpa only [Acc.winnerResult, Acc.slot] using hh

theorem winnerRes_eq_slot (s : Acc.State) (i : Acc.Input) (m : Nat) (hm : m < 6)
    (h : i.hit = (1 : BitVec 6) <<< m) :
    Acc.winnerRes s i = (Acc.alu s.a s.c (Acc.opSel i m) (Acc.opData i m)).res := by
  have hh := congrArg Acc.Alu.res (Acc.winnerResult_eq_slot s i m hm h)
  simpa only [Acc.winnerResult, Acc.slot] using hh

/-! #### The step theorems -/

/-- No hit: the machine holds `A`, `Z`, `C`, `N`, and the bank bytes are the
cut's (unchanged) four registers. -/
theorem Agrees_hit0 (cfg : Machine.Config) (s : Acc.State) (i : Acc.Input)
    (hreset : i.resetN = true) (h : i.hit = 0) :
    Agrees (mstep cfg s (absInNone i)) s i := by
  refine ⟨?_, ?_, ?_, ?_, r_eq_units cfg s i hreset (absInNone i) rfl⟩
  · simp [mstep, Machine.unitsNext, absUnits, absInNone, Acc.aNext, Acc.winnerWa, h, hreset,
      ShifterB.bv_toNat]
  · simp [mstep, Machine.unitsNext, absUnits, absInNone, Acc.zNext, h, hreset]
  · simp [mstep, Machine.unitsNext, absUnits, absInNone, Acc.cNext, Acc.winnerWc, h, hreset]
  · simp [mstep, Machine.unitsNext, absUnits, absInNone, Acc.nNext, h, hreset]

/-- One-hot at slot `m`: the machine step reproduces all five fields. -/
theorem Agrees_slot (cfg : Machine.Config) (s : Acc.State) (i : Acc.Input) (m : Nat)
    (hm : m < 6) (h : i.hit = (1 : BitVec 6) <<< m) (hreset : i.resetN = true)
    (h7 : Acc.opSel i m ≠ 7) : Agrees (mstep cfg s (absInSlot i m)) s i := by
  have hwa := winnerWa_eq_slot s i m hm h
  have hwc := winnerWc_eq_slot s i m hm h
  have hcy := winnerCy_eq_slot s i m hm h
  have hz := winnerZ_eq_slot s i m hm h
  have hn := winnerN_eq_slot s i m hm h
  have hr := winnerRes_eq_slot s i m hm h
  have hne : i.hit ≠ 0 := by rw [h]; exact onehot_ne_zero m hm
  refine ⟨?_, ?_, ?_, ?_, r_eq_units cfg s i hreset (absInSlot i m) rfl⟩
  · simp only [mstep, Machine.unitsNext, absUnits, absInSlot]
    rw [accNext_eq s.a (Acc.opData i m) s.c s.z s.n (Acc.opSel i m) h7]
    simp only [Acc.aNext, hreset, Bool.not_true, Bool.false_eq_true, if_false]
    rw [hwa, hr, ShifterB.bv_toNat]
  · simp only [mstep, Machine.unitsNext, absUnits, absInSlot]
    rw [accNext_eq s.a (Acc.opData i m) s.c s.z s.n (Acc.opSel i m) h7]
    simp only [Acc.zNext, hreset, Bool.not_true, Bool.false_eq_true, if_false]
    rw [if_neg hne, hz]
  · simp only [mstep, Machine.unitsNext, absUnits, absInSlot]
    rw [accNext_eq s.a (Acc.opData i m) s.c s.z s.n (Acc.opSel i m) h7]
    simp only [Acc.cNext, hreset, Bool.not_true, Bool.false_eq_true, if_false]
    rw [hwc, hcy]
  · simp only [mstep, Machine.unitsNext, absUnits, absInSlot]
    rw [accNext_eq s.a (Acc.opData i m) s.c s.z s.n (Acc.opSel i m) h7]
    simp only [Acc.nNext, hreset, Bool.not_true, Bool.false_eq_true, if_false]
    rw [if_neg hne, hn]

/-- The one-hot slot form with the winner's op code and data. -/
theorem abs_step_slot (cfg : Machine.Config) (s : Acc.State) (i : Acc.Input) (m : Nat)
    (hm : m < 6) (h : i.hit = (1 : BitVec 6) <<< m) (hreset : i.resetN = true)
    (h7 : i.hit = 0 ∨ winnerSel i ≠ 7) : Agrees (mstep cfg s (absIn i)) s i := by
  have h7' : Acc.opSel i m ≠ 7 := by
    rcases h7 with h0 | hs
    · rw [h] at h0
      exact absurd h0 (onehot_ne_zero m hm)
    · rwa [winnerSel_eq_slot i m hm h] at hs
  rw [absIn_slot i m hm h]
  exact Agrees_slot cfg s i m hm h hreset h7'

/-- **Accumulator bridge (all five fields).**  Under the §6 `OneHotOrZero`
write-group contract and the code-7 side condition (the cut's unreachable
`default:` reading), one machine `unitsNext` step on the mapped write groups
reproduces the cut's `A`, `Z`, `C`, `N` and the four `Rk` scratch bytes. -/
theorem abs_step (cfg : Machine.Config) (s : Acc.State) (i : Acc.Input)
    (hreset : i.resetN = true) (hhot : Acc.OneHotOrZero i.hit)
    (h7 : i.hit = 0 ∨ winnerSel i ≠ 7) : Agrees (mstep cfg s (absIn i)) s i := by
  rcases hhot with h | h | h | h | h | h | h
  · rw [absIn_none i h]
    exact Agrees_hit0 cfg s i hreset h
  · exact abs_step_slot cfg s i 0 (by decide) (by simpa using h) hreset h7
  · exact abs_step_slot cfg s i 1 (by decide) (by simpa using h) hreset h7
  · exact abs_step_slot cfg s i 2 (by decide) (by simpa using h) hreset h7
  · exact abs_step_slot cfg s i 3 (by decide) (by simpa using h) hreset h7
  · exact abs_step_slot cfg s i 4 (by decide) (by simpa using h) hreset h7
  · exact abs_step_slot cfg s i 5 (by decide) (by simpa using h) hreset h7

end AccB

end Metronome.Bridge
