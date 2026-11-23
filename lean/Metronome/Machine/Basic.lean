/-
Bit helpers for the machine specification (pure plumbing, no SPEC clause of its own).
§1 conventions: unsigned arithmetic, `{a,b}` concatenation with `a` most significant, `popcount`.
-/

namespace Metronome.Machine.Util

/-- Bit `i` of a bit vector (0 when out of range). -/
@[inline] def bit {n : Nat} (x : BitVec n) (i : Nat) : Bool := x.getLsbD i

/-- Bit `i` of a natural number. -/
@[inline] def nbit (x : Nat) (i : Nat) : Bool := (x >>> i) % 2 == 1

/-- Bits `lsb .. lsb+w-1` of a natural number. -/
@[inline] def nbits (x : Nat) (lsb w : Nat) : Nat := (x >>> lsb) % (2 ^ w)

/-- A bit vector from a natural number (reduced mod 2^n). -/
@[inline] def bv (n : Nat) (x : Nat) : BitVec n := BitVec.ofNat n x

/-- Bool as 0/1. -/
@[inline] def b2n (b : Bool) : Nat := if b then 1 else 0

/-- Set bit `i` of a bit vector to `v`. -/
def setBit {n : Nat} (x : BitVec n) (i : Nat) (v : Bool) : BitVec n :=
  let m := 2 ^ i
  let base := x.toNat - (if bit x i then m else 0)
  bv n (base + (if v then m else 0))

/-- Replace byte `k` (bits 8k+7..8k) of a bit vector. -/
def setByte {n : Nat} (x : BitVec n) (k : Nat) (b : Nat) : BitVec n :=
  let m := 2 ^ (8 * k)
  let old := nbits x.toNat (8 * k) 8
  bv n (x.toNat - old * m + (b % 256) * m)

/-- Byte `k` of a bit vector. -/
@[inline] def getByte {n : Nat} (x : BitVec n) (k : Nat) : Nat := nbits x.toNat (8 * k) 8

/-- §1 `popcount`. -/
def popcount (x : Nat) : Nat :=
  (List.range 32).foldl (fun acc i => acc + b2n (nbit x i)) 0

/-- Pack a list of booleans, element i into bit i. -/
def packBits (bs : List Bool) : Nat :=
  bs.foldr (fun b acc => acc * 2 + b2n b) 0

/-- Vector element with a runtime index (default when out of range). -/
@[inline] def vget {α : Type} {n : Nat} [Inhabited α] (v : Vector α n) (i : Nat) : α := v[i]!

/-- Vector update with a runtime index (unchanged when out of range). -/
@[inline] def vset {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (a : α) : Vector α n := v.set! i a

/-- Byte of a byte array (0 when out of range). -/
@[inline] def bget (a : ByteArray) (i : Nat) : Nat := (a.get! i).toNat

/-- Little-endian word of `w` bytes at byte address `base`. -/
def bgetLE (a : ByteArray) (base w : Nat) : Nat :=
  (List.range w).foldr (fun k acc => acc * 256 + bget a (base + k)) 0

/-- Write one byte (no effect when out of range). -/
@[inline] def bset (a : ByteArray) (i : Nat) (v : Nat) : ByteArray :=
  if i < a.size then a.set! i (UInt8.ofNat (v % 256)) else a

/-- A zero-filled byte array. -/
def bzero (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 0)

end Metronome.Machine.Util
