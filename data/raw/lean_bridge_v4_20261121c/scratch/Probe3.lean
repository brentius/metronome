import Metronome.Machine
import Metronome.HostRead

set_option autoImplicit false

open Metronome

namespace Probe3

example (x : BitVec 8) :
    x <<< 1 = Machine.Util.bv 8 ((x.toNat * 2) % 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Machine.Util.bv, BitVec.toNat_ofNat]
  omega

example (x : BitVec 8) : Machine.Util.bit x 7 = x.getLsbD 7 := rfl

example (x : BitVec 8) : x.getLsbD 7 = x.toNat.testBit 7 := by
  rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat]

example (x : BitVec 8) : HostRead.bitAt x 7 = x.toNat.testBit 7 := by
  simp only [HostRead.bitAt, Nat.testBit_eq_decide_div_mod_eq]
  rw [bne_iff_ne]
  -- LHS: ((x >>> 7) &&& 1 != 0)
  have hzero : ((x >>> 7) &&& (1 : BitVec 8)) = 0 ↔ ((x >>> 7) &&& (1 : BitVec 8)).toNat = 0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq (by rw [h]; rfl)
  rw [hzero]
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight]
  -- goal about Nat
  have h1 : (x.toNat >>> 7) &&& 1 < 2 := by
    sorry
  sorry

end Probe3
