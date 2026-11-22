import Metronome.Machine
import Metronome.HostRead

set_option autoImplicit false

open Metronome

#check @Nat.land_one_eq_mod_two
#check @Nat.and_one_eq_mod_two
#check @Nat.land_comm
#check @Nat.land_eq_min
#check @Nat.testBit_land
#check @Nat.land_two_pow_sub_one
#check @BitVec.getLsbD_of_ge
#check @BitVec.getLsbD_eq_getElem
#check @BitVec.getElem_eq_testBit_toNat
#check @BitVec.getLsbD_eq_testBit_toNat
#check @BitVec.ushiftRight_eq
#check @BitVec.ushiftRight_eq_zero
#check @BitVec.toNat_ushiftRight
#check @Nat.shiftRight_eq_div_pow
#check @Nat.mod_two_eq_zero_or_one
#check @beq_iff_eq
#check @decide_eq_true_eq
#check @Bool.eq_iff_iff
#check @bne_iff_ne
#check @BitVec.getLsbD_ushiftRight
#check @BitVec.getLsbD_and
#check @BitVec.getLsbD_one
#check @BitVec.zero_and
#check @BitVec.and_zero
