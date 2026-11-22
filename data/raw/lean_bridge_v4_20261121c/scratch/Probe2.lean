import Metronome.Machine
import Metronome.HostRead

set_option autoImplicit false

open Metronome

#check @BitVec.getLsbD
#check @BitVec.getElem
#check @BitVec.getLsbD_eq_getElem
#check @BitVec.getElem_eq_testBit_toNat
#check @BitVec.getLsbD_eq_testBit
#check @Nat.testBit
#check @BitVec.toNat_shiftLeft
#check @Nat.shiftLeft_eq
#check @BitVec.toNat_and
#check @BitVec.toNat_ushiftRight
#check @Nat.and_one
#check @Nat.testBit_eq_decide_div_mod_eq
#check @Nat.testBit_eq
#check @BitVec.getLsbD_ushiftRight
#check @BitVec.getLsbD_and
#check @BitVec.getLsbD_zero
#check @BitVec.getLsbD_one
#check @BitVec.getElem_ushiftRight
#check @BitVec.getElem_and
#check @BitVec.getElem_one
#check @BitVec.toNat_eq
#check @BitVec.eq_of_toNat_eq
#check @Machine.Util.bit
