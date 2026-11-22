import Metronome.Machine
import Metronome.HostRead

set_option autoImplicit false

open Metronome

#check @Nat.and_two_pow_sub_one_eq_mod
#check @Nat.land
#check @Nat.land_comm
#check @Nat.land_assoc
#check @Nat.land_eq
#check @Nat.testBit_eq_decide_div_mod_eq

namespace Probe5

theorem nbit_eq_bit_seven (x : BitVec 8) :
    Machine.Util.nbit x.toNat 7 = Machine.Util.bit x 7 := by
  unfold Machine.Util.nbit Machine.Util.bit
  rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat,
    Nat.testBit_eq_decide_div_mod_eq]
  show ((x.toNat >>> 7) % 2 == 1) = decide (x.toNat / 2 ^ 7 % 2 = 1)
  rw [Nat.shiftRight_eq_div_pow, beq_iff_eq]
  rfl

theorem bitAt_eq_bit_seven (x : BitVec 8) :
    HostRead.bitAt x 7 = Machine.Util.bit x 7 := by
  rw [← nbit_eq_bit_seven]
  rw [Bool.eq_iff_iff]
  unfold HostRead.bitAt Machine.Util.nbit
  rw [bne_iff_ne, ne_eq, BitVec.toNat_eq]
  rw [show ((0 : BitVec 8)).toNat = 0 from rfl]
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  rw [show (1 : Nat) % 2 ^ 8 = 1 from by decide]
  rw [Nat.and_two_pow_sub_one_eq_mod (m := 1)]
  rw [Nat.shiftRight_eq_div_pow]
  have hmod : ((x.toNat / 2 ^ 7) % 2 == 1) = decide (x.toNat / 2 ^ 7 % 2 = 1) := by
    rw [beq_iff_eq]; rfl
  rw [hmod, decide_eq_true_eq, decide_eq_true_eq]

end Probe5
