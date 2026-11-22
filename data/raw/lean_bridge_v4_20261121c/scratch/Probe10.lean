import Metronome.Machine
import Metronome.HostRead

set_option autoImplicit false

open Metronome

namespace Probe10

theorem nbit_eq_bit_seven (x : BitVec 8) :
    Machine.Util.nbit x.toNat 7 = Machine.Util.bit x 7 := by
  unfold Machine.Util.nbit Machine.Util.bit
  rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat,
    Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rw [show (x.toNat / 2 ^ 7 % 2 == 1) = decide (x.toNat / 2 ^ 7 % 2 = 1) from by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]]

theorem bitAt_eq_nbit_seven (x : BitVec 8) :
    HostRead.bitAt x 7 = Machine.Util.nbit x.toNat 7 := by
  rw [Bool.eq_iff_iff, HostRead.bitAt, Machine.Util.nbit, bne_iff_ne, beq_iff_eq]
  rw [ne_eq, BitVec.toNat_eq]
  rw [show ((0 : BitVec 8)).toNat = 0 from rfl]
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight]
  rw [show (1 : BitVec 8).toNat = 1 from rfl]
  rw [show (1 : Nat) = 2 ^ 1 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.shiftRight_eq_div_pow]
  constructor <;> intro h <;> omega

theorem bit_seven_eq_bitAt (x : BitVec 8) :
    Machine.Util.bit x 7 = HostRead.bitAt x 7 := by
  rw [← nbit_eq_bit_seven, bitAt_eq_nbit_seven]

theorem pinsOut_miso (m : Machine.State) :
    (Machine.pinsOut m).1 % 2 = Machine.Util.b2n (Machine.Util.bit m.host.tx 7) := by
  simp only [Machine.pinsOut, Machine.Util.b2n]
  by_cases hb : Machine.Util.bit m.host.tx 7 <;> simp [hb] <;> omega

end Probe10
