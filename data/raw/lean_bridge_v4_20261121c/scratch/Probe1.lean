import Metronome.Machine
import Metronome.HostRead

set_option autoImplicit false

namespace Probe1

open Metronome

example (x : BitVec 8) :
    x <<< 1 = Machine.Util.bv 8 ((x.toNat * 2) % 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Machine.Util.bv, BitVec.toNat_ofNat]
  norm_num

example (x : BitVec 8) : Machine.Util.bit x 7 = HostRead.bitAt x 7 := by
  simp [Machine.Util.bit, HostRead.bitAt]

example (x : BitVec 3) : (x.toNat < 7) ↔ x ≠ 7 := by
  omega

example (m : Machine.State) :
    (Machine.pinsOut m).1 % 2 = Machine.Util.b2n (Machine.Util.bit m.host.tx 7) := by
  simp only [Machine.pinsOut, Machine.Util.b2n]
  by_cases hb : Machine.Util.bit m.host.tx 7 <;> simp [hb] <;> omega

example (a : Nat) (h : Machine.Config.isCfgAddr a = true) : a < 0x21E0 := by
  simp only [Machine.Config.isCfgAddr, Machine.Util.cfgBlockNames, Machine.hostBlocks] at h
  simp only [List.contains_cons, List.contains_nil, Bool.false_eq_true, Bool.true_and,
    Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.any_cons, List.any_nil,
    List.range_succ, List.range_zero, List.mem_cons, List.not_mem_nil, reduceIte] at h
  omega

end Probe1
