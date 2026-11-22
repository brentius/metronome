import Metronome.Machine

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

open Metronome

namespace Probe9

def blockOk : String × Nat × Nat × Nat × Array (Nat × String × Nat × String) → Bool
  | (name, base, stride, inst, regs) =>
      !(Machine.Util.cfgBlockNames.contains name) ||
        (0x2000 ≤ base && regs.toList.all (fun (off, _, bytes, acc) =>
          !(acc == "W") || (base + stride * (inst - 1) + off + bytes ≤ 0x21E0)))

theorem blockOk_all : Machine.Tables.hostBlocks.toList.all blockOk = true := by decide

theorem isCfgAddr_list (a : Nat) :
    Machine.Config.isCfgAddr a =
      Machine.Tables.hostBlocks.toList.any (fun (name, base, stride, inst, regs) =>
        Machine.Util.cfgBlockNames.contains name &&
          (List.range inst).any fun i =>
            regs.any fun (off, _, bytes, acc) =>
              acc == "W" && decide (base + stride * i + off ≤ a) &&
                decide (a < base + stride * i + off + bytes)) := by
  unfold Machine.Config.isCfgAddr
  rw [← Array.any_toList]

theorem isCfgAddr_window (a : Nat) (h : Machine.Config.isCfgAddr a = true) :
    0x2000 ≤ a ∧ a < 0x21E0 := by
  rw [isCfgAddr_list, List.any_eq_true] at h
  obtain ⟨b, hb, hp⟩ := h
  have hshape := (List.all_eq_true.mp blockOk_all) b hb
  obtain ⟨name, base, stride, inst, regs⟩ := b
  simp only [blockOk] at hshape
  rw [Bool.and_eq_true] at hp
  obtain ⟨hname, hinner⟩ := hp
  rw [Bool.or_eq_true] at hshape
  rcases hshape with hnone | hsome
  · rw [hname] at hnone; exact absurd hnone (by simp)
  · rw [Bool.and_eq_true] at hsome
    obtain ⟨hbase, hall⟩ := hsome
    rw [List.any_eq_true] at hinner
    obtain ⟨i, hi, hq⟩ := hinner
    have hi' : i < inst := List.mem_range.mp hi
    rw [← Array.any_toList, List.any_eq_true] at hq
    obtain ⟨reg, hreg, hs⟩ := hq
    obtain ⟨off, rname, bytes, acc⟩ := reg
    simp only at hs
    rw [Bool.and_eq_true, Bool.and_eq_true] at hs
    obtain ⟨⟨hacc, hlo⟩, hup⟩ := hs
    have hall' := (List.all_eq_true.mp hall) (off, rname, bytes, acc) hreg
    simp only at hall'
    rw [Bool.or_eq_true] at hall'
    rcases hall' with hbad | hgood
    · rw [hacc] at hbad; exact absurd hbad (by simp)
    · have hi2 : i ≤ inst - 1 := by omega
      have hmul : stride * i ≤ stride * (inst - 1) := Nat.mul_le_mul_left stride hi2
      simp only [decide_eq_true_eq] at hlo hup hbase hgood
      omega

end Probe9
