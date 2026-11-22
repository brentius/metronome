import Metronome.Machine

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

open Metronome

namespace Probe8

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
  rfl

end Probe8
