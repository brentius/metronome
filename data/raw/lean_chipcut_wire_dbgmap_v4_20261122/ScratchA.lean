import Metronome.ChipCut.Discharge.StreamDbg

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Metronome.ChipCut.Discharge

open Metronome

/-- The machine's host write of the cycle, only through `m.host`. -/
theorem machHw_eq' (m : Machine.State) :
    machHw m = (if m.host.wPend then
      some ⟨m.host.addr.toNat, m.host.wData.toNat, Machine.hostLocate m.host.addr.toNat⟩
      else none) := rfl

theorem machHw_eq_hwOf {s : State} {m : Machine.State} (hrel : ChipRel s m) (hinv : Inv s) :
    machHw m = hwOf s := by
  obtain ⟨-, -, -, -, ha5, ha6, ha7, -, -⟩ := hinv.hostAgrees
  obtain ⟨-, -, -, -, -, -, haddr, hwr, hwd, -, -⟩ := hrel.host.base
  have hwr' : m.host.wPend = s.hostRead.wr := hwr.symm
  have haddr' : m.host.addr = s.hostRead.addr := haddr.symm
  have hwd' : s.hostRead.wr = true → s.hostRead.wdata = m.host.wData := hwd
  rw [machHw_eq', hwr', haddr', hwOf]
  simp only [← ha5, ← ha6, ← ha7]
  by_cases hw : s.hostRead.wr = true
  · rw [if_pos hw, if_pos hw, hwd' hw]
  · rw [if_neg hw, if_neg hw]

end Metronome.ChipCut.Discharge
