import Metronome.ChipCut.Discharge.MoveFabricKeyed

namespace Metronome.ChipCut.Discharge.PremiseWire

open Metronome

theorem six_slice (x0 x1 x2 x3 x4 x5 : BitVec 5) (q : Nat) (hq : q < 6) :
    CoreCtl.slice (BitVec.setWidth 30 x0 ||| BitVec.shiftLeft (BitVec.setWidth 30 x1) 5 |||
      BitVec.shiftLeft (BitVec.setWidth 30 x2) 10 |||
      BitVec.shiftLeft (BitVec.setWidth 30 x3) 15 |||
      BitVec.shiftLeft (BitVec.setWidth 30 x4) 20 |||
      BitVec.shiftLeft (BitVec.setWidth 30 x5) 25) (5 * q) 5
    = (match q with | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | 4 => x4 | _ => x5) := by
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold CoreCtl.slice
    bv_decide

end Metronome.ChipCut.Discharge.PremiseWire
