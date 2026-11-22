import Metronome.ChipCut.Discharge.MoveFabricKeyed

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Metronome.ChipCut.Discharge.PremiseWire

open Metronome

/-- Six `5`-bit group words packed the way `Moves.mapOfWith` packs them. -/
def pack6 (x0 x1 x2 x3 x4 x5 : BitVec 5) : BitVec 30 :=
  BitVec.setWidth 30 x0 ||| BitVec.shiftLeft (BitVec.setWidth 30 x1) 5 |||
    BitVec.shiftLeft (BitVec.setWidth 30 x2) 10 |||
    BitVec.shiftLeft (BitVec.setWidth 30 x3) 15 |||
    BitVec.shiftLeft (BitVec.setWidth 30 x4) 20 |||
    BitVec.shiftLeft (BitVec.setWidth 30 x5) 25

/-- Slot `q`'s word of a six-word packing. -/
def grpAt (q : Nat) (x0 x1 x2 x3 x4 x5 : BitVec 5) : BitVec 5 :=
  match q with
  | 0 => x0
  | 1 => x1
  | 2 => x2
  | 3 => x3
  | 4 => x4
  | _ => x5

theorem pack6_slice (x0 x1 x2 x3 x4 x5 : BitVec 5) (q : Nat) (hq : q < 6) :
    CoreCtl.slice (pack6 x0 x1 x2 x3 x4 x5) (5 * q) 5 =
      grpAt q x0 x1 x2 x3 x4 x5 := by
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold CoreCtl.slice grpAt pack6
    bv_decide

theorem mapOfWith_slice (tab : BitVec 320) (dst : BitVec 36) (q : Nat) (hq : q < 6) :
    CoreCtl.slice (Moves.mapOfWith tab dst) (5 * q) 5 =
      Moves.dgLookupAt tab (CoreCtl.slice dst (6 * q) 6) := by
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact pack6_slice (Moves.dgLookupAt tab (CoreCtl.slice dst 0 6))
      (Moves.dgLookupAt tab (CoreCtl.slice dst 6 6))
      (Moves.dgLookupAt tab (CoreCtl.slice dst 12 6))
      (Moves.dgLookupAt tab (CoreCtl.slice dst 18 6))
      (Moves.dgLookupAt tab (CoreCtl.slice dst 24 6))
      (Moves.dgLookupAt tab (CoreCtl.slice dst 30 6)) _ (by omega)

theorem grpPacked_holds (s : State) (pin : Machine.PinIn) :
    MoveFabricKeyed.GrpPacked s pin := by
  intro q hq
  have hg : ((MoveFabric.movBundle s pin).get q).group =
      CoreCtl.slice (mvGrp s pin) (5 * q) 5 :=
    MoveFabricKeyed.bundle_grp (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
      (mvXl s) (mvXt s) q hq
  have hd : ((MoveFabric.movBundle s pin).get q).dst =
      CoreCtl.slice (mvDst s pin) (6 * q) 6 :=
    MoveFabric.bundle_dst (mvEn s pin) (mvGrp s pin) (mvDst s pin) (mvDat s pin)
      (mvXl s) (mvXt s) q hq
  rw [hg, hd]
  exact mapOfWith_slice Moves.dgMapLiteral (mvDst s pin) q hq

end Metronome.ChipCut.Discharge.PremiseWire
