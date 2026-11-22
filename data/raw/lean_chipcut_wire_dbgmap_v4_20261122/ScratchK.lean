import Metronome.ChipCut.Discharge.Glue

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Metronome.ChipCut.Discharge.DbgMapWire

open Metronome

example (a : BitVec 16) (h : a.toNat = 9314) : a = 0x2462 := by
  have hnum : (0x2462 : BitVec 16).toNat = 9314 := by decide
  exact BitVec.eq_of_toNat_eq (by rw [h, hnum])

example (a : BitVec 16) (h : a.toNat = 9314) : a = 0x2462 := by
  apply BitVec.eq_of_toNat_eq
  rw [h]
  decide

end Metronome.ChipCut.Discharge.DbgMapWire
