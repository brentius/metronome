import Metronome.ChipCut.Discharge.LineThread

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Metronome.ChipCut.Discharge

open Metronome

example (o : Option Nat) (a b c : Bool) :
    (match o.map (fun v => v % 8) with
      | some v => (Machine.Util.nbit v 0, Machine.Util.nbit v 1, Machine.Util.nbit v 2)
      | none => (a, b, c)) =
    (match o with
      | some v => (Machine.Util.nbit v 0, Machine.Util.nbit v 1, Machine.Util.nbit v 2)
      | none => (a, b, c)) := by
  rw [ctlTriple_mod8]

example (o : Option Nat) (r0 a0 : Bool) (ren : BitVec 3) :
    (fun p : Bool × Bool × BitVec 3 => p) 
      (match o.map (fun v => v % 8) with
        | some v => (Machine.Util.nbit v 0, Machine.Util.nbit v 1, Machine.Util.nbit v 2)
        | none => (r0, a0, ren)) =
    (fun p : Bool × Bool × BitVec 3 => p)
      (match o with
        | some v => (Machine.Util.nbit v 0, Machine.Util.nbit v 1, Machine.Util.nbit v 2)
        | none => (r0, a0, ren)) := by
  rw [ctlTriple_mod8]

end Metronome.ChipCut.Discharge
