import Metronome.ChipCut.Discharge.HostPinWire

open Metronome

example (a b : Bool) :
    Debug.bitAt ((if a then (1 : BitVec 1) else 0) ++ (if b then (1 : BitVec 1) else 0)) 0 = a := by
  cases a <;> cases b <;> decide

example (a b : Bool) :
    Debug.bitAt ((if a then (1 : BitVec 1) else 0) ++ (if b then (1 : BitVec 1) else 0)) 0 = b := by
  cases a <;> cases b <;> decide
