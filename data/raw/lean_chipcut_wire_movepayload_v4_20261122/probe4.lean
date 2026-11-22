import Metronome.ChipCut.Discharge.MemHostCfg

set_option autoImplicit false

namespace Probe

open Metronome

def cwMoveOf : Machine.DstOp → Option Nat
  | .cwAl => some 0
  | .cwAh => some 1
  | .cwD => some 2
  | _ => none

def cwSel (dst : BitVec 6) : Option Nat :=
  if dst == (60 : BitVec 6) then some 2
  else if dst == (58 : BitVec 6) then some 0
  else if dst == (59 : BitVec 6) then some 1 else none

example : cwSel (58 : BitVec 6) = some 0 := by decide
example : cwMoveOf (Machine.dstOp 58) = some 0 := by decide
example : cwMoveOf (Machine.dstOp 58) = cwSel (58 : BitVec 6) := by decide
example : cwMoveOf (Machine.dstOp 59) = cwSel (59 : BitVec 6) := by decide
example : cwMoveOf (Machine.dstOp 60) = cwSel (60 : BitVec 6) := by decide
example : cwMoveOf (Machine.dstOp 5) = cwSel (5 : BitVec 6) := by decide

end Probe
