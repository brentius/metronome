import Metronome.ChipCut.Discharge.HostPinWire

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Metronome

namespace Metronome.ChipCut.Discharge

-- The packing order of a two-bit `++`.
example : Line.bitAt 0 (((1 : BitVec 1) ++ (0 : BitVec 1))) = false := by decide
example : Line.bitAt 1 (((1 : BitVec 1) ++ (0 : BitVec 1))) = true := by decide
example : Line.bitAt 0 (((0 : BitVec 1) ++ (1 : BitVec 1))) = true := by decide
example : Line.bitAt 1 (((0 : BitVec 1) ++ (1 : BitVec 1))) = false := by decide

-- The cut's `phWe` packs byte 0 first (high bit) and byte 1 second (low bit).
example : ((if true then (1 : BitVec 1) else 0) ++ (if false then (1 : BitVec 1) else 0))
    = (2 : BitVec 2) := by decide

-- `hostLocate` at the first `LRT.PHASE` byte.
example : (Machine.hostLocate 0x2410).map (fun l => (l.blk, l.inst, l.reg, l.byte))
    = some ("LRT", 0, "PHASE", (0 : Nat)) := by decide
example : (Machine.hostLocate 0x2411).map (fun l => (l.blk, l.inst, l.reg, l.byte))
    = some ("LRT", 0, "PHASE", (1 : Nat)) := by decide

end Metronome.ChipCut.Discharge
