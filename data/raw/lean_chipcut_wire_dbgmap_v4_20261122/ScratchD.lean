import Metronome.ChipCut.Discharge.DbgMapWire

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Metronome.ChipCut.Discharge.DbgMapWire

open Metronome

example : Machine.hostLocate 0x2469 = some ⟨"DBG", 0, "EMASK", 1, "RW"⟩ := by decide

example : Strobes.dbgByteWrite (hwDbg (witState Contents.init 0x2469 0x2468))
    (dbgOff (witState Contents.init 0x2469 0x2468).hostCmd.addr)
    (cwDrain (witState Contents.init 0x2469 0x2468))
    (witState Contents.init 0x2469 0x2468).cq.pendingAddr 8 = true := by decide

example : hwIsSome (witState Contents.init 0x2469 0x2468) "DBG" 0 "EMASK" = true := by decide

example : cwDrain (witState Contents.init 0x2469 0x2468) = true := by decide

example : Machine.Util.hwAt (hwOf (witState Contents.init 0x2469 0x2468)) "DBG" 0 "EMASK" =
    some (1, 0x5A) := by decide

example : Bridge.Debug.hostOpt2
    (Bridge.Debug.emaskPort0 (dbgCtrlIn (witState Contents.init 0x2469 0x2468) ⟨0, 0, true⟩))
    (Bridge.Debug.emaskPort1 (dbgCtrlIn (witState Contents.init 0x2469 0x2468) ⟨0, 0, true⟩))
    = some (0, 0x5A) := by decide

end Metronome.ChipCut.Discharge.DbgMapWire
