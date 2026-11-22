import Metronome.ChipCut.Discharge.DbgMapWire

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Metronome.ChipCut.Discharge.DbgMapWire

open Metronome

/-- No `DBG`-window address is a configuration address. -/
theorem isCfgAddr_false_of (a : Nat) (h : 0x21E0 ≤ a) :
    Machine.Config.isCfgAddr a = false := by
  rcases hc : Machine.Config.isCfgAddr a with _ | _
  · rfl
  · have hw := Bridge.CfgWrite.isCfgAddr_window a hc
    omega

example : Machine.Config.isCfgAddr 0x2469 = false := isCfgAddr_false_of 0x2469 (by decide)

example : (Machine.hostLocate 0x2469).map (fun l => (l.blk, l.inst, l.reg, l.byte)) =
    some ("DBG", 0, "EMASK", 1) := by decide

example : Strobes.hostDbg (hwDbg (witState Contents.init 0x2469 0x2468))
    (dbgOff (witState Contents.init 0x2469 0x2468).hostCmd.addr) 8 = false := by
  simp [hwDbg, witState, witHostCmd, Strobes.hostDbg, dbgOff, inDbg]

example : Bridge.Debug.hostOpt2
    (Bridge.Debug.emaskPort0 (dbgCtrlIn (witState Contents.init 0x2469 0x2468) ⟨0, 0, true⟩))
    (Bridge.Debug.emaskPort1 (dbgCtrlIn (witState Contents.init 0x2469 0x2468) ⟨0, 0, true⟩))
    = some (0, 0x5A) := by
  simp [Bridge.Debug.hostOpt2, Bridge.Debug.emaskPort0, Bridge.Debug.emaskPort1,
    Bridge.Debug.Port, dbgCtrlIn, hwIsSome, hwData, Strobes.dbgByteWrite, Strobes.hostDbg,
    Strobes.cwDbgOff, dbgOff, hwDbg, inDbg, cwDrain, Machine.Util.hwAt, witState, witHostCmd,
    witCq, resetState, if_true]
  decide

end Metronome.ChipCut.Discharge.DbgMapWire
