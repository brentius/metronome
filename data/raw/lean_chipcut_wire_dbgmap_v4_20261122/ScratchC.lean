import Metronome.ChipCut.Discharge.DbgMapWire

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Metronome.ChipCut.Discharge.DbgMapWire

open Metronome

/-- A host write of `EMASK` byte 1 and a drained core write of byte 0: the
machine's host half is byte 1, the cut's `EMASK` host-selected byte port 0 is
also "host" (`hEm0` is register-level), so `hostOpt2` returns byte 0. -/
theorem dbgHEH_false :
    ∃ (s : State) (m : Machine.State) (pin : Machine.PinIn),
      ChipRel s m ∧ Inv s ∧ runRst s pin = true ∧
      Machine.Util.hwAt (machHw m) "DBG" 0 "EMASK" ≠
        Bridge.Debug.hostOpt2 (Bridge.Debug.emaskPort0 (dbgCtrlIn s pin))
          (Bridge.Debug.emaskPort1 (dbgCtrlIn s pin)) :=
  ⟨witState Contents.init 0x2469 0x2468, absChip (witState Contents.init 0x2469 0x2468),
    ⟨0, 0, true⟩, wit_chipRel _ _ _, wit_inv _ _ _, wit_runRst _ _ _, by decide⟩

end Metronome.ChipCut.Discharge.DbgMapWire
