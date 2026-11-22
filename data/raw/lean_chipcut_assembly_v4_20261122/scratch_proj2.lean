import Metronome.ChipCut.Discharge.LineThread

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Metronome.ChipCut.Discharge

open Metronome

def lineInTrunc' (i : Machine.LineIn) : Machine.LineIn where
  sym := i.sym.map (fun w => { w with v := w.v % 16 })
  ctlMove := i.ctlMove.map (fun v => v % 8)
  hPhase := i.hPhase
  hCtl := i.hCtl
  hTapmissClr := i.hTapmissClr

theorem lineNext_truncD (c : Machine.LineCfg) (st : Machine.LineSt) (cb : Machine.LineComb)
    (p : Machine.PinView) (f : Bool) (i : Machine.LineIn) :
    Machine.lineNext c st cb p i f = Machine.lineNext c st cb p (lineInTrunc' i) f := by
  obtain ⟨sy, ct, ph, hc, ht⟩ := i
  cases sy <;> cases ct <;>
    simp only [Machine.lineNext, lineInTrunc', bv4_mod16, nbit_mod8_0, nbit_mod8_1,
      nbit_mod8_2, Option.map_none, Option.map_some, stagedNext_mod16_some] <;>
    rfl

end Metronome.ChipCut.Discharge
