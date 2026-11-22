import Metronome.ChipCut.Discharge.HostPinWire

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

open Metronome

namespace Metronome.ChipCut.Discharge

/-- The concrete state of the historical `hPhase` witness: a completed host
write of byte `0x5A` to `LRT[0].PHASE` byte 0 (address `0x2410`). -/
def hPhaseState (cont : Contents) : State :=
  { resetState cont with
    hostCmd := { HostCmd.resetState with wr := true, addr := 0x2410, wdata := 0x5A }
    hostRead := { HostRead.resetState with wr := true, addr := 0x2410, wdata := 0x5A } }

/-- **The fixed `phWe` on the historical witness state.**  With
`ChipCut/Wire.lean`'s current `phWe = {byte-1 strobe, byte-0 strobe}` the cut
reads byte 0 of the very write that used to land in bit 1 — the two sides of
`WireAgree.hPhase` agree here (contrast `Section9.lean`'s `hPhase_false` for
the pre-fix text). -/
theorem hPhase_fixed (cont : Contents) (pin : Machine.PinIn) :
    (Machine.Util.hwAt (hwOf (hPhaseState cont)) "LRT" 0 "PHASE") =
      (Bridge.Line.absIn (lineIn (hPhaseState cont) pin 0)).hPhase := by
  have hm : Machine.Util.hwAt (hwOf (hPhaseState cont)) "LRT" 0 "PHASE"
      = some (0, 0x5A) := by
    show Machine.Util.hwAt
      (some ⟨(0x2410 : Nat), (0x5A : Nat), Machine.hostLocate 0x2410⟩) "LRT" 0 "PHASE"
        = some (0, (0x5A : Nat))
    decide
  have hpw : (lineIn (hPhaseState cont) pin 0).phWe = (1 : BitVec 2) := by
    show ((if byteStrobe (Machine.Util.hwAt
          (some ⟨(0x2410 : Nat), (0x5A : Nat), Machine.hostLocate 0x2410⟩) "LRT" 0 "PHASE")
          1 then (1 : BitVec 1) else 0) ++
        (if byteStrobe (Machine.Util.hwAt
          (some ⟨(0x2410 : Nat), (0x5A : Nat), Machine.hostLocate 0x2410⟩) "LRT" 0 "PHASE")
          0 then (1 : BitVec 1) else 0)) = (1 : BitVec 2)
    decide
  have hd : (lineIn (hPhaseState cont) pin 0).hD = 0x5A := rfl
  have hcut : (Bridge.Line.absIn (lineIn (hPhaseState cont) pin 0)).hPhase
      = some (0, 0x5A) := by
    simp only [Bridge.Line.absIn, hpw, hd]
    decide
  rw [hm, hcut]

end Metronome.ChipCut.Discharge
