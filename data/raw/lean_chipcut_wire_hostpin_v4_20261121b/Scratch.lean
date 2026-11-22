import Metronome.ChipCut.Discharge.HostPinWire

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

open Metronome

namespace Metronome.ChipCut.Discharge

/-- The concrete state: a completed host write of byte `0x5A` to
`LRT[0].PHASE` byte 0 (address `0x2410`). -/
def hPhaseState (cont : Contents) : State :=
  { resetState cont with
    hostCmd := { HostCmd.resetState with wr := true, addr := 0x2410, wdata := 0x5A }
    hostRead := { HostRead.resetState with wr := true, addr := 0x2410, wdata := 0x5A } }

/-- The machine side of the `PHASE` write decode: byte 0, data `0x5A`. -/
theorem hPhase_mach (cont : Contents) (pin : Machine.PinIn) :
    Machine.Util.hwAt (hwOf (hPhaseState cont)) "LRT" 0 "PHASE" = some (0, 0x5A) := by
  show Machine.Util.hwAt
    (some ⟨(0x2410 : Nat), (0x5A : Nat), Machine.hostLocate 0x2410⟩) "LRT" 0 "PHASE"
      = some (0, (0x5A : Nat))
  decide

/-- The cut side of the same write: `lineIn`'s `phWe` packs the byte-0 strobe
into **bit 1** (`a ++ b` puts `a` high), so `absIn` reads it as byte 1. -/
theorem hPhase_cut (cont : Contents) (pin : Machine.PinIn) :
    (Bridge.Line.absIn (lineIn (hPhaseState cont) pin 0)).hPhase = some (1, 0x5A) := by
  have hpw : (lineIn (hPhaseState cont) pin 0).phWe = (2 : BitVec 2) := by
    show ((if byteStrobe (Machine.Util.hwAt
          (some ⟨(0x2410 : Nat), (0x5A : Nat), Machine.hostLocate 0x2410⟩) "LRT" 0 "PHASE")
          0 then (1 : BitVec 1) else 0) ++
        (if byteStrobe (Machine.Util.hwAt
          (some ⟨(0x2410 : Nat), (0x5A : Nat), Machine.hostLocate 0x2410⟩) "LRT" 0 "PHASE")
          1 then (1 : BitVec 1) else 0)) = (2 : BitVec 2)
    decide
  have hd : (lineIn (hPhaseState cont) pin 0).hD = 0x5A := rfl
  simp only [Bridge.Line.absIn, hpw, hd]
  decide

/-- **`WireAgree.hPhase` is false.**  The two sides of the field disagree on a
plain `LRT[0].PHASE` byte-0 write: `ChipCut/Wire.lean`'s `phWe` is
`(byte-0 strobe) ++ (byte-1 strobe)`, i.e. the byte-0 strobe lands in bit 1,
while the cut's own `Line.phF` and `Bridge.Line.absIn` read bit 0 as byte 0.
`ltHw_eq` reduces the field's left side to the machine side below, so no
`WireAgree` holds for a related machine on such a cycle. -/
theorem hPhase_false (cont : Contents) (pin : Machine.PinIn) :
    ¬ ((Machine.Util.hwAt (hwOf (hPhaseState cont)) "LRT" 0 "PHASE") =
        (Bridge.Line.absIn (lineIn (hPhaseState cont) pin 0)).hPhase) := by
  intro h
  rw [hPhase_mach cont pin, hPhase_cut cont pin] at h
  exact absurd h (by decide)

end Metronome.ChipCut.Discharge
