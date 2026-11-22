import Metronome.ChipCut.Discharge.Glue

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Metronome.ChipCut.Discharge.DbgMapWire

open Metronome

example (a : BitVec 16) : Strobes.cwDbgOff a = BitVec.setWidth 32 (dbgOff a) := by
  unfold Strobes.cwDbgOff Strobes.haDbgBase dbgOff
  bv_decide

example (a : BitVec 16) (D : Nat) (hD : D < 0x20) (h : dbgOff a = BitVec.ofNat 16 D) :
    a = BitVec.ofNat 16 (0x2460 + D) := by
  bv_decide

example (a : BitVec 16) (n : Nat) (hn : n < 65536)
    (h : BitVec.setWidth 32 a = BitVec.ofNat 32 n) : a = BitVec.ofNat 16 n := by
  bv_decide

example (a : BitVec 16) (D : Nat) (h : Strobes.cwDbgOff a = BitVec.ofNat 32 D) : True := by
  trivial

end Metronome.ChipCut.Discharge.DbgMapWire
