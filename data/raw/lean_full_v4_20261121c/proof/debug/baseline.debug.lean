import Metronome.Debug

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 434c6ae6e52b85991f0be864394e5c93382f4aa239c9302ae0ef91d19dab2b3b
-- Elaboration: read_verilog -I src -D USE_IHP_SRAM; hierarchy -check; proc;
-- opt_clean.  Every cone below is the elaborated netlist, not the specification.

set_option autoImplicit false
set_option maxHeartbeats 8000000
-- A mutant may legitimately disconnect a bound leaf; the extraction's leaf-use
-- checks catch that, and the equivalence theorem then fails on the real cone.
set_option linter.unusedVariables false

namespace Metronome.Debug

namespace Pins

/-- The elaborated `rtlPinsLevel` cone. -/
def rtlPinsLevel (s2 : BitVec 16) (rlv emask : BitVec 13) (replay : Bool) : BitVec 13 :=
  let pins0 := (emask &&& ((if replay then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let pins1 := (~~~pins0)
  let pins2 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight (s2) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s2) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s2) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s2) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s2) 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s2) 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s2) 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s2) 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s2) 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s2) 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s2) 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s2) 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s2) 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))) &&& pins1)
  let pins3 := (rlv &&& emask &&& ((if replay then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let pins4 := (pins2 ||| pins3)
  pins4

/-- The elaborated `rtlPinsPrev` cone. -/
def rtlPinsPrev (sp : BitVec 16) (rlvPrev emask : BitVec 13) (replay : Bool) : BitVec 13 :=
  let pins0 := (emask &&& ((if replay then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let pins5 := (~~~pins0)
  let pins6 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight (sp) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (sp) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (sp) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (sp) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (sp) 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (sp) 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (sp) 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (sp) 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (sp) 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (sp) 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (sp) 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (sp) 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (sp) 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))) &&& pins5)
  let pins7 := (rlvPrev &&& emask &&& ((if replay then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if replay then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let pins8 := (pins6 ||| pins7)
  pins8

/-- The elaborated `rtlLvl` cone. -/
def rtlLvl (pl : BitVec 13) : BitVec 16 :=
  (0 : BitVec 3) ++ pl

/-- The elaborated `rtlRise` cone. -/
def rtlRise (pl pp : BitVec 13) : BitVec 16 :=
  let pins20 := (~~~pp)
  let pins21 := (pl &&& pins20)
  (0 : BitVec 3) ++ pins21

/-- The elaborated `rtlFall` cone. -/
def rtlFall (pl pp : BitVec 13) : BitVec 16 :=
  let pins22 := (~~~pl)
  let pins23 := (pins22 &&& pp)
  (0 : BitVec 3) ++ pins23

end Pins

namespace Digest

/-- The elaborated `rtlMen` cone. -/
def rtlMen (s : State) (i : Input) : Bool :=
  let digest0 := (if i.dWrMctl then ((BitVec.truncate 1 (BitVec.ushiftRight (i.hWd) 0)) != 0) else s.men)
  let digest1 := (if i.resetN then digest0 else false)
  digest1

/-- The elaborated `rtlMisr` cone. -/
def rtlMisr (s : State) (i : Input) : BitVec 32 :=
  let digest2 := (i.dWrMctl && ((BitVec.truncate 1 (BitVec.ushiftRight (i.hWd) 1)) != 0))
  let digest3 := (!i.frz)
  let digest4 := (s.men && digest3)
  let digest5 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 31)) != 0) then (79764919 : BitVec 32) else (0 : BitVec 32))
  let digest6 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 16)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 17)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 18)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 19)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 20)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 21)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 22)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 23)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 24)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 25)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 26)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 27)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 28)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 29)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (s.misr) 30)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) ^^^ digest5)
  let digest7 := (digest6 ^^^ ((BitVec.shiftLeft ((BitVec.setWidth 32) (i.oOut)) 0) ||| (BitVec.shiftLeft ((BitVec.setWidth 32) (i.oEe)) 14)))
  let digest8 := (if digest4 then digest7 else s.misr)
  let digest9 := (if digest2 then (0 : BitVec 32) else digest8)
  let digest10 := (if i.resetN then digest9 else (0 : BitVec 32))
  digest10

/-- The elaborated whole transition. -/
def rtlStep (s : State) (i : Input) : State :=
  ⟨rtlMen s i, rtlMisr s i⟩

end Digest

namespace Ctrl

/-- The elaborated `rtlTick` cone. -/
def rtlTick (dc : BitVec 19) : BitVec 20 :=
  let ctrlcomb0 := (((BitVec.shiftLeft ((BitVec.setWidth 20) (dc)) 0)) + (1 : BitVec 20))
  ctrlcomb0

/-- The elaborated `rtlInterval` cone. -/
def rtlInterval (rw : BitVec 32) : BitVec 20 :=
  ((if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 0) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 1) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 2) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 16)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 3) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 17)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 4) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 18)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 5) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 19)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 6) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 20)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 7) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 21)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 8) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 22)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 9) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 23)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 10) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 24)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 11) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 25)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 12) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 26)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 13) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 27)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 14) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 28)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 15) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 29)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 16) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 30)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 17) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 31)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 18) else (0 : BitVec 20)))

/-- The elaborated `rtlApply` cone. -/
def rtlApply (replay frz : Bool) (rv : BitVec 2) (dc : BitVec 19) (rw : BitVec 32) : Bool :=
  let ctrlcomb0 := (((BitVec.shiftLeft ((BitVec.setWidth 20) (dc)) 0)) + (1 : BitVec 20))
  let ctrlcomb1 := (!frz)
  let ctrlcomb2 := decide (ctrlcomb0 >= ((if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 0) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 1) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 2) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 16)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 3) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 17)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 4) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 18)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 5) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 19)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 6) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 20)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 7) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 21)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 8) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 22)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 9) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 23)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 10) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 24)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 11) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 25)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 12) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 26)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 13) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 27)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 14) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 28)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 15) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 29)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 16) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 30)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 17) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 31)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 18) else (0 : BitVec 20))))
  let ctrlcomb3 := (replay && ctrlcomb1 && ((BitVec.truncate 1 (BitVec.ushiftRight (rv) 0)) != 0) && ctrlcomb2)
  ctrlcomb3

/-- The elaborated `rtlLate` cone. -/
def rtlLate (replay frz : Bool) (rv : BitVec 2) (dc : BitVec 19) (rw : BitVec 32) : Bool :=
  let ctrlcomb0 := (((BitVec.shiftLeft ((BitVec.setWidth 20) (dc)) 0)) + (1 : BitVec 20))
  let ctrlcomb1 := (!frz)
  let ctrlcomb2 := decide (ctrlcomb0 >= ((if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 0) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 1) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 2) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 16)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 3) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 17)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 4) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 18)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 5) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 19)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 6) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 20)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 7) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 21)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 8) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 22)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 9) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 23)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 10) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 24)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 11) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 25)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 12) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 26)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 13) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 27)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 14) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 28)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 15) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 29)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 16) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 30)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 17) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 31)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 18) else (0 : BitVec 20))))
  let ctrlcomb4 := decide (ctrlcomb0 > ((if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 0) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 1) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 2) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 16)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 3) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 17)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 4) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 18)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 5) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 19)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 6) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 20)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 7) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 21)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 8) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 22)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 9) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 23)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 10) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 24)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 11) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 25)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 12) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 26)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 13) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 27)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 14) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 28)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 15) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 29)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 16) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 30)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 17) else (0 : BitVec 20)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (rw) 31)) != 0) then (BitVec.shiftLeft (1 : BitVec 20) 18) else (0 : BitVec 20))))
  let ctrlcomb5 := (replay && ctrlcomb1 && ((BitVec.truncate 1 (BitVec.ushiftRight (rv) 0)) != 0) && ctrlcomb2 && ctrlcomb4)
  ctrlcomb5

/-- The elaborated `rtlReplayLevels` cone. -/
def rtlReplayLevels (rlv emask : BitVec 13) (ap : Bool) (rw : BitVec 32) : BitVec 13 :=
  let ctrllevels0 := (~~~emask)
  let ctrllevels1 := (rlv &&& ctrllevels0)
  let ctrllevels2 := ((BitVec.truncate 13 (BitVec.ushiftRight (rw) 0)) &&& emask)
  let ctrllevels3 := (ctrllevels1 ||| ctrllevels2)
  let ctrllevels4 := (if ap then ctrllevels3 else rlv)
  ctrllevels4

/-- The elaborated `rtlCev` cone. -/
def rtlCev (cen replay frz : Bool) (rise fall : BitVec 16) (emask : BitVec 13) : Bool :=
  let ctrlcomb6 := (!replay)
  let ctrlcomb7 := (!frz)
  let ctrlcomb8 := ((BitVec.truncate 13 rise) ||| (BitVec.truncate 13 fall))
  let ctrlcomb9 := (ctrlcomb8 &&& emask)
  let ctrlcomb10 := (ctrlcomb9 != 0)
  let ctrlcomb11 := (cen && ctrlcomb6 && ctrlcomb7 && ctrlcomb10)
  ctrlcomb11

/-- The elaborated `rtlReplay` cone. -/
def rtlReplay (s : State) (i : Input) : Bool :=
  let ctrlregs0 := (if i.hEctl then (BitVec.truncate 2 (BitVec.ushiftRight (i.hWd) 0)) else (BitVec.truncate 2 (BitVec.ushiftRight (i.cwData) 0)))
  let ctrlregs1 := (if i.dWrEctl then ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs0) 1)) != 0) else s.replay)
  let ctrlregs2 := (if i.resetN then ctrlregs1 else false)
  ctrlregs2

/-- The elaborated `rtlCen` cone. -/
def rtlCen (s : State) (i : Input) : Bool :=
  let ctrlregs0 := (if i.hEctl then (BitVec.truncate 2 (BitVec.ushiftRight (i.hWd) 0)) else (BitVec.truncate 2 (BitVec.ushiftRight (i.cwData) 0)))
  let ctrlregs3 := (if i.dWrEctl then ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs0) 0)) != 0) else s.cen)
  let ctrlregs4 := (if i.resetN then ctrlregs3 else false)
  ctrlregs4

/-- The elaborated `rtlEmask` cone. -/
def rtlEmask (s : State) (i : Input) : BitVec 13 :=
  let ctrlregs5 := (if i.hEm0 then i.hWd else i.cwData)
  let ctrlregs6 := (if i.dWrEm0 then ctrlregs5 else (BitVec.truncate 8 (BitVec.ushiftRight (s.emask) 0)))
  let ctrlregs7 := (if i.resetN then ctrlregs6 else (0 : BitVec 8))
  let ctrlregs8 := (if i.hEm1 then (BitVec.truncate 5 (BitVec.ushiftRight (i.hWd) 0)) else (BitVec.truncate 5 (BitVec.ushiftRight (i.cwData) 0)))
  let ctrlregs9 := (if i.dWrEm1 then ctrlregs8 else (BitVec.truncate 5 (BitVec.ushiftRight (s.emask) 8)))
  let ctrlregs10 := (if i.resetN then ctrlregs9 else (0 : BitVec 5))
  ((if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs7) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs7) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs7) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs7) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs7) 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs7) 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs7) 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs7) 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs10) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs10) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs10) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs10) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs10) 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13)))

/-- The elaborated `rtlRlv` cone. -/
def rtlRlv (s : State) (i : Input) : BitVec 13 :=
  let ctrlregs11 := (if i.hRlv0 then i.hWd else i.cwData)
  let ctrlregs12 := (if i.dWrRlv0 then ctrlregs11 else (BitVec.truncate 8 (BitVec.ushiftRight ((replayLevels s.rlv s.emask (apply s.replay i.frz (bitAt i.replayValid 0) s.dc i.replayWord) i.replayWord)) 0)))
  let ctrlregs13 := (if i.resetN then ctrlregs12 else (0 : BitVec 8))
  let ctrlregs14 := (if i.hRlv1 then (BitVec.truncate 5 (BitVec.ushiftRight (i.hWd) 0)) else (BitVec.truncate 5 (BitVec.ushiftRight (i.cwData) 0)))
  let ctrlregs15 := (if i.dWrRlv1 then ctrlregs14 else (BitVec.truncate 5 (BitVec.ushiftRight ((replayLevels s.rlv s.emask (apply s.replay i.frz (bitAt i.replayValid 0) s.dc i.replayWord) i.replayWord)) 8)))
  let ctrlregs16 := (if i.resetN then ctrlregs15 else (0 : BitVec 5))
  ((if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs13) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs13) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs13) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs13) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs13) 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs13) 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs13) 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs13) 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs16) 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs16) 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs16) 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs16) 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight (ctrlregs16) 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13)))

/-- The elaborated `rtlRlvPrev` cone. -/
def rtlRlvPrev (s : State) (i : Input) : BitVec 13 :=
  let ctrlregs17 := (if i.frz then s.rlvPrev else s.rlv)
  let ctrlregs18 := (if i.resetN then ctrlregs17 else (0 : BitVec 13))
  ctrlregs18

/-- The elaborated `rtlDc` cone. -/
def rtlDc (s : State) (i : Input) : BitVec 19 :=
  let ctrlregs19 := (!s.replay)
  let ctrlregs20 := (!s.cen)
  let ctrlregs21 := (ctrlregs19 && ctrlregs20)
  let ctrlregs22 := ((apply s.replay i.frz (bitAt i.replayValid 0) s.dc i.replayWord) || ctrlregs21)
  let ctrlregs23 := (s.dc != (524287 : BitVec 19))
  let ctrlregs24 := (s.dc + (1 : BitVec 19))
  let ctrlregs25 := (if ctrlregs23 then ctrlregs24 else s.dc)
  let ctrlregs26 := (if (cev s.cen s.replay i.frz i.rise i.fall s.emask) then (1 : BitVec 19) else ctrlregs25)
  let ctrlregs27 := (if ctrlregs22 then (0 : BitVec 19) else ctrlregs26)
  let ctrlregs28 := (if i.frz then s.dc else ctrlregs27)
  let ctrlregs29 := (if i.dWrEctl then (0 : BitVec 19) else ctrlregs28)
  let ctrlregs30 := (if i.resetN then ctrlregs29 else (0 : BitVec 19))
  ctrlregs30

/-- The elaborated whole transition. -/
def rtlStep (s : State) (i : Input) : State :=
  ⟨rtlReplay s i, rtlCen s i, rtlEmask s i, rtlRlv s i, rtlRlvPrev s i, rtlDc s i⟩

end Ctrl

namespace Pmem

/-- The elaborated `rtlPmWe0` cone. -/
def rtlPmWe0 (hWr inPrg : Bool) (a : BitVec 16) : Bool :=
  let pmem0 := (!((BitVec.truncate 1 (BitVec.ushiftRight (a) 11)) != 0))
  let pmem1 := (hWr && inPrg && pmem0)
  pmem1

/-- The elaborated `rtlPmWe1` cone. -/
def rtlPmWe1 (hWr inPrg : Bool) (a : BitVec 16) : Bool :=
  let pmem2 := (hWr && inPrg && ((BitVec.truncate 1 (BitVec.ushiftRight (a) 11)) != 0))
  pmem2

/-- The elaborated `rtlPmBe` cone. -/
def rtlPmBe (a : BitVec 16) : BitVec 8 :=
  let pmem3 := (BitVec.shiftLeft (1 : BitVec 8) ((BitVec.truncate 3 (BitVec.ushiftRight (a) 0))).toNat)
  pmem3

/-- The elaborated `rtlPmAddr0` cone. -/
def rtlPmAddr0 (we0 : Bool) (a fadr : BitVec 16) : BitVec 8 :=
  let pmaddr0 := (if we0 then (BitVec.truncate 8 (BitVec.ushiftRight (a) 3)) else (BitVec.truncate 8 (BitVec.ushiftRight (fadr) 0)))
  pmaddr0

/-- The elaborated `rtlPmAddr1` cone. -/
def rtlPmAddr1 (we1 : Bool) (a fadr : BitVec 16) : BitVec 8 :=
  let pmaddr1 := (if we1 then (BitVec.truncate 8 (BitVec.ushiftRight (a) 3)) else (BitVec.truncate 8 (BitVec.ushiftRight (fadr) 8)))
  pmaddr1

end Pmem

namespace Reset

/-- The elaborated `rtlRstM` cone. -/
def rtlRstM (i : Input) : Bool :=
  (if i.rstN then true else false)

/-- The elaborated `rtlRstQ` cone. -/
def rtlRstQ (s : State) (i : Input) : Bool :=
  (if i.rstN then s.rstM else false)

/-- The elaborated whole transition. -/
def rtlStep (s : State) (i : Input) : State :=
  ⟨rtlRstM i, rtlRstQ s i⟩

end Reset

end Metronome.Debug

set_option linter.unusedSimpArgs false

namespace Metronome.Debug

namespace Pins

/-! ## (a) The pin level and edge vectors

The extracted cones are the RTL's `pins_level`, `pins_prev`, `lvl`, `rise` and
`fall`; the right-hand sides are SPEC_V2 §2 and §13.2. -/

theorem rtlPinsLevel_eq (s2 : BitVec 16) (rlv emask : BitVec 13) (replay : Bool) :
    rtlPinsLevel s2 rlv emask replay = level (pinVec s2) rlv emask replay := by
  simp only [rtlPinsLevel, level, pinVec, mask, maskOf, slice] <;> bv_decide

theorem rtlPinsPrev_eq (sp : BitVec 16) (rlvPrev emask : BitVec 13) (replay : Bool) :
    rtlPinsPrev sp rlvPrev emask replay = previous (pinVec sp) rlvPrev emask replay := by
  simp only [rtlPinsPrev, previous, pinVec, mask, maskOf, slice] <;> bv_decide

theorem rtlLvl_eq (pl : BitVec 13) : rtlLvl pl = lvl pl := by
  simp only [rtlLvl, lvl] <;> bv_decide

theorem rtlRise_eq (pl pp : BitVec 13) : rtlRise pl pp = rise pl pp := by
  simp only [rtlRise, rise] <;> bv_decide

theorem rtlFall_eq (pl pp : BitVec 13) : rtlFall pl pp = fall pl pp := by
  simp only [rtlFall, fall] <;> bv_decide

/-- The extracted pin level is the replay-masked synchronised level: masked pins
read `RLV` (SPEC_V2 §13.2). -/
theorem rtl_level_masked (s2 : BitVec 16) (rlv emask : BitVec 13) (replay : Bool) :
    rtlPinsLevel s2 rlv emask replay &&& mask emask replay = rlv &&& mask emask replay := by
  rw [rtlPinsLevel_eq]
  exact level_masked _ _ _ _

/-- Pins 13..15 of the extracted `lvl` read 0 (SPEC_V2 §2). -/
theorem rtl_lvl_high_zero (s2 : BitVec 16) (rlv emask : BitVec 13) (replay : Bool) :
    bitAt (rtlLvl (rtlPinsLevel s2 rlv emask replay)) 13 = false ∧
      bitAt (rtlLvl (rtlPinsLevel s2 rlv emask replay)) 14 = false ∧
      bitAt (rtlLvl (rtlPinsLevel s2 rlv emask replay)) 15 = false := by
  rw [rtlLvl_eq]
  exact lvl_high_zero _

/-- The extracted `rise` of the elaborated level and previous level. -/
theorem rtl_rise_level (s2 sp : BitVec 16) (rlv rlvPrev emask : BitVec 13) (replay : Bool) :
    rtlRise (rtlPinsLevel s2 rlv emask replay) (rtlPinsPrev sp rlvPrev emask replay) =
      rise (level (pinVec s2) rlv emask replay) (previous (pinVec sp) rlvPrev emask replay) := by
  rw [rtlPinsLevel_eq, rtlPinsPrev_eq, rtlRise_eq]

/-- The extracted `fall` of the elaborated level and previous level. -/
theorem rtl_fall_level (s2 sp : BitVec 16) (rlv rlvPrev emask : BitVec 13) (replay : Bool) :
    rtlFall (rtlPinsLevel s2 rlv emask replay) (rtlPinsPrev sp rlvPrev emask replay) =
      fall (level (pinVec s2) rlv emask replay) (previous (pinVec sp) rlvPrev emask replay) := by
  rw [rtlPinsLevel_eq, rtlPinsPrev_eq, rtlFall_eq]

end Pins

namespace Digest

/-! ## (b1) The execution digest (SPEC_V2 §12.2)

The extracted `MEN` and `MISR` next states are the SPEC equation: a `MCTL` write
with bit 1 clears, `MEN && !FRZ` advances, otherwise it holds. -/

theorem rtlMen_eq (s : State) (i : Input) : rtlMen s i = (step s i).men := by
  simp only [rtlMen, step, menNext, resetState, bitAt] <;> bv_decide

theorem rtlMisr_eq (s : State) (i : Input) : rtlMisr s i = (step s i).misr := by
  simp only [rtlMisr, step, misrNext, dataVec, poly, resetState, bitAt, slice] <;> bv_decide

/-- The extracted digest transition is SPEC_V2 §12.2's. -/
theorem rtlStep_eq_step (s : State) (i : Input) : rtlStep s i = step s i := by
  rw [show rtlStep s i = ⟨rtlMen s i, rtlMisr s i⟩ from rfl]
  exact State.ext (rtlMen_eq s i) (rtlMisr_eq s i)

/-- The digest state during cycle `n` of the extracted transition. -/
def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => rtlStep s i) inputs initial n

theorem rtlStateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial (n + 1) = rtlStep (rtlStateAt inputs initial n) (inputs n) := rfl

/-- The digest state during cycle `n` of the specification transition. -/
def stateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => step s i) inputs initial n

theorem stateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    stateAt inputs initial (n + 1) = step (stateAt inputs initial n) (inputs n) := rfl

/-- The extracted digest trace is the specification trace at every cycle. -/
theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt inputs initial n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rtlStateAt_succ, stateAt_succ, ih, rtlStep_eq_step]

theorem rtl_trace_result (inputs : Nat → Input) (initial : State) :
    ∀ n, rtlStateAt inputs initial n = stateAt inputs initial n :=
  fun n => rtlStateAt_eq inputs initial n

/-- A frozen cycle without an `MCTL` clear holds the extracted `MISR`
(SPEC_V2 §12.2's "else M' = M" with §12.3's freeze). -/
theorem rtl_trace_misr_frozen (inputs : Nat → Input) (initial : State) (n : Nat)
    (hr : (inputs n).resetN = true) (hf : (inputs n).frz = true)
    (hc : ((inputs n).dWrMctl && bitAt (inputs n).hWd 1) = false) :
    (rtlStateAt inputs initial (n + 1)).misr = (rtlStateAt inputs initial n).misr := by
  rw [rtlStateAt_succ, rtlStep_eq_step]
  simp only [step, hr, ite_true]
  exact misr_frozen_holds _ _ _ hf hc

end Digest

namespace Ctrl

/-! ## (b2) The capture/replay control (SPEC_V2 §12.4, §13.1, §13.2) -/

theorem rtlTick_eq (dc : BitVec 19) : rtlTick dc = tick dc := by
  simp only [rtlTick, tick] <;> bv_decide

theorem rtlInterval_eq (rw : BitVec 32) : rtlInterval rw = interval rw := by
  simp only [rtlInterval, interval, slice] <;> bv_decide

theorem rtlApply_eq (replay frz : Bool) (rv : BitVec 2) (dc : BitVec 19) (rw : BitVec 32) :
    rtlApply replay frz rv dc rw = apply replay frz (bitAt rv 0) dc rw := by
  simp only [rtlApply, apply, rtlTick, interval, tick, bitAt, slice] <;> bv_decide

theorem rtlLate_eq (replay frz : Bool) (rv : BitVec 2) (dc : BitVec 19) (rw : BitVec 32) :
    rtlLate replay frz rv dc rw = late replay frz (bitAt rv 0) dc rw := by
  simp only [rtlLate, late, rtlTick, interval, tick, bitAt, slice] <;> bv_decide

theorem rtlReplayLevels_eq (rlv emask : BitVec 13) (ap : Bool) (rw : BitVec 32) :
    rtlReplayLevels rlv emask ap rw = replayLevels rlv emask ap rw := by
  simp only [rtlReplayLevels, replayLevels, slice] <;> bv_decide

theorem rtlCev_eq (cen replay frz : Bool) (rise fall : BitVec 16) (emask : BitVec 13) :
    rtlCev cen replay frz rise fall emask = cev cen replay frz rise fall emask := by
  simp only [rtlCev, cev, slice] <;> bv_decide

theorem rtlReplay_eq (s : State) (i : Input) : rtlReplay s i = (step s i).replay := by
  simp only [rtlReplay, step, replayNext, resetState, bitAt] <;> bv_decide

theorem rtlCen_eq (s : State) (i : Input) : rtlCen s i = (step s i).cen := by
  simp only [rtlCen, step, cenNext, resetState, bitAt] <;> bv_decide

theorem rtlEmask_eq (s : State) (i : Input) : rtlEmask s i = (step s i).emask := by
  simp only [rtlEmask, step, emaskNext, resetState, bitAt, slice] <;> bv_decide

theorem rtlRlv_eq (s : State) (i : Input) : rtlRlv s i = (step s i).rlv := by
  simp only [rtlRlv, step, rlvNext, replayLevels, resetState, bitAt, slice] <;> bv_decide

theorem rtlRlvPrev_eq (s : State) (i : Input) : rtlRlvPrev s i = (step s i).rlvPrev := by
  simp only [rtlRlvPrev, step, rlvPrevNext, resetState, bitAt, slice] <;> bv_decide

theorem rtlDc_eq (s : State) (i : Input) : rtlDc s i = (step s i).dc := by
  simp only [rtlDc, step, dcNext, replayLevels, apply, cev, interval, tick, resetState, bitAt, slice] <;> bv_decide

/-- The extracted capture/replay transition is SPEC_V2 §12.4 and §13.2's. -/
theorem rtlStep_eq_step (s : State) (i : Input) : rtlStep s i = step s i := by
  rw [show rtlStep s i =
      ⟨rtlReplay s i, rtlCen s i, rtlEmask s i, rtlRlv s i, rtlRlvPrev s i,
       rtlDc s i⟩ from rfl]
  exact State.ext (rtlReplay_eq s i) (rtlCen_eq s i) (rtlEmask_eq s i) (rtlRlv_eq s i)
    (rtlRlvPrev_eq s i) (rtlDc_eq s i)

/-- The capture/replay state during cycle `n` of the extracted transition. -/
def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => rtlStep s i) inputs initial n

theorem rtlStateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial (n + 1) = rtlStep (rtlStateAt inputs initial n) (inputs n) := rfl

/-- The capture/replay state during cycle `n` of the specification transition. -/
def stateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => step s i) inputs initial n

theorem stateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    stateAt inputs initial (n + 1) = step (stateAt inputs initial n) (inputs n) := rfl

/-- The extracted capture/replay trace is the specification trace. -/
theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt inputs initial n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rtlStateAt_succ, stateAt_succ, ih, rtlStep_eq_step]

theorem rtl_trace_result (inputs : Nat → Input) (initial : State) :
    ∀ n, rtlStateAt inputs initial n = stateAt inputs initial n :=
  fun n => rtlStateAt_eq inputs initial n

/-- A frozen cycle with none of the four writes holds the extracted block
(SPEC_V2 §12.3). -/
theorem rtl_trace_frozen (inputs : Nat → Input) (initial : State) (n : Nat)
    (hr : (inputs n).resetN = true) (hf : (inputs n).frz = true)
    (h0 : (inputs n).dWrEctl = false) (h1 : (inputs n).dWrEm0 = false)
    (h2 : (inputs n).dWrEm1 = false) (h3 : (inputs n).dWrRlv0 = false)
    (h4 : (inputs n).dWrRlv1 = false) :
    rtlStateAt inputs initial (n + 1) = rtlStateAt inputs initial n := by
  rw [rtlStateAt_succ, rtlStep_eq_step]
  exact frozen_holds _ _ hr hf h0 h1 h2 h3 h4

/-- An `ECTL` write clears the extracted `DC` in the next cycle (SPEC_V2 §12.4,
host priority over the replay timer). -/
theorem rtl_trace_dc_ectl (inputs : Nat → Input) (initial : State) (n : Nat)
    (hr : (inputs n).resetN = true) (h : (inputs n).dWrEctl = true) :
    (rtlStateAt inputs initial (n + 1)).dc = 0 := by
  rw [rtlStateAt_succ, rtlStep_eq_step]
  simp only [step, hr, ite_true]
  exact dc_write_clears _ _ h

/-- A host `ECTL` write beats a same-cycle core drain, on the extracted
transition (SPEC_V2 §13.1). -/
theorem rtl_trace_ectl_host_wins (inputs : Nat → Input) (initial : State) (n : Nat)
    (hr : (inputs n).resetN = true) (h : (inputs n).dWrEctl = true)
    (hh : (inputs n).hEctl = true) :
    (rtlStateAt inputs initial (n + 1)).replay = bitAt (inputs n).hWd 1 ∧
      (rtlStateAt inputs initial (n + 1)).cen = bitAt (inputs n).hWd 0 := by
  rw [rtlStateAt_succ, rtlStep_eq_step]
  simp only [step, hr, ite_true]
  exact host_ectl_wins _ _ h hh

end Ctrl

namespace Pmem

/-! ## (c) The program-memory port (SPEC_V2 §5, §9, 9a.8) -/

theorem rtlPmWe0_eq (hWr inPrg : Bool) (a : BitVec 16) :
    rtlPmWe0 hWr inPrg a = we0 hWr inPrg a := by
  simp only [rtlPmWe0, we0, bitAt] <;> bv_decide

theorem rtlPmWe1_eq (hWr inPrg : Bool) (a : BitVec 16) :
    rtlPmWe1 hWr inPrg a = we1 hWr inPrg a := by
  simp only [rtlPmWe1, we1, bitAt] <;> bv_decide

theorem rtlPmBe_eq (a : BitVec 16) : rtlPmBe a = be a := by
  simp only [rtlPmBe, be, slice] <;> bv_decide

theorem rtlPmAddr0_eq (host : Bool) (a fadr : BitVec 16) :
    rtlPmAddr0 host a fadr = portAddr host (wordAddr a) (fetchAddr0 fadr) := by
  simp only [rtlPmAddr0, portAddr, wordAddr, fetchAddr0, slice] <;> bv_decide

theorem rtlPmAddr1_eq (host : Bool) (a fadr : BitVec 16) :
    rtlPmAddr1 host a fadr = portAddr host (wordAddr a) (fetchAddr1 fadr) := by
  simp only [rtlPmAddr1, portAddr, wordAddr, fetchAddr1, slice] <;> bv_decide

/-- The extracted byte lane is never zero. -/
theorem rtl_pm_lane_nonzero (a : BitVec 16) : rtlPmBe a != 0 := by
  rw [rtlPmBe_eq]
  exact be_ne_zero a

/-- At most one core's program-memory strobe fires. -/
theorem rtl_pm_exclusive (hWr inPrg : Bool) (a : BitVec 16) :
    (rtlPmWe0 hWr inPrg a && rtlPmWe1 hWr inPrg a) = false := by
  rw [rtlPmWe0_eq, rtlPmWe1_eq]
  exact we_exclusive _ _ _

/-- A host write takes the port: the word address presented to core 0 is the
host's, not that core's fetch address (§9; 9a.8 calls the word undefined). -/
theorem rtl_pm_port0 (hWr inPrg : Bool) (a fadr : BitVec 16) :
    rtlPmAddr0 (rtlPmWe0 hWr inPrg a) a fadr =
      portAddr (we0 hWr inPrg a) (wordAddr a) (fetchAddr0 fadr) := by
  rw [rtlPmAddr0_eq, rtlPmWe0_eq]

/-- The same for core 1. -/
theorem rtl_pm_port1 (hWr inPrg : Bool) (a fadr : BitVec 16) :
    rtlPmAddr1 (rtlPmWe1 hWr inPrg a) a fadr =
      portAddr (we1 hWr inPrg a) (wordAddr a) (fetchAddr1 fadr) := by
  rw [rtlPmAddr1_eq, rtlPmWe1_eq]

end Pmem

namespace Reset

/-! ## (d) The reset synchroniser (SPEC_V2 §1) -/

theorem rtlRstM_eq (s : State) (i : Input) : rtlRstM i = (step s i).rstM := by
  simp only [rtlRstM, step, resetState] <;> bv_decide

theorem rtlRstQ_eq (s : State) (i : Input) : rtlRstQ s i = (step s i).rstQ := by
  simp only [rtlRstQ, step, resetState] <;> bv_decide

/-- The extracted reset chain is SPEC_V2 §1's: both clear on a sampled low, and
`rst_q` takes `rst_m`. -/
theorem rtlStep_eq_step (s : State) (i : Input) : rtlStep s i = step s i := by
  rw [show rtlStep s i = ⟨rtlRstM i, rtlRstQ s i⟩ from rfl]
  exact State.ext (rtlRstM_eq s i) (rtlRstQ_eq s i)

/-- The reset state during cycle `n` of the extracted transition. -/
def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => rtlStep s i) inputs initial n

theorem rtlStateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial (n + 1) = rtlStep (rtlStateAt inputs initial n) (inputs n) := rfl

/-- The reset state during cycle `n` of the specification transition. -/
def stateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => step s i) inputs initial n

theorem stateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    stateAt inputs initial (n + 1) = step (stateAt inputs initial n) (inputs n) := rfl

/-- The extracted reset trace is the specification trace. -/
theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt inputs initial n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rtlStateAt_succ, stateAt_succ, ih, rtlStep_eq_step]

theorem rtl_trace_result (inputs : Nat → Input) (initial : State) :
    ∀ n, rtlStateAt inputs initial n = stateAt inputs initial n :=
  fun n => rtlStateAt_eq inputs initial n

/-- The extracted `rst_q` is low in the cycle after a sampled reset. -/
theorem rtl_trace_rstq_low (inputs : Nat → Input) (initial : State) (n : Nat)
    (h : (inputs n).rstN = false) :
    (rtlStateAt inputs initial (n + 1)).rstQ = false := by
  rw [rtlStateAt_eq]
  exact rstq_low_after_reset inputs initial n h

/-- The extracted `rst_q` is still low one cycle later: release needs two
rising edges (SPEC_V2 §1). -/
theorem rtl_trace_rstq_low_one_more (inputs : Nat → Input) (initial : State) (n : Nat)
    (h : (inputs n).rstN = false) :
    (rtlStateAt inputs initial (n + 2)).rstQ = false := by
  rw [rtlStateAt_eq]
  exact rstq_low_one_more inputs initial n h

/-- Two released edges after the assertion release the extracted `rst_q`. -/
theorem rtl_trace_rstq_after_two (inputs : Nat → Input) (initial : State) (n : Nat)
    (h0 : (inputs n).rstN = false) (h1 : (inputs (n + 1)).rstN = true)
    (h2 : (inputs (n + 2)).rstN = true) :
    (rtlStateAt inputs initial (n + 3)).rstQ = true := by
  rw [rtlStateAt_eq]
  exact rstq_after_two inputs initial n h0 h1 h2

end Reset

/-! ## Axiom audit

`debug_check.py` parses these records: a `sorryAx` fails an accepted case, and
the remaining axioms are kept with the evidence. -/

#print axioms Pins.rtlPinsLevel_eq
#print axioms Pins.rtlPinsPrev_eq
#print axioms Pins.rtlLvl_eq
#print axioms Pins.rtlRise_eq
#print axioms Pins.rtlFall_eq
#print axioms Pins.rtl_level_masked
#print axioms Pins.rtl_lvl_high_zero
#print axioms Pins.rtl_rise_level
#print axioms Pins.rtl_fall_level
#print axioms Digest.rtlMen_eq
#print axioms Digest.rtlMisr_eq
#print axioms Digest.rtlStep_eq_step
#print axioms Digest.rtlStateAt_eq
#print axioms Digest.rtl_trace_result
#print axioms Digest.rtl_trace_misr_frozen
#print axioms Ctrl.rtlTick_eq
#print axioms Ctrl.rtlInterval_eq
#print axioms Ctrl.rtlApply_eq
#print axioms Ctrl.rtlLate_eq
#print axioms Ctrl.rtlReplayLevels_eq
#print axioms Ctrl.rtlCev_eq
#print axioms Ctrl.rtlReplay_eq
#print axioms Ctrl.rtlCen_eq
#print axioms Ctrl.rtlEmask_eq
#print axioms Ctrl.rtlRlv_eq
#print axioms Ctrl.rtlRlvPrev_eq
#print axioms Ctrl.rtlDc_eq
#print axioms Ctrl.rtlStep_eq_step
#print axioms Ctrl.rtlStateAt_eq
#print axioms Ctrl.rtl_trace_result
#print axioms Ctrl.rtl_trace_frozen
#print axioms Ctrl.rtl_trace_dc_ectl
#print axioms Ctrl.rtl_trace_ectl_host_wins
#print axioms Pmem.rtlPmWe0_eq
#print axioms Pmem.rtlPmWe1_eq
#print axioms Pmem.rtlPmBe_eq
#print axioms Pmem.rtlPmAddr0_eq
#print axioms Pmem.rtlPmAddr1_eq
#print axioms Pmem.rtl_pm_lane_nonzero
#print axioms Pmem.rtl_pm_exclusive
#print axioms Pmem.rtl_pm_port0
#print axioms Pmem.rtl_pm_port1
#print axioms Reset.rtlRstM_eq
#print axioms Reset.rtlRstQ_eq
#print axioms Reset.rtlStep_eq_step
#print axioms Reset.rtlStateAt_eq
#print axioms Reset.rtl_trace_result
#print axioms Reset.rtl_trace_rstq_low
#print axioms Reset.rtl_trace_rstq_low_one_more
#print axioms Reset.rtl_trace_rstq_after_two

end Metronome.Debug
