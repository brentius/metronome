import Metronome.Line

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 4a6c28a649f418577beffa948701180953d1f020c4a9e5332f6ee42b57cb4984
-- Line: the `md2_line` module of the four `g_ln` instances.  `cfg` is the
-- line's window; the adapter checked that every `c_*` field net is the window
-- byte slice of the specification before emitting this file.
--
-- The transition is emitted in layers (see `LAYERS` in `line_check.py`): each
-- intermediate net is a definition whose cone binds the earlier layers to their
-- specification expressions, and `rtlStep` binds all of them, so the register
-- equations are definitional.

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Metronome.Line

/-- The elaborated `edg` cone. -/
def rtlEdg (input : Input) : Bool :=
  let rtl0 := (((BitVec.ushiftRight (input.rise) ((BitVec.truncate 4 (BitVec.ushiftRight (input.cfg.edge) 0))).toNat) &&& (1 : BitVec 16)) != 0)
  let rtl1 := ((BitVec.truncate 2 (BitVec.ushiftRight (input.cfg.edge) 4)) == (1 : BitVec 2))
  let rtl2 := (((BitVec.ushiftRight (input.fall) ((BitVec.truncate 4 (BitVec.ushiftRight (input.cfg.edge) 0))).toNat) &&& (1 : BitVec 16)) != 0)
  let rtl3 := ((BitVec.truncate 2 (BitVec.ushiftRight (input.cfg.edge) 4)) == (2 : BitVec 2))
  let rtl4 := (((BitVec.ushiftRight (input.rise) ((BitVec.truncate 4 (BitVec.ushiftRight (input.cfg.edge) 0))).toNat) &&& (1 : BitVec 16)) != 0)
  let rtl5 := (((BitVec.ushiftRight (input.fall) ((BitVec.truncate 4 (BitVec.ushiftRight (input.cfg.edge) 0))).toNat) &&& (1 : BitVec 16)) != 0)
  let rtl6 := (rtl4 || rtl5)
  let rtl7 := ((BitVec.truncate 2 (BitVec.ushiftRight (input.cfg.edge) 4)) == (3 : BitVec 2))
  let rtl8 := (if rtl7 then rtl6 else (if rtl3 then rtl2 else (if rtl1 then rtl0 else false)))
  let rtl9 := (!input.frz)
  let rtl10 := (rtl8 && rtl9)
  rtl10

/-- The elaborated `e0` cone. -/
def rtlE0 (input : Input) : Bool :=
  let rtl0 := (((BitVec.ushiftRight (input.rise) ((BitVec.truncate 4 (BitVec.ushiftRight (input.cfg.t0edge) 0))).toNat) &&& (1 : BitVec 16)) != 0)
  let rtl1 := ((BitVec.truncate 2 (BitVec.ushiftRight (input.cfg.t0edge) 4)) == (1 : BitVec 2))
  let rtl2 := (((BitVec.ushiftRight (input.fall) ((BitVec.truncate 4 (BitVec.ushiftRight (input.cfg.t0edge) 0))).toNat) &&& (1 : BitVec 16)) != 0)
  let rtl3 := ((BitVec.truncate 2 (BitVec.ushiftRight (input.cfg.t0edge) 4)) == (2 : BitVec 2))
  let rtl4 := (((BitVec.ushiftRight (input.rise) ((BitVec.truncate 4 (BitVec.ushiftRight (input.cfg.t0edge) 0))).toNat) &&& (1 : BitVec 16)) != 0)
  let rtl5 := (((BitVec.ushiftRight (input.fall) ((BitVec.truncate 4 (BitVec.ushiftRight (input.cfg.t0edge) 0))).toNat) &&& (1 : BitVec 16)) != 0)
  let rtl6 := (rtl4 || rtl5)
  let rtl7 := ((BitVec.truncate 2 (BitVec.ushiftRight (input.cfg.t0edge) 4)) == (3 : BitVec 2))
  let rtl8 := (if rtl7 then rtl6 else (if rtl3 then rtl2 else (if rtl1 then rtl0 else false)))
  let rtl9 := (!input.frz)
  let rtl10 := (rtl8 && rtl9)
  rtl10

/-- The elaborated `runa` cone. -/
def rtlRuna (state : State) (input : Input) : Bool :=
  let rtl0 := (!input.frz)
  let rtl1 := (state.run && rtl0)
  rtl1

/-- The elaborated `inwin` cone. -/
def rtlInwin (state : State) (input : Input) : Bool :=
  let rtl0 := decide (input.cfg.wlo <= input.cfg.whi)
  let rtl1 := decide (input.cfg.wlo <= state.ph)
  let rtl2 := decide (state.ph <= input.cfg.whi)
  let rtl3 := (rtl1 && rtl2)
  let rtl4 := decide (state.ph >= input.cfg.wlo)
  let rtl5 := decide (state.ph <= input.cfg.whi)
  let rtl6 := (rtl4 || rtl5)
  let rtl7 := (if rtl0 then rtl3 else rtl6)
  rtl7

/-- The elaborated `start` cone. -/
def rtlStart (state : State) (input : Input) : Bool :=
  let rtl0 := (!state.run)
  let rtl1 := (edge state input && state.arm && rtl0)
  rtl1

/-- The elaborated `accept` cone. -/
def rtlAccept (state : State) (input : Input) : Bool :=
  let rtl0 := (!((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.edge) 6)) != 0))
  let rtl1 := (rtl0 || inwin state input)
  let rtl2 := (edge state input && state.run && state.ren && rtl1)
  rtl2

/-- The elaborated `n` cone. -/
def rtlN (state : State) (input : Input) : BitVec 17 :=
  let rtl0 := (((0 : BitVec 1) ++ (BitVec.truncate 16 (BitVec.ushiftRight (state.ph) 0))) + ((0 : BitVec 1) ++ (BitVec.truncate 16 (BitVec.ushiftRight (input.cfg.inc) 0))))
  rtl0

/-- The elaborated `over` cone. -/
def rtlOver (state : State) (input : Input) : Bool :=
  let rtl0 := decide (sum17 state input >= ((0 : BitVec 1) ++ (BitVec.truncate 16 (BitVec.ushiftRight (input.cfg.mod) 0))))
  rtl0

/-- The elaborated `nxw` cone. -/
def rtlNxw (state : State) (input : Input) : BitVec 17 :=
  let rtl0 := (sum17 state input - ((0 : BitVec 1) ++ (BitVec.truncate 16 (BitVec.ushiftRight (input.cfg.mod) 0))))
  rtl0

/-- The elaborated `nx` cone. -/
def rtlNx (state : State) (input : Input) : BitVec 16 :=
  let rtl0 := (if over state input then (BitVec.truncate 16 (BitVec.ushiftRight (nxw state input) 0)) else (BitVec.truncate 16 (BitVec.ushiftRight (sum17 state input) 0)))
  rtl0

/-- The elaborated `th` cone. -/
def rtlTh (input : Input) : BitVec 16 :=
  let rtl0 := ((BitVec.truncate 2 (BitVec.ushiftRight (input.cfg.hold) 5)) == (0 : BitVec 2))
  let rtl1 := ((BitVec.truncate 2 (BitVec.ushiftRight (input.cfg.hold) 5)) == (1 : BitVec 2))
  let rtl2 := (if rtl1 then input.cfg.t1 else input.cfg.t2)
  let rtl3 := (if rtl0 then input.cfg.t0 else rtl2)
  rtl3

/-- The elaborated `htok` cone. -/
def rtlHTok (input : Input) : Bool :=
  let rtl0 := ((BitVec.truncate 2 (BitVec.ushiftRight (input.cfg.hold) 5)) != (3 : BitVec 2))
  let rtl1 := ((BitVec.truncate 2 (BitVec.ushiftRight (input.cfg.hold) 5)) == (0 : BitVec 2))
  let rtl2 := (rtl1 && ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.t0edge) 6)) != 0))
  let rtl3 := (!rtl2)
  let rtl4 := ((BitVec.truncate 2 (BitVec.ushiftRight (input.cfg.hold) 5)) == (0 : BitVec 2))
  let rtl5 := decide (input.cfg.t0 < input.cfg.mod)
  let rtl6 := ((BitVec.truncate 2 (BitVec.ushiftRight (input.cfg.hold) 5)) == (1 : BitVec 2))
  let rtl7 := decide (input.cfg.t1 < input.cfg.mod)
  let rtl8 := decide (input.cfg.t2 < input.cfg.mod)
  let rtl9 := (if rtl6 then rtl7 else rtl8)
  let rtl10 := (if rtl4 then rtl5 else rtl9)
  let rtl11 := (rtl0 && rtl3 && rtl10)
  rtl11

/-- The elaborated `hold` cone. -/
def rtlHold (state : State) (input : Input) : Bool :=
  let rtl0 := (!accept state input)
  let rtl1 := decide (holdTap input > state.ph)
  let rtl2 := decide (holdTap input <= nx state input)
  let rtl3 := (rtl1 || rtl2)
  let rtl4 := decide (state.ph < holdTap input)
  let rtl5 := decide (holdTap input <= nx state input)
  let rtl6 := (rtl4 && rtl5)
  let rtl7 := (if over state input then rtl3 else rtl6)
  let rtl8 := (((BitVec.ushiftRight (input.lvl) ((BitVec.truncate 4 (BitVec.ushiftRight (input.cfg.hold) 0))).toNat) &&& (1 : BitVec 16)) != 0)
  let rtl9 := (rtl8 != ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.hold) 4)) != 0))
  let rtl10 := (((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.hold) 7)) != 0) && runa state input && rtl0 && holdTok state input && rtl7 && rtl9)
  rtl10

/-- The elaborated `adv` cone. -/
def rtlAdv (state : State) (input : Input) : Bool :=
  let rtl0 := (!accept state input)
  let rtl1 := (!hold state input)
  let rtl2 := (runa state input && rtl0 && rtl1)
  rtl2

/-- The elaborated `wrap` cone. -/
def rtlWrap (state : State) (input : Input) : Bool :=
  let rtl0 := (adv state input && over state input)
  rtl0

/-- The elaborated `beatout` cone. -/
def rtlBeatOut (state : State) (input : Input) : Bool :=
  let rtl0 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.edge) 7)) != 0) then accept state input else wrap state input)
  rtl0

/-- The elaborated `missev` cone. -/
def rtlMissEv (state : State) (input : Input) : Bool :=
  let rtl0 := ((BitVec.truncate 2 (BitVec.ushiftRight (input.cfg.t0edge) 4)) != 0)
  let rtl1 := decide (input.cfg.t0 < input.cfg.mod)
  let rtl2 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.t0edge) 6)) != 0) then rtl0 else rtl1)
  let rtl3 := decide (input.cfg.t1 < input.cfg.mod)
  let rtl4 := decide (input.cfg.t2 < input.cfg.mod)
  let rtl5 := (~~~state.fired)
  let rtl6 := (state.run && e0 state input)
  let rtl7 := decide (input.cfg.t1 > state.ph)
  let rtl8 := decide (input.cfg.t1 <= nx state input)
  let rtl9 := (rtl7 || rtl8)
  let rtl10 := decide (state.ph < input.cfg.t1)
  let rtl11 := decide (input.cfg.t1 <= nx state input)
  let rtl12 := (rtl10 && rtl11)
  let rtl13 := (if over state input then rtl9 else rtl12)
  let rtl14 := (adv state input && rtl1 && rtl13)
  let rtl15 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.t0edge) 6)) != 0) then rtl6 else rtl14)
  let rtl16 := (state.run && e0 state input && beat state input)
  let rtl17 := decide (input.cfg.t0 <= nx state input)
  let rtl18 := (adv state input && rtl1 && rtl13 && beat state input && over state input && rtl17)
  let rtl19 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.t0edge) 6)) != 0) then rtl16 else rtl18)
  let rtl20 := (!rtl19)
  let rtl21 := (rtl15 && rtl20)
  let rtl22 := decide (input.cfg.t1 > state.ph)
  let rtl23 := decide (input.cfg.t1 <= nx state input)
  let rtl24 := (rtl22 || rtl23)
  let rtl25 := decide (state.ph < input.cfg.t1)
  let rtl26 := decide (input.cfg.t1 <= nx state input)
  let rtl27 := (rtl25 && rtl26)
  let rtl28 := (if over state input then rtl24 else rtl27)
  let rtl29 := decide (input.cfg.t1 <= nx state input)
  let rtl30 := (adv state input && rtl3 && rtl28 && beat state input && over state input && rtl29)
  let rtl31 := (!rtl30)
  let rtl32 := (adv state input && rtl3 && rtl28 && rtl31)
  let rtl33 := decide (input.cfg.t2 > state.ph)
  let rtl34 := decide (input.cfg.t2 <= nx state input)
  let rtl35 := (rtl33 || rtl34)
  let rtl36 := decide (state.ph < input.cfg.t2)
  let rtl37 := decide (input.cfg.t2 <= nx state input)
  let rtl38 := (rtl36 && rtl37)
  let rtl39 := (if over state input then rtl35 else rtl38)
  let rtl40 := decide (input.cfg.t2 <= nx state input)
  let rtl41 := (adv state input && rtl4 && rtl39 && beat state input && over state input && rtl40)
  let rtl42 := (!rtl41)
  let rtl43 := (adv state input && rtl4 && rtl39 && rtl42)
  let rtl44 := (~~~(((if rtl43 then (1 : BitVec 1) else 0) ++ (if rtl32 then (1 : BitVec 1) else 0)) ++ (if rtl21 then (1 : BitVec 1) else 0)))
  let rtl45 := (((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.t0edge) 6)) != 0) && state.first)
  let rtl46 := (!rtl45)
  let rtl47 := ((((if rtl4 then (1 : BitVec 1) else 0) ++ (if rtl3 then (1 : BitVec 1) else 0)) ++ (if rtl2 then (1 : BitVec 1) else 0)) &&& rtl5 &&& rtl44 &&& ((3 : BitVec 2) ++ (if rtl46 then (1 : BitVec 1) else 0)))
  let rtl48 := (rtl47 != 0)
  let rtl49 := (beat state input && rtl48)
  rtl49

/-- The elaborated `firednext` cone. -/
def rtlFiredNext (state : State) (input : Input) : BitVec 3 :=
  let rtl0 := (state.run && e0 state input && beat state input)
  let rtl1 := decide (input.cfg.t0 < input.cfg.mod)
  let rtl2 := decide (input.cfg.t1 > state.ph)
  let rtl3 := decide (input.cfg.t1 <= nx state input)
  let rtl4 := (rtl2 || rtl3)
  let rtl5 := decide (state.ph < input.cfg.t1)
  let rtl6 := decide (input.cfg.t1 <= nx state input)
  let rtl7 := (rtl5 && rtl6)
  let rtl8 := (if over state input then rtl4 else rtl7)
  let rtl9 := decide (input.cfg.t0 <= nx state input)
  let rtl10 := (adv state input && rtl1 && rtl8 && beat state input && over state input && rtl9)
  let rtl11 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.t0edge) 6)) != 0) then rtl0 else rtl10)
  let rtl12 := decide (input.cfg.t1 < input.cfg.mod)
  let rtl13 := decide (input.cfg.t1 > state.ph)
  let rtl14 := decide (input.cfg.t1 <= nx state input)
  let rtl15 := (rtl13 || rtl14)
  let rtl16 := decide (state.ph < input.cfg.t1)
  let rtl17 := decide (input.cfg.t1 <= nx state input)
  let rtl18 := (rtl16 && rtl17)
  let rtl19 := (if over state input then rtl15 else rtl18)
  let rtl20 := decide (input.cfg.t1 <= nx state input)
  let rtl21 := (adv state input && rtl12 && rtl19 && beat state input && over state input && rtl20)
  let rtl22 := decide (input.cfg.t2 < input.cfg.mod)
  let rtl23 := decide (input.cfg.t2 > state.ph)
  let rtl24 := decide (input.cfg.t2 <= nx state input)
  let rtl25 := (rtl23 || rtl24)
  let rtl26 := decide (state.ph < input.cfg.t2)
  let rtl27 := decide (input.cfg.t2 <= nx state input)
  let rtl28 := (rtl26 && rtl27)
  let rtl29 := (if over state input then rtl25 else rtl28)
  let rtl30 := decide (input.cfg.t2 <= nx state input)
  let rtl31 := (adv state input && rtl22 && rtl29 && beat state input && over state input && rtl30)
  let rtl32 := (state.run && e0 state input)
  let rtl33 := (adv state input && rtl1 && rtl8)
  let rtl34 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.t0edge) 6)) != 0) then rtl32 else rtl33)
  let rtl35 := (!rtl11)
  let rtl36 := (rtl34 && rtl35)
  let rtl37 := (!rtl21)
  let rtl38 := (adv state input && rtl12 && rtl19 && rtl37)
  let rtl39 := (!rtl31)
  let rtl40 := (adv state input && rtl22 && rtl29 && rtl39)
  let rtl41 := (state.fired ||| (((if rtl40 then (1 : BitVec 1) else 0) ++ (if rtl38 then (1 : BitVec 1) else 0)) ++ (if rtl36 then (1 : BitVec 1) else 0)))
  let rtl42 := (if beat state input then (((if rtl31 then (1 : BitVec 1) else 0) ++ (if rtl21 then (1 : BitVec 1) else 0)) ++ (if rtl11 then (1 : BitVec 1) else 0)) else rtl41)
  rtl42

/-- The elaborated `snap` cone. -/
def rtlSnap (state : State) (input : Input) : Bool :=
  let rtl0 := (input.cfg.snap == (3 : BitVec 2))
  let rtl1 := (state.run && e0 state input)
  let rtl2 := decide (input.cfg.t0 < input.cfg.mod)
  let rtl3 := decide (input.cfg.t1 > state.ph)
  let rtl4 := decide (input.cfg.t1 <= nx state input)
  let rtl5 := (rtl3 || rtl4)
  let rtl6 := decide (state.ph < input.cfg.t1)
  let rtl7 := decide (input.cfg.t1 <= nx state input)
  let rtl8 := (rtl6 && rtl7)
  let rtl9 := (if over state input then rtl5 else rtl8)
  let rtl10 := (adv state input && rtl2 && rtl9)
  let rtl11 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.t0edge) 6)) != 0) then rtl1 else rtl10)
  let rtl12 := (state.run && e0 state input && beat state input)
  let rtl13 := decide (input.cfg.t0 <= nx state input)
  let rtl14 := (adv state input && rtl2 && rtl9 && beat state input && over state input && rtl13)
  let rtl15 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.t0edge) 6)) != 0) then rtl12 else rtl14)
  let rtl16 := (!rtl15)
  let rtl17 := (!((BitVec.truncate 1 (BitVec.ushiftRight (state.fired) 0)) != 0))
  let rtl18 := (rtl11 && rtl16 && rtl17)
  let rtl19 := (rtl18 || rtl15)
  let rtl20 := decide (input.cfg.t1 < input.cfg.mod)
  let rtl21 := decide (input.cfg.t1 > state.ph)
  let rtl22 := decide (input.cfg.t1 <= nx state input)
  let rtl23 := (rtl21 || rtl22)
  let rtl24 := decide (state.ph < input.cfg.t1)
  let rtl25 := decide (input.cfg.t1 <= nx state input)
  let rtl26 := (rtl24 && rtl25)
  let rtl27 := (if over state input then rtl23 else rtl26)
  let rtl28 := decide (input.cfg.t1 <= nx state input)
  let rtl29 := (adv state input && rtl20 && rtl27 && beat state input && over state input && rtl28)
  let rtl30 := (!rtl29)
  let rtl31 := (!((BitVec.truncate 1 (BitVec.ushiftRight (state.fired) 1)) != 0))
  let rtl32 := (adv state input && rtl20 && rtl27 && rtl30 && rtl31)
  let rtl33 := (rtl32 || rtl29)
  let rtl34 := decide (input.cfg.t2 < input.cfg.mod)
  let rtl35 := decide (input.cfg.t2 > state.ph)
  let rtl36 := decide (input.cfg.t2 <= nx state input)
  let rtl37 := (rtl35 || rtl36)
  let rtl38 := decide (state.ph < input.cfg.t2)
  let rtl39 := decide (input.cfg.t2 <= nx state input)
  let rtl40 := (rtl38 && rtl39)
  let rtl41 := (if over state input then rtl37 else rtl40)
  let rtl42 := decide (input.cfg.t2 <= nx state input)
  let rtl43 := (adv state input && rtl34 && rtl41 && beat state input && over state input && rtl42)
  let rtl44 := (!rtl43)
  let rtl45 := (!((BitVec.truncate 1 (BitVec.ushiftRight (state.fired) 2)) != 0))
  let rtl46 := (adv state input && rtl34 && rtl41 && rtl44 && rtl45)
  let rtl47 := (rtl46 || rtl43)
  let rtl48 := (((BitVec.ushiftRight ((((if rtl47 then (1 : BitVec 1) else 0) ++ (if rtl33 then (1 : BitVec 1) else 0)) ++ (if rtl19 then (1 : BitVec 1) else 0))) (input.cfg.snap).toNat) &&& (1 : BitVec 3)) != 0)
  let rtl49 := (if rtl0 then beat state input else rtl48)
  rtl49

/-- The elaborated `phc` cone. -/
def rtlPhC (state : State) (input : Input) : BitVec 16 :=
  let rtl0 := (start state input || accept state input)
  let rtl1 := (if adv state input then nx state input else state.ph)
  let rtl2 := (if rtl0 then input.cfg.pre else rtl1)
  rtl2

/-- The elaborated `phf` cone. -/
def rtlPhF (state : State) (input : Input) : BitVec 16 :=
  let rtl0 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.phWe) 1)) != 0) then ((BitVec.truncate 8 (BitVec.ushiftRight (input.hD) 0)) ++ (BitVec.truncate 8 (BitVec.ushiftRight (phC state input) 0))) else phC state input)
  let rtl1 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.phWe) 0)) != 0) then ((BitVec.truncate 8 (BitVec.ushiftRight (phC state input) 8)) ++ (BitVec.truncate 8 (BitVec.ushiftRight (input.hD) 0))) else rtl0)
  rtl1

/-- The elaborated `runc` cone. -/
def rtlRunC (state : State) (input : Input) : Bool :=
  let rtl0 := (state.run || start state input)
  let rtl1 := (if input.ctlWe then ((BitVec.truncate 1 (BitVec.ushiftRight (input.ctlD) 0)) != 0) else rtl0)
  rtl1

/-- The elaborated `armc` cone. -/
def rtlArmC (state : State) (input : Input) : Bool :=
  let rtl0 := (!start state input)
  let rtl1 := (state.arm && rtl0)
  let rtl2 := (if input.ctlWe then ((BitVec.truncate 1 (BitVec.ushiftRight (input.ctlD) 1)) != 0) else rtl1)
  rtl2

/-- The elaborated `renc` cone. -/
def rtlRenC (state : State) (input : Input) : Bool :=
  let rtl0 := (if input.ctlWe then ((BitVec.truncate 1 (BitVec.ushiftRight (input.ctlD) 2)) != 0) else state.ren)
  rtl0

/-- The elaborated `runf` cone. -/
def rtlRunF (state : State) (input : Input) : Bool :=
  let rtl0 := (if input.hCtlWe then ((BitVec.truncate 1 (BitVec.ushiftRight (input.hD) 0)) != 0) else runC state input)
  rtl0

/-- The elaborated `starting` cone. -/
def rtlStarting (state : State) (input : Input) : Bool :=
  let rtl0 := (!state.run)
  let rtl1 := (runF state input && rtl0)
  rtl1

/-- The elaborated `stagedn` cone. -/
def rtlStagedN (state : State) (input : Input) : BitVec 4 :=
  let rtl0 := (state.staged ^^^ input.symD)
  let rtl1 := (input.symOp == (0 : BitVec 2))
  let rtl2 := (input.symOp == (1 : BitVec 2))
  let rtl3 := (if rtl2 then ((BitVec.truncate 3 (BitVec.ushiftRight (state.staged) 1)) ++ (BitVec.truncate 1 (BitVec.ushiftRight (input.symD) 0))) else (if rtl1 then input.symD else rtl0))
  let rtl4 := (if input.symWe then rtl3 else (0 : BitVec 4))
  let rtl5 := (if input.symWe then rtl4 else state.staged)
  rtl5

/-- The elaborated `segvalue` cone. -/
def rtlSegValue (state : State) : BitVec 2 :=
  let rtl0 := (((0 : BitVec 1) ++ (BitVec.truncate 1 (BitVec.ushiftRight (state.fired) 0))) + ((0 : BitVec 1) ++ (BitVec.truncate 1 (BitVec.ushiftRight (state.fired) 1))))
  let rtl1 := (rtl0 + ((0 : BitVec 1) ++ (BitVec.truncate 1 (BitVec.ushiftRight (state.fired) 2))))
  rtl1

/-- The elaborated `pinain` cone. -/
def rtlPinaIn (input : Input) : Bool :=
  let rtl0 := (((BitVec.ushiftRight (input.lvl) ((BitVec.truncate 4 (BitVec.ushiftRight (input.cfg.pins) 0))).toNat) &&& (1 : BitVec 16)) != 0)
  rtl0

/-- The elaborated `pinbin` cone. -/
def rtlPinbIn (input : Input) : Bool :=
  let rtl0 := (((BitVec.ushiftRight (input.lvl) ((BitVec.truncate 4 (BitVec.ushiftRight (input.cfg.pins) 4))).toNat) &&& (1 : BitVec 16)) != 0)
  rtl0

/-- The elaborated `pinarisein` cone. -/
def rtlPinaRiseIn (input : Input) : Bool :=
  let rtl0 := (((BitVec.ushiftRight (input.rise) ((BitVec.truncate 4 (BitVec.ushiftRight (input.cfg.pins) 0))).toNat) &&& (1 : BitVec 16)) != 0)
  rtl0

/-- The elaborated `pinafallin` cone. -/
def rtlPinaFallIn (input : Input) : Bool :=
  let rtl0 := (((BitVec.ushiftRight (input.fall) ((BitVec.truncate 4 (BitVec.ushiftRight (input.cfg.pins) 0))).toNat) &&& (1 : BitVec 16)) != 0)
  rtl0

/-- The elaborated `tapout` output cone. -/
def rtlTapOut (state : State) (input : Input) : BitVec 3 :=
  let rtl0 := (state.run && e0 state input)
  let rtl1 := decide (input.cfg.t0 < input.cfg.mod)
  let rtl2 := decide (input.cfg.t1 > state.ph)
  let rtl3 := decide (input.cfg.t1 <= nx state input)
  let rtl4 := (rtl2 || rtl3)
  let rtl5 := decide (state.ph < input.cfg.t1)
  let rtl6 := decide (input.cfg.t1 <= nx state input)
  let rtl7 := (rtl5 && rtl6)
  let rtl8 := (if over state input then rtl4 else rtl7)
  let rtl9 := (adv state input && rtl1 && rtl8)
  let rtl10 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.t0edge) 6)) != 0) then rtl0 else rtl9)
  let rtl11 := (state.run && e0 state input && beat state input)
  let rtl12 := decide (input.cfg.t0 <= nx state input)
  let rtl13 := (adv state input && rtl1 && rtl8 && beat state input && over state input && rtl12)
  let rtl14 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.t0edge) 6)) != 0) then rtl11 else rtl13)
  let rtl15 := (!rtl14)
  let rtl16 := (!((BitVec.truncate 1 (BitVec.ushiftRight (state.fired) 0)) != 0))
  let rtl17 := (rtl10 && rtl15 && rtl16)
  let rtl18 := (rtl17 || rtl14)
  let rtl19 := decide (input.cfg.t1 < input.cfg.mod)
  let rtl20 := decide (input.cfg.t1 > state.ph)
  let rtl21 := decide (input.cfg.t1 <= nx state input)
  let rtl22 := (rtl20 || rtl21)
  let rtl23 := decide (state.ph < input.cfg.t1)
  let rtl24 := decide (input.cfg.t1 <= nx state input)
  let rtl25 := (rtl23 && rtl24)
  let rtl26 := (if over state input then rtl22 else rtl25)
  let rtl27 := decide (input.cfg.t1 <= nx state input)
  let rtl28 := (adv state input && rtl19 && rtl26 && beat state input && over state input && rtl27)
  let rtl29 := (!rtl28)
  let rtl30 := (!((BitVec.truncate 1 (BitVec.ushiftRight (state.fired) 1)) != 0))
  let rtl31 := (adv state input && rtl19 && rtl26 && rtl29 && rtl30)
  let rtl32 := (rtl31 || rtl28)
  let rtl33 := decide (input.cfg.t2 < input.cfg.mod)
  let rtl34 := decide (input.cfg.t2 > state.ph)
  let rtl35 := decide (input.cfg.t2 <= nx state input)
  let rtl36 := (rtl34 || rtl35)
  let rtl37 := decide (state.ph < input.cfg.t2)
  let rtl38 := decide (input.cfg.t2 <= nx state input)
  let rtl39 := (rtl37 && rtl38)
  let rtl40 := (if over state input then rtl36 else rtl39)
  let rtl41 := decide (input.cfg.t2 <= nx state input)
  let rtl42 := (adv state input && rtl33 && rtl40 && beat state input && over state input && rtl41)
  let rtl43 := (!rtl42)
  let rtl44 := (!((BitVec.truncate 1 (BitVec.ushiftRight (state.fired) 2)) != 0))
  let rtl45 := (adv state input && rtl33 && rtl40 && rtl43 && rtl44)
  let rtl46 := (rtl45 || rtl42)
  (((if rtl46 then (1 : BitVec 1) else 0) ++ (if rtl32 then (1 : BitVec 1) else 0)) ++ (if rtl18 then (1 : BitVec 1) else 0))

/-- The elaborated `insymout` output cone. -/
def rtlInSymOut (state : State) (input : Input) : BitVec 2 :=
  let rtl0 := (((BitVec.ushiftRight (input.cfg.lut0) (((if state.rem then (1 : BitVec 1) else 0) ++ (BitVec.truncate 4 (BitVec.ushiftRight (state.sn) 0)))).toNat) &&& (1 : BitVec 32)) != 0)
  let rtl1 := (((BitVec.ushiftRight (input.cfg.lut1) (((if state.rem then (1 : BitVec 1) else 0) ++ (BitVec.truncate 4 (BitVec.ushiftRight (state.sn) 0)))).toNat) &&& (1 : BitVec 32)) != 0)
  ((if rtl1 then (1 : BitVec 1) else 0) ++ (if rtl0 then (1 : BitVec 1) else 0))

/-- The elaborated `capvalue` output cone. -/
def rtlCapValue (state : State) : BitVec 5 :=

  ((if state.rem then (1 : BitVec 1) else 0) ++ (BitVec.truncate 4 (BitVec.ushiftRight (state.sn) 0)))

/-- The elaborated line transition.  `state` holds the fifteen registers of
`md2_line.v`; `input` holds the sampled pins, moves, host writes and freeze. -/
def rtlStep (state : State) (input : Input) : State :=
  let rtl0 := (if input.resetN then phF state input else (0 : BitVec 16))
  let rtl1 := (if input.resetN then runF state input else false)
  let rtl2 := (if input.hCtlWe then ((BitVec.truncate 1 (BitVec.ushiftRight (input.hD) 1)) != 0) else armC state input)
  let rtl3 := (if input.resetN then rtl2 else false)
  let rtl4 := (if input.hCtlWe then ((BitVec.truncate 1 (BitVec.ushiftRight (input.hD) 2)) != 0) else renC state input)
  let rtl5 := (if input.resetN then rtl4 else false)
  let rtl6 := (if input.frz then state.held else hold state input)
  let rtl7 := (if input.resetN then rtl6 else false)
  let rtl8 := (!beat state input)
  let rtl9 := (state.first && rtl8)
  let rtl10 := (starting state input || rtl9)
  let rtl11 := (if input.resetN then rtl10 else false)
  let rtl12 := (if beat state input then false else state.sc)
  let rtl13 := (if accept state input then true else rtl12)
  let rtl14 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.edge) 7)) != 0) then false else rtl13)
  let rtl15 := (if input.resetN then rtl14 else false)
  let rtl16 := (if wrap state input then false else state.sp)
  let rtl17 := (if beat state input then true else rtl16)
  let rtl18 := (if beat state input then state.sc else state.sp)
  let rtl19 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.edge) 7)) != 0) then rtl17 else rtl18)
  let rtl20 := (if input.resetN then rtl19 else false)
  let rtl21 := (!((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.t0edge) 6)) != 0))
  let rtl22 := decide (input.cfg.t0 < input.cfg.mod)
  let rtl23 := decide (input.cfg.t0 <= phF state input)
  let rtl24 := (rtl21 && rtl22 && rtl23)
  let rtl25 := decide (input.cfg.t1 < input.cfg.mod)
  let rtl26 := decide (input.cfg.t1 <= phF state input)
  let rtl27 := (rtl25 && rtl26)
  let rtl28 := decide (input.cfg.t2 < input.cfg.mod)
  let rtl29 := decide (input.cfg.t2 <= phF state input)
  let rtl30 := (rtl28 && rtl29)
  let rtl31 := (if starting state input then (((if rtl30 then (1 : BitVec 1) else 0) ++ (if rtl27 then (1 : BitVec 1) else 0)) ++ (if rtl24 then (1 : BitVec 1) else 0)) else firedNext state input)
  let rtl32 := (if input.resetN then rtl31 else (0 : BitVec 3))
  let rtl33 := (state.run && e0 state input)
  let rtl34 := decide (input.cfg.t1 > state.ph)
  let rtl35 := decide (input.cfg.t1 <= nx state input)
  let rtl36 := (rtl34 || rtl35)
  let rtl37 := decide (state.ph < input.cfg.t1)
  let rtl38 := decide (input.cfg.t1 <= nx state input)
  let rtl39 := (rtl37 && rtl38)
  let rtl40 := (if over state input then rtl36 else rtl39)
  let rtl41 := (adv state input && rtl22 && rtl40)
  let rtl42 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.t0edge) 6)) != 0) then rtl33 else rtl41)
  let rtl43 := (state.run && e0 state input && beat state input)
  let rtl44 := decide (input.cfg.t0 <= nx state input)
  let rtl45 := (adv state input && rtl22 && rtl40 && beat state input && over state input && rtl44)
  let rtl46 := (if ((BitVec.truncate 1 (BitVec.ushiftRight (input.cfg.t0edge) 6)) != 0) then rtl43 else rtl45)
  let rtl47 := (!rtl46)
  let rtl48 := (!((BitVec.truncate 1 (BitVec.ushiftRight (state.fired) 0)) != 0))
  let rtl49 := (rtl42 && rtl47 && rtl48)
  let rtl50 := (rtl49 || rtl46)
  let rtl51 := (if rtl50 then pina input else ((BitVec.truncate 1 (BitVec.ushiftRight (state.w) 0)) != 0))
  let rtl52 := decide (input.cfg.t1 > state.ph)
  let rtl53 := decide (input.cfg.t1 <= nx state input)
  let rtl54 := (rtl52 || rtl53)
  let rtl55 := decide (state.ph < input.cfg.t1)
  let rtl56 := decide (input.cfg.t1 <= nx state input)
  let rtl57 := (rtl55 && rtl56)
  let rtl58 := (if over state input then rtl54 else rtl57)
  let rtl59 := decide (input.cfg.t1 <= nx state input)
  let rtl60 := (adv state input && rtl25 && rtl58 && beat state input && over state input && rtl59)
  let rtl61 := (!rtl60)
  let rtl62 := (!((BitVec.truncate 1 (BitVec.ushiftRight (state.fired) 1)) != 0))
  let rtl63 := (adv state input && rtl25 && rtl58 && rtl61 && rtl62)
  let rtl64 := (rtl63 || rtl60)
  let rtl65 := (if rtl64 then pina input else ((BitVec.truncate 1 (BitVec.ushiftRight (state.w) 1)) != 0))
  let rtl66 := decide (input.cfg.t2 > state.ph)
  let rtl67 := decide (input.cfg.t2 <= nx state input)
  let rtl68 := (rtl66 || rtl67)
  let rtl69 := decide (state.ph < input.cfg.t2)
  let rtl70 := decide (input.cfg.t2 <= nx state input)
  let rtl71 := (rtl69 && rtl70)
  let rtl72 := (if over state input then rtl68 else rtl71)
  let rtl73 := decide (input.cfg.t2 <= nx state input)
  let rtl74 := (adv state input && rtl28 && rtl72 && beat state input && over state input && rtl73)
  let rtl75 := (!rtl74)
  let rtl76 := (!((BitVec.truncate 1 (BitVec.ushiftRight (state.fired) 2)) != 0))
  let rtl77 := (adv state input && rtl28 && rtl72 && rtl75 && rtl76)
  let rtl78 := (rtl77 || rtl74)
  let rtl79 := (if rtl78 then pina input else ((BitVec.truncate 1 (BitVec.ushiftRight (state.w) 2)) != 0))
  let rtl80 := (if rtl64 then pinb input else ((BitVec.truncate 1 (BitVec.ushiftRight (state.w) 3)) != 0))
  let rtl81 := (if input.resetN then ((((if rtl80 then (1 : BitVec 1) else 0) ++ (if rtl79 then (1 : BitVec 1) else 0)) ++ (if rtl65 then (1 : BitVec 1) else 0)) ++ (if rtl51 then (1 : BitVec 1) else 0)) else (0 : BitVec 4))
  let rtl82 := (if snap state input then ((((if rtl80 then (1 : BitVec 1) else 0) ++ (if rtl79 then (1 : BitVec 1) else 0)) ++ (if rtl65 then (1 : BitVec 1) else 0)) ++ (if rtl51 then (1 : BitVec 1) else 0)) else state.sn)
  let rtl83 := (if input.resetN then rtl82 else (0 : BitVec 4))
  let rtl84 := (((BitVec.ushiftRight (input.cfg.lut1) (((if state.rem then (1 : BitVec 1) else 0) ++ (BitVec.truncate 4 (BitVec.ushiftRight (state.sn) 0)))).toNat) &&& (1 : BitVec 32)) != 0)
  let rtl85 := (if snap state input then rtl84 else state.rem)
  let rtl86 := (if input.resetN then rtl85 else false)
  let rtl87 := (if input.resetN then stagedNext state input else (0 : BitVec 4))
  let rtl88 := (beat state input || starting state input)
  let rtl89 := (if rtl88 then stagedNext state input else state.committed)
  let rtl90 := (if input.resetN then rtl89 else (0 : BitVec 4))
  let rtl91 := (input.hStatWe && ((BitVec.truncate 1 (BitVec.ushiftRight (input.hD) 0)) != 0))
  let rtl92 := (!rtl91)
  let rtl93 := (state.tapmiss && rtl92)
  let rtl94 := (missEv state input || rtl93)
  let rtl95 := (if input.resetN then rtl94 else false)
  { ph := rtl0, run := rtl1, arm := rtl3,
    ren := rtl5, held := rtl7, first := rtl11,
    sc := rtl15, sp := rtl20, fired := rtl32,
    w := rtl81, sn := rtl83, rem := rtl86,
    staged := rtl87, committed := rtl90,
    tapmiss := rtl95 }

/-! ## Layer equations

Each intermediate net of `src/md2_line.v` is its specification sub-function.
`line_check.py` emits one theorem per layer, in dependency order. -/

theorem rtlEdg_eq (state : State) (input : Input) : rtlEdg input = edge state input := by
  simp only [rtlEdg, edge, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlE0_eq (state : State) (input : Input) : rtlE0 input = e0 state input := by
  simp only [rtlE0, e0, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlRuna_eq (state : State) (input : Input) : rtlRuna state input = runa state input := by
  simp only [rtlRuna, runa, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlInwin_eq (state : State) (input : Input) : rtlInwin state input = inwin state input := by
  simp only [rtlInwin, inwin, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlStart_eq (state : State) (input : Input) : rtlStart state input = start state input := by
  simp only [rtlStart, start, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlAccept_eq (state : State) (input : Input) : rtlAccept state input = accept state input := by
  simp only [rtlAccept, accept, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlN_eq (state : State) (input : Input) : rtlN state input = sum17 state input := by
  simp only [rtlN, sum17, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlOver_eq (state : State) (input : Input) : rtlOver state input = over state input := by
  simp only [rtlOver, over, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlNxw_eq (state : State) (input : Input) : rtlNxw state input = nxw state input := by
  simp only [rtlNxw, nxw, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlNx_eq (state : State) (input : Input) : rtlNx state input = nx state input := by
  simp only [rtlNx, nx, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlTh_eq (input : Input) : rtlTh input = holdTap input := by
  simp only [rtlTh, holdTap, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlHTok_eq (state : State) (input : Input) : rtlHTok input = holdTok state input := by
  simp only [rtlHTok, holdTok, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlHold_eq (state : State) (input : Input) : rtlHold state input = hold state input := by
  simp only [rtlHold, hold, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlAdv_eq (state : State) (input : Input) : rtlAdv state input = adv state input := by
  simp only [rtlAdv, adv, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlWrap_eq (state : State) (input : Input) : rtlWrap state input = wrap state input := by
  simp only [rtlWrap, wrap, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlBeatOut_eq (state : State) (input : Input) : rtlBeatOut state input = beat state input := by
  simp only [rtlBeatOut, beat, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlMissEv_eq (state : State) (input : Input) : rtlMissEv state input = missEv state input := by
  simp only [rtlMissEv, missEv, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlFiredNext_eq (state : State) (input : Input) : rtlFiredNext state input = firedNext state input := by
  simp only [rtlFiredNext, firedNext, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlSnap_eq (state : State) (input : Input) : rtlSnap state input = snap state input := by
  simp only [rtlSnap, snap, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlPhC_eq (state : State) (input : Input) : rtlPhC state input = phC state input := by
  simp only [rtlPhC, phC, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlPhF_eq (state : State) (input : Input) : rtlPhF state input = phF state input := by
  simp only [rtlPhF, phF, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlRunC_eq (state : State) (input : Input) : rtlRunC state input = runC state input := by
  simp only [rtlRunC, runC, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlArmC_eq (state : State) (input : Input) : rtlArmC state input = armC state input := by
  simp only [rtlArmC, armC, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlRenC_eq (state : State) (input : Input) : rtlRenC state input = renC state input := by
  simp only [rtlRenC, renC, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlRunF_eq (state : State) (input : Input) : rtlRunF state input = runF state input := by
  simp only [rtlRunF, runF, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlStarting_eq (state : State) (input : Input) : rtlStarting state input = starting state input := by
  simp only [rtlStarting, starting, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlStagedN_eq (state : State) (input : Input) : rtlStagedN state input = stagedNext state input := by
  simp only [rtlStagedN, stagedNext, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlSegValue_eq (state : State) : rtlSegValue state = seg state := by
  simp only [rtlSegValue, seg, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlPinaIn_eq (input : Input) : rtlPinaIn input = pina input := by
  simp only [rtlPinaIn, pina, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlPinbIn_eq (input : Input) : rtlPinbIn input = pinb input := by
  simp only [rtlPinbIn, pinb, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlPinaRiseIn_eq (input : Input) : rtlPinaRiseIn input = pinaRise input := by
  simp only [rtlPinaRiseIn, pinaRise, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlPinaFallIn_eq (input : Input) : rtlPinaFallIn input = pinaFall input := by
  simp only [rtlPinaFallIn, pinaFall, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlTapOut_eq (state : State) (input : Input) : rtlTapOut state input = tap state input := by
  simp only [rtlTapOut, tap, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlInSymOut_eq (state : State) (input : Input) : rtlInSymOut state input = inSym state input := by
  simp only [rtlInSymOut, inSym, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

theorem rtlCapValue_eq (state : State) : rtlCapValue state = cap state := by
  simp only [rtlCapValue, cap, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl


/-! ## The extracted transition is the specification

The transition binds every intermediate net to its specification sub-function,
so each register equation is the same formula on both sides. -/

/-- The extracted `PH` next state is the specification's. -/
theorem rtlPh (state : State) (input : Input) :
    (rtlStep state input).ph = (step state input).ph := by
  simp only [rtlStep, step, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl
/-- The extracted `RUN` next state is the specification's. -/
theorem rtlRun (state : State) (input : Input) :
    (rtlStep state input).run = (step state input).run := by
  simp only [rtlStep, step, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl
/-- The extracted `ARM` next state is the specification's. -/
theorem rtlArm (state : State) (input : Input) :
    (rtlStep state input).arm = (step state input).arm := by
  simp only [rtlStep, step, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl
/-- The extracted `REN` next state is the specification's. -/
theorem rtlRen (state : State) (input : Input) :
    (rtlStep state input).ren = (step state input).ren := by
  simp only [rtlStep, step, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl
/-- The extracted `HELD` next state is the specification's. -/
theorem rtlHeld (state : State) (input : Input) :
    (rtlStep state input).held = (step state input).held := by
  simp only [rtlStep, step, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl
/-- The extracted `FIRST` next state is the specification's. -/
theorem rtlFirst (state : State) (input : Input) :
    (rtlStep state input).first = (step state input).first := by
  simp only [rtlStep, step, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl
/-- The extracted `SC` next state is the specification's. -/
theorem rtlSc (state : State) (input : Input) :
    (rtlStep state input).sc = (step state input).sc := by
  simp only [rtlStep, step, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl
/-- The extracted `SP` next state is the specification's. -/
theorem rtlSp (state : State) (input : Input) :
    (rtlStep state input).sp = (step state input).sp := by
  simp only [rtlStep, step, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl
/-- The extracted `FIRED` next state is the specification's. -/
theorem rtlFired (state : State) (input : Input) :
    (rtlStep state input).fired = (step state input).fired := by
  simp only [rtlStep, step, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl
/-- The extracted `W` next state is the specification's. -/
theorem rtlW (state : State) (input : Input) :
    (rtlStep state input).w = (step state input).w := by
  simp only [rtlStep, step, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl
/-- The extracted `SN` next state is the specification's. -/
theorem rtlSn (state : State) (input : Input) :
    (rtlStep state input).sn = (step state input).sn := by
  simp only [rtlStep, step, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl
/-- The extracted `REM` next state is the specification's. -/
theorem rtlRem (state : State) (input : Input) :
    (rtlStep state input).rem = (step state input).rem := by
  simp only [rtlStep, step, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl
/-- The extracted `STAGED` next state is the specification's. -/
theorem rtlStaged (state : State) (input : Input) :
    (rtlStep state input).staged = (step state input).staged := by
  simp only [rtlStep, step, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl
/-- The extracted `COMMITTED` next state is the specification's. -/
theorem rtlCommitted (state : State) (input : Input) :
    (rtlStep state input).committed = (step state input).committed := by
  simp only [rtlStep, step, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl
/-- The extracted `TAPMISS` next state is the specification's. -/
theorem rtlTapmiss (state : State) (input : Input) :
    (rtlStep state input).tapmiss = (step state input).tapmiss := by
  simp only [rtlStep, step, esel, crossing, tlt0, tlt1, tlt2, tapCross0, tapCross1, tapCross2, cross0, next0, next1, next2, cur0, cur1, cur2, crossBits, nextBits, curBits, tap0, tap1, tap2, enBits, missOk, missBits, wNext, tap, cap, inSym, committedNext, startBits, scNext, spNext, armF, renF, pack3, pack4, slice, bitAt, sel, ite_ite_zero, ite_ite_false, Config.edgePin, Config.edgePol, Config.wen, Config.follow, Config.t0Pin, Config.t0Pol, Config.t0src, Config.pinaSel, Config.pinbSel, Config.hpin, Config.hlvl, Config.htap, Config.hen] <;> rfl

/-- The elaborated line transition matches the independent SPEC_V2 §3
specification for every state and input: all fifteen register values and the
combinational outputs (their layer equations above). -/
theorem rtlStep_eq_step (state : State) (input : Input) :
    rtlStep state input = step state input := by
  simp only [rtlStep, step] <;> rfl
set_option linter.unusedSimpArgs false

/-! ## Traces

The layer and register equations above say the elaborated transition is the
specification's; the specification's `stateAt` theorems therefore hold of the
RTL. -/

/-- The register state of the extracted transition during cycle `n`. -/
def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun state input => rtlStep state input) inputs initial n

theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt inputs initial n :=
  run_congr (fun state input => rtlStep_eq_step state input) inputs initial n

theorem rtl_trace_result (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStep (rtlStateAt inputs initial n) (inputs n) =
      step (stateAt inputs initial n) (inputs n) := by
  rw [rtlStateAt_eq, rtlStep_eq_step]

/-- A sampled reset edge of the extracted trace leaves the reset state. -/
theorem rtl_trace_reset (inputs : Nat → Input) (initial : State)
    (reset : (inputs 0).resetN = false) : rtlStateAt inputs initial 1 = resetState := by
  rw [rtlStateAt_eq]
  exact stateAt_one_reset inputs initial reset

/-- A frozen `FOLLOW = 0` cycle with no move and no host write of the extracted
trace leaves it unchanged: deleting it gives the same state sequence (§12.3). -/
theorem rtl_trace_frz_holds (inputs : Nat → Input) (initial : State) (n : Nat)
    (hreset : (inputs n).resetN = true) (hfrz : (inputs n).frz = true)
    (hfollow : (inputs n).cfg.follow = false) (hctl : (inputs n).ctlWe = false)
    (hsym : (inputs n).symWe = false) (hph : (inputs n).phWe = 0)
    (hhctl : (inputs n).hCtlWe = false) (hhstat : (inputs n).hStatWe = false) :
    rtlStateAt inputs initial (n + 1) = rtlStateAt inputs initial n := by
  rw [rtlStateAt_eq]
  exact trace_frz_holds inputs initial n hreset hfrz hfollow hctl hsym hph hhctl hhstat

/-! ## Axiom audit

`line_check.py` records these records and rejects `sorryAx`. -/

#print axioms rtlStep_eq_step
#print axioms rtlStateAt_eq
#print axioms rtl_trace_frz_holds
#print axioms rtlEdg_eq
#print axioms rtlE0_eq
#print axioms rtlRuna_eq
#print axioms rtlInwin_eq
#print axioms rtlStart_eq
#print axioms rtlAccept_eq
#print axioms rtlN_eq
#print axioms rtlOver_eq
#print axioms rtlNxw_eq
#print axioms rtlNx_eq
#print axioms rtlTh_eq
#print axioms rtlHTok_eq
#print axioms rtlHold_eq
#print axioms rtlAdv_eq
#print axioms rtlWrap_eq
#print axioms rtlBeatOut_eq
#print axioms rtlMissEv_eq
#print axioms rtlFiredNext_eq
#print axioms rtlSnap_eq
#print axioms rtlPhC_eq
#print axioms rtlPhF_eq
#print axioms rtlRunC_eq
#print axioms rtlArmC_eq
#print axioms rtlRenC_eq
#print axioms rtlRunF_eq
#print axioms rtlStarting_eq
#print axioms rtlStagedN_eq
#print axioms rtlSegValue_eq
#print axioms rtlPinaIn_eq
#print axioms rtlPinbIn_eq
#print axioms rtlPinaRiseIn_eq
#print axioms rtlPinaFallIn_eq
#print axioms rtlTapOut_eq
#print axioms rtlInSymOut_eq
#print axioms rtlCapValue_eq
#print axioms rtl_trace_reset
#print axioms rtlPh
#print axioms rtlRun
#print axioms rtlArm
#print axioms rtlRen
#print axioms rtlHeld
#print axioms rtlFirst
#print axioms rtlSc
#print axioms rtlSp
#print axioms rtlFired
#print axioms rtlW
#print axioms rtlSn
#print axioms rtlRem
#print axioms rtlStaged
#print axioms rtlCommitted
#print axioms rtlTapmiss
