import Metronome.Units

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 411703d96e7be470b1e355a1fa4cdc340aff379a5b11547e59d84fcdde14e882
-- Units: the `md2_counter`, `md2_shifter`, `md2_lfsr` and `md2_acc` instances
-- of tt_um_brentius_metronome.  Every register of every unit is sampled; the thirteen register
-- values are symbolic, as are the move, configuration and reset inputs.

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Metronome.Units.Counter

/-- The elaborated counter transition (`V`). -/
def rtlStep (state : State) (input : Input) : State :=
  let rtl0 := (if (state.v != 0) then (1 : BitVec 1) else 0)
  let rtl1 := (state.v - (1 : BitVec 16))
  let rtl2 := (if (rtl0 != 0) then rtl1 else (0 : BitVec 16))
  let rtl3 := (if (input.sel == (1 : BitVec 2)) then (1 : BitVec 1) else 0)
  let rtl4 := (if (rtl3 != 0) then input.d else (BitVec.truncate 8 (BitVec.ushiftRight state.v 0)))
  let rtl5 := (if ((BitVec.truncate 1 (BitVec.ushiftRight input.sel 1)) != 0) then ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else rtl4)
  let rtl6 := (if ((if input.we then (1 : BitVec 1) else 0) != 0) then rtl5 else (BitVec.truncate 8 (BitVec.ushiftRight state.v 0)))
  let rtl7 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl6 else (0 : BitVec 8))
  let rtl8 := (if (input.sel == (0 : BitVec 2)) then (1 : BitVec 1) else 0)
  let rtl9 := (if (rtl8 != 0) then input.d else (BitVec.truncate 8 (BitVec.ushiftRight state.v 8)))
  let rtl10 := (if ((BitVec.truncate 1 (BitVec.ushiftRight input.sel 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl2 8)) else rtl9)
  let rtl11 := (if ((if input.we then (1 : BitVec 1) else 0) != 0) then rtl10 else (BitVec.truncate 8 (BitVec.ushiftRight state.v 8)))
  let rtl12 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl11 else (0 : BitVec 8))
  ⟨((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl7 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl7 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl7 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl7 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl7 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl7 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl7 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl7 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl12 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl12 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl12 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl12 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl12 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl12 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl12 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl12 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16)))⟩

/-- The elaborated `Z` output. -/
def rtlZ (state : State) : Bool :=
  let rtlz0 := (if (state.v == (0 : BitVec 16)) then (1 : BitVec 1) else 0)
  (rtlz0 != 0)

end Metronome.Units.Counter

namespace Metronome.Units.Shifter

/-- The elaborated shifter transition (`D`, `CNT`, `LEN`, `MSB`). -/
def rtlStep (state : State) (input : Input) : State :=
  let rtl0 := (if !((if input.sel then (1 : BitVec 1) else 0) != 0) then (1 : BitVec 1) else 0)
  let rtl1 := (if ((if input.we then (1 : BitVec 1) else 0) != 0) && (rtl0 != 0) then (1 : BitVec 1) else 0)
  let rtl2 := (if ((if state.msb then (1 : BitVec 1) else 0) != 0) then ((if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.dr 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.dr 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.dr 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.dr 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.dr 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.dr 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.dr 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else ((if ((BitVec.truncate 1 (BitVec.ushiftRight state.dr 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.dr 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.dr 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.dr 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.dr 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.dr 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.dr 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))))
  let rtl3 := (if ((if input.we then (1 : BitVec 1) else 0) != 0) then rtl2 else state.dr)
  let rtl4 := (if (rtl1 != 0) then input.d else rtl3)
  let rtl5 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl4 else (0 : BitVec 8))
  let rtl6 := (if (state.len != 0) then (1 : BitVec 1) else 0)
  let rtl7 := (if (rtl6 != 0) then state.len else (8 : BitVec 4))
  let rtl8 := (if (state.cnt != 0) then (1 : BitVec 1) else 0)
  let rtl9 := (state.cnt - (1 : BitVec 4))
  let rtl10 := (if (rtl8 != 0) then rtl9 else (0 : BitVec 4))
  let rtl11 := (if ((if input.we then (1 : BitVec 1) else 0) != 0) then rtl10 else state.cnt)
  let rtl12 := (if (rtl1 != 0) then rtl7 else rtl11)
  let rtl13 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl12 else (0 : BitVec 4))
  let rtl14 := (if ((if input.cfgWe then (1 : BitVec 1) else 0) != 0) then (BitVec.truncate 4 (BitVec.ushiftRight input.cfgD 0)) else state.len)
  let rtl15 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl14 else (0 : BitVec 4))
  let rtl16 := (if ((if input.cfgWe then (1 : BitVec 1) else 0) != 0) then (BitVec.truncate 1 (BitVec.ushiftRight input.cfgD 4)) else (if state.msb then (1 : BitVec 1) else 0))
  let rtl17 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl16 else (0 : BitVec 1))
  ⟨rtl5, rtl13, rtl15, (rtl17 != 0)⟩

/-- The elaborated `O` output. -/
def rtlO (state : State) : Bool :=
  let rtlo0 := (if ((if state.msb then (1 : BitVec 1) else 0) != 0) then (BitVec.truncate 1 (BitVec.ushiftRight state.dr 7)) else (BitVec.truncate 1 (BitVec.ushiftRight state.dr 0)))
  (rtlo0 != 0)

/-- The elaborated `DONE` output. -/
def rtlDone (state : State) : Bool :=
  let rtldone0 := (if (state.cnt == (0 : BitVec 4)) then (1 : BitVec 1) else 0)
  (rtldone0 != 0)

end Metronome.Units.Shifter

namespace Metronome.Units.Lfsr

/-- The elaborated LFSR transition (`S`). -/
def rtlStep (state : State) (input : Input) : State :=
  let rtl0 := (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 0)) != 0) then (0 : BitVec 32) else input.poly)
  let rtl1 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 16)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 17)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 18)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 19)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 20)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 21)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 22)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 23)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 24)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 25)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 26)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 27)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 28)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 29)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 30)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 31)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) ^^^ rtl0)
  let rtl2 := (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 0)) != 0) then input.poly else (0 : BitVec 32))
  let rtl3 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 16)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 17)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 18)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 19)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 20)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 21)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 22)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 23)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 24)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 25)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 26)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 27)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 28)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 29)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 30)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.s 31)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32))) ^^^ rtl2)
  let rtl4 := (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 0)) != 0) then rtl1 else rtl3)
  let rtl5 := (if (input.sel == (0 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl6 := (if (input.sel == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl7 := (if (rtl6 != 0) then input.d else (if (rtl5 != 0) then ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl4 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl4 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl4 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl4 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl4 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl4 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl4 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl4 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else (BitVec.truncate 8 (BitVec.ushiftRight state.s 0))))
  let rtl8 := (if ((if input.we then (1 : BitVec 1) else 0) != 0) then rtl7 else (BitVec.truncate 8 (BitVec.ushiftRight state.s 0)))
  let rtl9 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl8 else (0 : BitVec 8))
  let rtl10 := (if (input.sel == (0 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl11 := (if (input.sel == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl12 := (if (rtl11 != 0) then input.d else (if (rtl10 != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl4 8)) else (BitVec.truncate 8 (BitVec.ushiftRight state.s 8))))
  let rtl13 := (if ((if input.we then (1 : BitVec 1) else 0) != 0) then rtl12 else (BitVec.truncate 8 (BitVec.ushiftRight state.s 8)))
  let rtl14 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl13 else (0 : BitVec 8))
  let rtl15 := (if (input.sel == (0 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl16 := (if (input.sel == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl17 := (if (rtl16 != 0) then input.d else (if (rtl15 != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl4 16)) else (BitVec.truncate 8 (BitVec.ushiftRight state.s 16))))
  let rtl18 := (if ((if input.we then (1 : BitVec 1) else 0) != 0) then rtl17 else (BitVec.truncate 8 (BitVec.ushiftRight state.s 16)))
  let rtl19 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl18 else (0 : BitVec 8))
  let rtl20 := (if (input.sel == (0 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl21 := (if (input.sel == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl22 := (if (rtl21 != 0) then input.d else (if (rtl20 != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl4 24)) else (BitVec.truncate 8 (BitVec.ushiftRight state.s 24))))
  let rtl23 := (if ((if input.we then (1 : BitVec 1) else 0) != 0) then rtl22 else (BitVec.truncate 8 (BitVec.ushiftRight state.s 24)))
  let rtl24 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl23 else (0 : BitVec 8))
  ⟨((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl9 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl9 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl9 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl9 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl9 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl9 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl9 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl9 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl14 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl14 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl14 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl14 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl14 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl14 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl14 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl14 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl19 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl19 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl19 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl19 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl19 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl19 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl19 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl19 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl24 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl24 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl24 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl24 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl24 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl24 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl24 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl24 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32)))⟩

end Metronome.Units.Lfsr

namespace Metronome.Units.Acc

/-- The elaborated accumulator transition (`A`, `Z`, `C`, `N`, `R0..R3`). -/
def rtlStep (state : State) (input : Input) : State :=
  let rtl0 := (if (input.hit != 0) then (1 : BitVec 1) else 0)
  let rtl1 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))) + ((if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))))
  let rtl2 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl3 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 0)))
  let rtl4 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl5 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 0)))
  let rtl6 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl7 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 0)))
  let rtl8 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl9 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 0)))
  let rtl10 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl11 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 0)))
  let rtl12 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl13 := (if (rtl12 != 0) then rtl11 else (if (rtl10 != 0) then rtl9 else (if (rtl8 != 0) then rtl7 else (if (rtl6 != 0) then rtl5 else (if (rtl4 != 0) then rtl3 else (if (rtl2 != 0) then ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl1 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl1 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl1 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl1 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl1 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl1 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl1 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl1 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 0))))))))
  let rtl14 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 0)))
  let rtl15 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 0)))
  let rtl16 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 0)))
  let rtl17 := (if (rtl12 != 0) then rtl11 else (if (rtl10 != 0) then rtl16 else (if (rtl8 != 0) then rtl15 else (if (rtl6 != 0) then rtl14 else (if (rtl4 != 0) then rtl3 else (if (rtl2 != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl1 0)) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 0))))))))
  let rtl18 := (if (rtl17 == (0 : BitVec 8)) then (1 : BitVec 1) else 0)
  let rtl19 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl20 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 0))) then (1 : BitVec 1) else 0)
  let rtl21 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl22 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 0))) then (1 : BitVec 1) else 0)
  let rtl23 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl24 := (if (rtl23 != 0) then rtl22 else (if (rtl21 != 0) then rtl20 else (if (rtl19 != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl1 8)) else (if state.c then (1 : BitVec 1) else 0))))
  let rtl25 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl26 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl27 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl28 := (if (rtl27 != 0) then (1 : BitVec 1) else (if (rtl26 != 0) then (1 : BitVec 1) else (if (rtl25 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))
  let rtl29 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (0 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl30 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl31 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl32 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl33 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl34 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl35 := (if (rtl34 != 0) then (1 : BitVec 1) else (if (rtl33 != 0) then (1 : BitVec 1) else (if (rtl32 != 0) then (1 : BitVec 1) else (if (rtl31 != 0) then (1 : BitVec 1) else (if (rtl30 != 0) then (1 : BitVec 1) else (if (rtl29 != 0) then (1 : BitVec 1) else (0 : BitVec 1)))))))
  let rtl36 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))) &&& ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if (rtl18 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if (rtl24 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if (rtl28 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if (rtl35 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let rtl37 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))) + ((if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))))
  let rtl38 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl39 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl40 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl41 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl42 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl43 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl44 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl45 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl46 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl47 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl48 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl49 := (if (rtl48 != 0) then rtl47 else (if (rtl46 != 0) then rtl45 else (if (rtl44 != 0) then rtl43 else (if (rtl42 != 0) then rtl41 else (if (rtl40 != 0) then rtl39 else (if (rtl38 != 0) then ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl37 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl37 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl37 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl37 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl37 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl37 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl37 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl37 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 8))))))))
  let rtl50 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl51 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl52 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl53 := (if (rtl48 != 0) then rtl47 else (if (rtl46 != 0) then rtl52 else (if (rtl44 != 0) then rtl51 else (if (rtl42 != 0) then rtl50 else (if (rtl40 != 0) then rtl39 else (if (rtl38 != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl37 0)) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 8))))))))
  let rtl54 := (if (rtl53 == (0 : BitVec 8)) then (1 : BitVec 1) else 0)
  let rtl55 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl56 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 8))) then (1 : BitVec 1) else 0)
  let rtl57 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl58 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 8))) then (1 : BitVec 1) else 0)
  let rtl59 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl60 := (if (rtl59 != 0) then rtl58 else (if (rtl57 != 0) then rtl56 else (if (rtl55 != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl37 8)) else (if state.c then (1 : BitVec 1) else 0))))
  let rtl61 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl62 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl63 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl64 := (if (rtl63 != 0) then (1 : BitVec 1) else (if (rtl62 != 0) then (1 : BitVec 1) else (if (rtl61 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))
  let rtl65 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (0 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl66 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl67 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl68 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl69 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl70 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl71 := (if (rtl70 != 0) then (1 : BitVec 1) else (if (rtl69 != 0) then (1 : BitVec 1) else (if (rtl68 != 0) then (1 : BitVec 1) else (if (rtl67 != 0) then (1 : BitVec 1) else (if (rtl66 != 0) then (1 : BitVec 1) else (if (rtl65 != 0) then (1 : BitVec 1) else (0 : BitVec 1)))))))
  let rtl72 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))) &&& ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl49 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl49 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl49 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl49 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl49 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl49 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl49 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl49 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl49 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if (rtl54 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if (rtl60 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if (rtl64 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if (rtl71 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let rtl73 := (rtl36 ||| rtl72)
  let rtl74 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))) + ((if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 16)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 17)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 18)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 19)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 20)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 21)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 22)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 23)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))))
  let rtl75 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl76 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl77 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl78 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl79 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl80 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl81 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl82 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl83 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl84 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl85 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl86 := (if (rtl85 != 0) then rtl84 else (if (rtl83 != 0) then rtl82 else (if (rtl81 != 0) then rtl80 else (if (rtl79 != 0) then rtl78 else (if (rtl77 != 0) then rtl76 else (if (rtl75 != 0) then ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl74 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl74 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl74 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl74 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl74 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl74 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl74 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl74 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 16))))))))
  let rtl87 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl88 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl89 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl90 := (if (rtl85 != 0) then rtl84 else (if (rtl83 != 0) then rtl89 else (if (rtl81 != 0) then rtl88 else (if (rtl79 != 0) then rtl87 else (if (rtl77 != 0) then rtl76 else (if (rtl75 != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl74 0)) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 16))))))))
  let rtl91 := (if (rtl90 == (0 : BitVec 8)) then (1 : BitVec 1) else 0)
  let rtl92 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl93 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 16))) then (1 : BitVec 1) else 0)
  let rtl94 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl95 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 16))) then (1 : BitVec 1) else 0)
  let rtl96 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl97 := (if (rtl96 != 0) then rtl95 else (if (rtl94 != 0) then rtl93 else (if (rtl92 != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl74 8)) else (if state.c then (1 : BitVec 1) else 0))))
  let rtl98 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl99 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl100 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl101 := (if (rtl100 != 0) then (1 : BitVec 1) else (if (rtl99 != 0) then (1 : BitVec 1) else (if (rtl98 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))
  let rtl102 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (0 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl103 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl104 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl105 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl106 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl107 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl108 := (if (rtl107 != 0) then (1 : BitVec 1) else (if (rtl106 != 0) then (1 : BitVec 1) else (if (rtl105 != 0) then (1 : BitVec 1) else (if (rtl104 != 0) then (1 : BitVec 1) else (if (rtl103 != 0) then (1 : BitVec 1) else (if (rtl102 != 0) then (1 : BitVec 1) else (0 : BitVec 1)))))))
  let rtl109 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))) &&& ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl86 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl86 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl86 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl86 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl86 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl86 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl86 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl86 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl86 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if (rtl91 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if (rtl97 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if (rtl101 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if (rtl108 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let rtl110 := (rtl73 ||| rtl109)
  let rtl111 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))) + ((if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 24)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 25)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 26)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 27)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 28)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 29)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 30)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 31)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))))
  let rtl112 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl113 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl114 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl115 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl116 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl117 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl118 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl119 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl120 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl121 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl122 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl123 := (if (rtl122 != 0) then rtl121 else (if (rtl120 != 0) then rtl119 else (if (rtl118 != 0) then rtl117 else (if (rtl116 != 0) then rtl115 else (if (rtl114 != 0) then rtl113 else (if (rtl112 != 0) then ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl111 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl111 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl111 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl111 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl111 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl111 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl111 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl111 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 24))))))))
  let rtl124 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl125 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl126 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl127 := (if (rtl122 != 0) then rtl121 else (if (rtl120 != 0) then rtl126 else (if (rtl118 != 0) then rtl125 else (if (rtl116 != 0) then rtl124 else (if (rtl114 != 0) then rtl113 else (if (rtl112 != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl111 0)) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 24))))))))
  let rtl128 := (if (rtl127 == (0 : BitVec 8)) then (1 : BitVec 1) else 0)
  let rtl129 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl130 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 24))) then (1 : BitVec 1) else 0)
  let rtl131 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl132 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 24))) then (1 : BitVec 1) else 0)
  let rtl133 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl134 := (if (rtl133 != 0) then rtl132 else (if (rtl131 != 0) then rtl130 else (if (rtl129 != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl111 8)) else (if state.c then (1 : BitVec 1) else 0))))
  let rtl135 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl136 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl137 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl138 := (if (rtl137 != 0) then (1 : BitVec 1) else (if (rtl136 != 0) then (1 : BitVec 1) else (if (rtl135 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))
  let rtl139 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (0 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl140 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl141 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl142 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl143 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl144 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl145 := (if (rtl144 != 0) then (1 : BitVec 1) else (if (rtl143 != 0) then (1 : BitVec 1) else (if (rtl142 != 0) then (1 : BitVec 1) else (if (rtl141 != 0) then (1 : BitVec 1) else (if (rtl140 != 0) then (1 : BitVec 1) else (if (rtl139 != 0) then (1 : BitVec 1) else (0 : BitVec 1)))))))
  let rtl146 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))) &&& ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl123 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl123 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl123 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl123 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl123 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl123 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl123 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl123 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl123 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if (rtl128 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if (rtl134 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if (rtl138 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if (rtl145 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let rtl147 := (rtl110 ||| rtl146)
  let rtl148 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))) + ((if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 32)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 33)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 34)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 35)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 36)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 37)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 38)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 39)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))))
  let rtl149 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl150 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl151 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl152 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl153 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl154 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl155 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl156 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl157 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl158 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl159 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl160 := (if (rtl159 != 0) then rtl158 else (if (rtl157 != 0) then rtl156 else (if (rtl155 != 0) then rtl154 else (if (rtl153 != 0) then rtl152 else (if (rtl151 != 0) then rtl150 else (if (rtl149 != 0) then ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl148 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl148 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl148 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl148 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl148 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl148 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl148 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl148 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 32))))))))
  let rtl161 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl162 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl163 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl164 := (if (rtl159 != 0) then rtl158 else (if (rtl157 != 0) then rtl163 else (if (rtl155 != 0) then rtl162 else (if (rtl153 != 0) then rtl161 else (if (rtl151 != 0) then rtl150 else (if (rtl149 != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl148 0)) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 32))))))))
  let rtl165 := (if (rtl164 == (0 : BitVec 8)) then (1 : BitVec 1) else 0)
  let rtl166 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl167 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 32))) then (1 : BitVec 1) else 0)
  let rtl168 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl169 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 32))) then (1 : BitVec 1) else 0)
  let rtl170 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl171 := (if (rtl170 != 0) then rtl169 else (if (rtl168 != 0) then rtl167 else (if (rtl166 != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl148 8)) else (if state.c then (1 : BitVec 1) else 0))))
  let rtl172 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl173 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl174 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl175 := (if (rtl174 != 0) then (1 : BitVec 1) else (if (rtl173 != 0) then (1 : BitVec 1) else (if (rtl172 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))
  let rtl176 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (0 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl177 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl178 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl179 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl180 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl181 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl182 := (if (rtl181 != 0) then (1 : BitVec 1) else (if (rtl180 != 0) then (1 : BitVec 1) else (if (rtl179 != 0) then (1 : BitVec 1) else (if (rtl178 != 0) then (1 : BitVec 1) else (if (rtl177 != 0) then (1 : BitVec 1) else (if (rtl176 != 0) then (1 : BitVec 1) else (0 : BitVec 1)))))))
  let rtl183 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))) &&& ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl160 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl160 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl160 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl160 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl160 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl160 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl160 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl160 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl160 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if (rtl165 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if (rtl171 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if (rtl175 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if (rtl182 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let rtl184 := (rtl147 ||| rtl183)
  let rtl185 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))) + ((if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 40)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 41)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 42)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 43)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 44)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 45)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 46)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 47)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))))
  let rtl186 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl187 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl188 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl189 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl190 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl191 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl192 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl193 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl194 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl195 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl196 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl197 := (if (rtl196 != 0) then rtl195 else (if (rtl194 != 0) then rtl193 else (if (rtl192 != 0) then rtl191 else (if (rtl190 != 0) then rtl189 else (if (rtl188 != 0) then rtl187 else (if (rtl186 != 0) then ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl185 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl185 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl185 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl185 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl185 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl185 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl185 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl185 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 40))))))))
  let rtl198 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl199 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl200 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl201 := (if (rtl196 != 0) then rtl195 else (if (rtl194 != 0) then rtl200 else (if (rtl192 != 0) then rtl199 else (if (rtl190 != 0) then rtl198 else (if (rtl188 != 0) then rtl187 else (if (rtl186 != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl185 0)) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 40))))))))
  let rtl202 := (if (rtl201 == (0 : BitVec 8)) then (1 : BitVec 1) else 0)
  let rtl203 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl204 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 40))) then (1 : BitVec 1) else 0)
  let rtl205 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl206 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 40))) then (1 : BitVec 1) else 0)
  let rtl207 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl208 := (if (rtl207 != 0) then rtl206 else (if (rtl205 != 0) then rtl204 else (if (rtl203 != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl185 8)) else (if state.c then (1 : BitVec 1) else 0))))
  let rtl209 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl210 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl211 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl212 := (if (rtl211 != 0) then (1 : BitVec 1) else (if (rtl210 != 0) then (1 : BitVec 1) else (if (rtl209 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))
  let rtl213 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (0 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl214 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl215 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl216 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl217 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl218 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl219 := (if (rtl218 != 0) then (1 : BitVec 1) else (if (rtl217 != 0) then (1 : BitVec 1) else (if (rtl216 != 0) then (1 : BitVec 1) else (if (rtl215 != 0) then (1 : BitVec 1) else (if (rtl214 != 0) then (1 : BitVec 1) else (if (rtl213 != 0) then (1 : BitVec 1) else (0 : BitVec 1)))))))
  let rtl220 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))) &&& ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl197 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl197 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl197 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl197 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl197 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl197 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl197 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl197 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl197 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if (rtl202 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if (rtl208 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if (rtl212 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if (rtl219 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let rtl221 := (rtl184 ||| rtl220)
  let rtl222 := (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl221 12)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl221 0)) else state.a)
  let rtl223 := (if (rtl0 != 0) then rtl222 else state.a)
  let rtl224 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl223 else (0 : BitVec 8))
  let rtl225 := (if (rtl0 != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl221 9)) else (if state.z then (1 : BitVec 1) else 0))
  let rtl226 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl225 else (0 : BitVec 1))
  let rtl227 := (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl221 11)) != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl221 10)) else (if state.c then (1 : BitVec 1) else 0))
  let rtl228 := (if (rtl0 != 0) then rtl227 else (if state.c then (1 : BitVec 1) else 0))
  let rtl229 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl228 else (0 : BitVec 1))
  let rtl230 := (if (rtl0 != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl221 8)) else (if state.n then (1 : BitVec 1) else 0))
  let rtl231 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl230 else (0 : BitVec 1))
  let rtl232 := (if ((BitVec.truncate 1 (BitVec.ushiftRight input.rWe 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.rD 0)) else (BitVec.truncate 8 (BitVec.ushiftRight state.r 0)))
  let rtl233 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl232 else (0 : BitVec 8))
  let rtl234 := (if ((BitVec.truncate 1 (BitVec.ushiftRight input.rWe 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.rD 8)) else (BitVec.truncate 8 (BitVec.ushiftRight state.r 8)))
  let rtl235 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl234 else (0 : BitVec 8))
  let rtl236 := (if ((BitVec.truncate 1 (BitVec.ushiftRight input.rWe 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.rD 16)) else (BitVec.truncate 8 (BitVec.ushiftRight state.r 16)))
  let rtl237 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl236 else (0 : BitVec 8))
  let rtl238 := (if ((BitVec.truncate 1 (BitVec.ushiftRight input.rWe 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.rD 24)) else (BitVec.truncate 8 (BitVec.ushiftRight state.r 24)))
  let rtl239 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl238 else (0 : BitVec 8))
  ⟨rtl224, (rtl226 != 0), (rtl229 != 0), (rtl231 != 0), ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl233 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl233 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl233 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl233 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl233 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl233 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl233 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl233 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl235 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl235 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl235 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl235 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl235 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl235 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl235 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl235 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl237 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl237 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl237 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl237 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl237 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl237 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl237 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl237 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32)))⟩

end Metronome.Units.Acc

namespace Metronome.Units.Counter


def rtlSel0 (opLo opHi : Bool) : BitVec 2 :=
    let sel_counter00 := (if ((if opHi then (1 : BitVec 1) else 0) != 0) then (1 : BitVec 2) else (2 : BitVec 2))
    let sel_counter01 := (if ((if opLo then (1 : BitVec 1) else 0) != 0) then (0 : BitVec 2) else sel_counter00)
  sel_counter01


def rtlSel1 (opLo opHi : Bool) : BitVec 2 :=
    let sel_counter10 := (if ((if opHi then (1 : BitVec 1) else 0) != 0) then (1 : BitVec 2) else (2 : BitVec 2))
    let sel_counter11 := (if ((if opLo then (1 : BitVec 1) else 0) != 0) then (0 : BitVec 2) else sel_counter10)
  sel_counter11


def rtlSel2 (opLo opHi : Bool) : BitVec 2 :=
    let sel_counter20 := (if ((if opHi then (1 : BitVec 1) else 0) != 0) then (1 : BitVec 2) else (2 : BitVec 2))
    let sel_counter21 := (if ((if opLo then (1 : BitVec 1) else 0) != 0) then (0 : BitVec 2) else sel_counter20)
  sel_counter21

end Metronome.Units.Counter

namespace Metronome.Units.Lfsr


def rtlSel0 (opSt opB0 opB1 opB2 : Bool) : BitVec 3 :=
    let sel_lfsr00 := (if ((if opB2 then (1 : BitVec 1) else 0) != 0) then (3 : BitVec 3) else (4 : BitVec 3))
    let sel_lfsr01 := (if ((if opB1 then (1 : BitVec 1) else 0) != 0) then (2 : BitVec 3) else sel_lfsr00)
    let sel_lfsr02 := (if ((if opB0 then (1 : BitVec 1) else 0) != 0) then (1 : BitVec 3) else sel_lfsr01)
    let sel_lfsr03 := (if ((if opSt then (1 : BitVec 1) else 0) != 0) then (0 : BitVec 3) else sel_lfsr02)
  sel_lfsr03


def rtlSel1 (opSt opB0 opB1 opB2 : Bool) : BitVec 3 :=
    let sel_lfsr10 := (if ((if opB2 then (1 : BitVec 1) else 0) != 0) then (3 : BitVec 3) else (4 : BitVec 3))
    let sel_lfsr11 := (if ((if opB1 then (1 : BitVec 1) else 0) != 0) then (2 : BitVec 3) else sel_lfsr10)
    let sel_lfsr12 := (if ((if opB0 then (1 : BitVec 1) else 0) != 0) then (1 : BitVec 3) else sel_lfsr11)
    let sel_lfsr13 := (if ((if opSt then (1 : BitVec 1) else 0) != 0) then (0 : BitVec 3) else sel_lfsr12)
  sel_lfsr13

end Metronome.Units.Lfsr

namespace Metronome.Units.Acc


def rtlSel0 (cDst : BitVec 36) : BitVec 3 :=
    let accsel00 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 0)) == (7 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel01 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 0)) == (8 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel02 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 0)) == (9 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel03 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 0)) == (10 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel04 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 0)) == (11 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel05 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 0)) == (12 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel06 := (if (accsel05 != 0) then (5 : BitVec 3) else (if (accsel04 != 0) then (4 : BitVec 3) else (if (accsel03 != 0) then (3 : BitVec 3) else (if (accsel02 != 0) then (2 : BitVec 3) else (if (accsel01 != 0) then (1 : BitVec 3) else (if (accsel00 != 0) then (0 : BitVec 3) else (6 : BitVec 3)))))))
  accsel06


def rtlSel1 (cDst : BitVec 36) : BitVec 3 :=
    let accsel10 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 6)) == (7 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel11 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 6)) == (8 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel12 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 6)) == (9 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel13 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 6)) == (10 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel14 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 6)) == (11 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel15 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 6)) == (12 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel16 := (if (accsel15 != 0) then (5 : BitVec 3) else (if (accsel14 != 0) then (4 : BitVec 3) else (if (accsel13 != 0) then (3 : BitVec 3) else (if (accsel12 != 0) then (2 : BitVec 3) else (if (accsel11 != 0) then (1 : BitVec 3) else (if (accsel10 != 0) then (0 : BitVec 3) else (6 : BitVec 3)))))))
  accsel16


def rtlSel2 (cDst : BitVec 36) : BitVec 3 :=
    let accsel20 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 12)) == (7 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel21 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 12)) == (8 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel22 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 12)) == (9 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel23 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 12)) == (10 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel24 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 12)) == (11 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel25 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 12)) == (12 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel26 := (if (accsel25 != 0) then (5 : BitVec 3) else (if (accsel24 != 0) then (4 : BitVec 3) else (if (accsel23 != 0) then (3 : BitVec 3) else (if (accsel22 != 0) then (2 : BitVec 3) else (if (accsel21 != 0) then (1 : BitVec 3) else (if (accsel20 != 0) then (0 : BitVec 3) else (6 : BitVec 3)))))))
  accsel26


def rtlSel3 (cDst : BitVec 36) : BitVec 3 :=
    let accsel30 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 18)) == (7 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel31 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 18)) == (8 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel32 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 18)) == (9 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel33 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 18)) == (10 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel34 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 18)) == (11 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel35 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 18)) == (12 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel36 := (if (accsel35 != 0) then (5 : BitVec 3) else (if (accsel34 != 0) then (4 : BitVec 3) else (if (accsel33 != 0) then (3 : BitVec 3) else (if (accsel32 != 0) then (2 : BitVec 3) else (if (accsel31 != 0) then (1 : BitVec 3) else (if (accsel30 != 0) then (0 : BitVec 3) else (6 : BitVec 3)))))))
  accsel36


def rtlSel4 (cDst : BitVec 36) : BitVec 3 :=
    let accsel40 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 24)) == (7 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel41 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 24)) == (8 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel42 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 24)) == (9 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel43 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 24)) == (10 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel44 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 24)) == (11 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel45 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 24)) == (12 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel46 := (if (accsel45 != 0) then (5 : BitVec 3) else (if (accsel44 != 0) then (4 : BitVec 3) else (if (accsel43 != 0) then (3 : BitVec 3) else (if (accsel42 != 0) then (2 : BitVec 3) else (if (accsel41 != 0) then (1 : BitVec 3) else (if (accsel40 != 0) then (0 : BitVec 3) else (6 : BitVec 3)))))))
  accsel46


def rtlSel5 (cDst : BitVec 36) : BitVec 3 :=
    let accsel50 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 30)) == (7 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel51 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 30)) == (8 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel52 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 30)) == (9 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel53 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 30)) == (10 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel54 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 30)) == (11 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel55 := (if ((BitVec.truncate 6 (BitVec.ushiftRight cDst 30)) == (12 : BitVec 6)) then (1 : BitVec 1) else 0)
    let accsel56 := (if (accsel55 != 0) then (5 : BitVec 3) else (if (accsel54 != 0) then (4 : BitVec 3) else (if (accsel53 != 0) then (3 : BitVec 3) else (if (accsel52 != 0) then (2 : BitVec 3) else (if (accsel51 != 0) then (1 : BitVec 3) else (if (accsel50 != 0) then (0 : BitVec 3) else (6 : BitVec 3)))))))
  accsel56

end Metronome.Units.Acc

namespace Metronome.Units.Counter

set_option linter.unusedSimpArgs false

/-! ## The extracted transition is the specification -/

/-- The extracted counter value is the specification's. -/
theorem rtlV (state : State) (input : Input) :
    (rtlStep state input).v = (step state input).v := by
  simp only [rtlStep, step, vNext, loadLow, loadHigh, decrement]
  bv_decide

/-- The extracted `Z` output is `V == 0`. -/
theorem rtlZ_eq_spec (state : State) : rtlZ state = zOut state := by
  simp only [rtlZ, zOut]
  bv_decide

/-- The extracted counter transition equals the SPEC v1 §6.1 counter for every
state and input. -/
theorem rtlStep_eq_step (state : State) (input : Input) :
    rtlStep state input = step state input := by
  simp only [rtlStep, step, vNext, loadLow, loadHigh, decrement, State.mk.injEq]
  exact rtlV state input

/-! ## The elaborated port-code decode -/

/-- The elaborated `LO`/`HI`/`DEC` priority mux is the documented code map. -/
theorem rtlSel0_eq_spec (opLo opHi : Bool) :
    rtlSel0 opLo opHi = selOf opLo opHi := by
  simp only [rtlSel0, selOf]
  bv_decide

theorem rtlSel1_eq_spec (opLo opHi : Bool) :
    rtlSel1 opLo opHi = selOf opLo opHi := by
  simp only [rtlSel1, selOf]
  bv_decide

theorem rtlSel2_eq_spec (opLo opHi : Bool) :
    rtlSel2 opLo opHi = selOf opLo opHi := by
  simp only [rtlSel2, selOf]
  bv_decide

/-! ## Trace lifting -/

def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun state input => rtlStep state input) inputs initial n

theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt inputs initial n :=
  run_congr (fun state input => rtlStep_eq_step state input) inputs initial n

theorem rtl_trace_result (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStep (rtlStateAt inputs initial n) (inputs n) =
      step (stateAt inputs initial n) (inputs n) := by
  rw [rtlStateAt_eq, rtlStep_eq_step]

#print axioms rtlV
#print axioms rtlZ_eq_spec
#print axioms rtlStep_eq_step
#print axioms rtlSel0_eq_spec
#print axioms rtlStateAt_eq

end Metronome.Units.Counter

namespace Metronome.Units.Shifter

set_option linter.unusedSimpArgs false

/-! ## The extracted transition is the specification -/

theorem rtlDr (state : State) (input : Input) :
    (rtlStep state input).dr = (step state input).dr := by
  simp only [rtlStep, step, drNext, shifted, bitAt]
  bv_decide

theorem rtlCnt (state : State) (input : Input) :
    (rtlStep state input).cnt = (step state input).cnt := by
  simp only [rtlStep, step, cntNext, loadCount, shiftCount]
  bv_decide

theorem rtlLen (state : State) (input : Input) :
    (rtlStep state input).len = (step state input).len := by
  simp only [rtlStep, step, lenNext, slice]
  bv_decide

theorem rtlMsb (state : State) (input : Input) :
    (rtlStep state input).msb = (step state input).msb := by
  simp only [rtlStep, step, msbNext, bitAt]
  bv_decide

/-- The extracted `O` output is `MSB ? D[7] : D[0]`. -/
theorem rtlO_eq_spec (state : State) : rtlO state = out state := by
  simp only [rtlO, out, bitAt]
  bv_decide

/-- The extracted `DONE` output is `CNT == 0`. -/
theorem rtlDone_eq_spec (state : State) : rtlDone state = done state := by
  simp only [rtlDone, done]
  bv_decide

/-- The extracted shifter transition equals the SPEC v1 §6.1 shifter for every
state and input: `D`, `CNT`, `LEN` and `MSB`. -/
theorem rtlStep_eq_step (state : State) (input : Input) :
    rtlStep state input = step state input := by
  simp only [rtlStep, step, drNext, cntNext, lenNext, msbNext, shifted, loadCount,
    shiftCount, slice, bitAt, State.mk.injEq]
  exact ⟨rtlDr state input, rtlCnt state input, rtlLen state input,
    rtlMsb state input⟩

/-! ## Trace lifting -/

def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun state input => rtlStep state input) inputs initial n

theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt inputs initial n :=
  run_congr (fun state input => rtlStep_eq_step state input) inputs initial n

theorem rtl_trace_result (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStep (rtlStateAt inputs initial n) (inputs n) =
      step (stateAt inputs initial n) (inputs n) := by
  rw [rtlStateAt_eq, rtlStep_eq_step]

#print axioms rtlDr
#print axioms rtlCnt
#print axioms rtlLen
#print axioms rtlMsb
#print axioms rtlO_eq_spec
#print axioms rtlDone_eq_spec
#print axioms rtlStep_eq_step
#print axioms rtlStateAt_eq

end Metronome.Units.Shifter

namespace Metronome.Units.Lfsr

set_option linter.unusedSimpArgs false

/-! ## The extracted transition is the specification -/

/-- The extracted LFSR state is the SPEC v1 §6.1 `ST`/`B0..B3` equation for
every state and input. -/
theorem rtlS (state : State) (input : Input) :
    (rtlStep state input).s = (step state input).s := by
  simp only [rtlStep, step, sNext, stepBit, feedback, loadByte0, loadByte1,
    loadByte2, loadByte3, bitAt]
  bv_decide

theorem rtlStep_eq_step (state : State) (input : Input) :
    rtlStep state input = step state input := by
  simp only [rtlStep, step, sNext, stepBit, feedback, loadByte0, loadByte1,
    loadByte2, loadByte3, bitAt, State.mk.injEq]
  exact rtlS state input

/-- The elaborated `ST`/`B0..B3` priority mux is the documented code map. -/
theorem rtlSel0_eq_spec (opSt opB0 opB1 opB2 : Bool) :
    rtlSel0 opSt opB0 opB1 opB2 = selOf opSt opB0 opB1 opB2 := by
  simp only [rtlSel0, selOf]
  bv_decide

theorem rtlSel1_eq_spec (opSt opB0 opB1 opB2 : Bool) :
    rtlSel1 opSt opB0 opB1 opB2 = selOf opSt opB0 opB1 opB2 := by
  simp only [rtlSel1, selOf]
  bv_decide

/-! ## Trace lifting -/

def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun state input => rtlStep state input) inputs initial n

theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt inputs initial n :=
  run_congr (fun state input => rtlStep_eq_step state input) inputs initial n

theorem rtl_trace_result (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStep (rtlStateAt inputs initial n) (inputs n) =
      step (stateAt inputs initial n) (inputs n) := by
  rw [rtlStateAt_eq, rtlStep_eq_step]

#print axioms rtlS
#print axioms rtlStep_eq_step
#print axioms rtlSel0_eq_spec
#print axioms rtlStateAt_eq

end Metronome.Units.Lfsr

namespace Metronome.Units.Acc

set_option linter.unusedSimpArgs false

/-! ## The extracted transition is the specification -/

theorem rtlA (state : State) (input : Input)
    (h : OneHotOrZero input.hit) :
    (rtlStep state input).a = (step state input).a := by
  rcases state with ⟨a, z, c, n, r⟩
  rcases input with ⟨resetN, hit, sel, d, rWe, rD⟩
  simp only [OneHotOrZero] at h
  simp only [rtlStep, step, aNext, winnerWa, winnerRes, aluWa, aluRes, opSel, opData, slice, bitAt]
  cases resetN <;> cases z <;> cases c <;> cases n <;> bv_decide

theorem rtlZ (state : State) (input : Input)
    (h : OneHotOrZero input.hit) :
    (rtlStep state input).z = (step state input).z := by
  rcases state with ⟨a, z, c, n, r⟩
  rcases input with ⟨resetN, hit, sel, d, rWe, rD⟩
  simp only [OneHotOrZero] at h
  simp only [rtlStep, step, zNext, winnerZ, aluZ, opSel, opData, slice, bitAt]
  cases resetN <;> cases z <;> cases c <;> cases n <;> bv_decide

theorem rtlC (state : State) (input : Input)
    (h : OneHotOrZero input.hit) :
    (rtlStep state input).c = (step state input).c := by
  rcases state with ⟨a, z, c, n, r⟩
  rcases input with ⟨resetN, hit, sel, d, rWe, rD⟩
  simp only [OneHotOrZero] at h
  simp only [rtlStep, step, cNext, winnerWc, winnerCy, aluWc, aluCy, opSel, opData, slice, bitAt]
  cases resetN <;> cases z <;> cases c <;> cases n <;> bv_decide

theorem rtlN (state : State) (input : Input)
    (h : OneHotOrZero input.hit) :
    (rtlStep state input).n = (step state input).n := by
  rcases state with ⟨a, z, c, n, r⟩
  rcases input with ⟨resetN, hit, sel, d, rWe, rD⟩
  simp only [OneHotOrZero] at h
  simp only [rtlStep, step, nNext, winnerN, aluN, opSel, opData, slice, bitAt]
  cases resetN <;> cases z <;> cases c <;> cases n <;> bv_decide

theorem rtlR (state : State) (input : Input) :
    (rtlStep state input).r = (step state input).r := by
  rcases state with ⟨a, z, c, n, r⟩
  rcases input with ⟨resetN, hit, sel, d, rWe, rD⟩
  simp only [rtlStep, step, rNext, bitAt]
  cases resetN <;> bv_decide

/-- The extracted accumulator transition equals the SPEC v1 §6.1 accumulator for
every state and input: the one hit slot's op and data, with `CMP` leaving `A`
and the four scratch groups independent. -/
theorem rtlStep_eq_step (state : State) (input : Input)
    (h : OneHotOrZero input.hit) :
    rtlStep state input = step state input := by
  simp only [rtlStep, step, State.mk.injEq]
  exact ⟨rtlA state input h, rtlZ state input h, rtlC state input h,
    rtlN state input h, rtlR state input⟩

/-! ## The elaborated destination decode -/

/-- Slot `m`'s elaborated `case` implements the documented destination-code map. -/
theorem rtlSel0_eq_spec (cDst : BitVec 36) :
    rtlSel0 cDst = opCodeOf (slice cDst 0 6) := by
  simp only [rtlSel0, opCodeOf, slice]
  bv_decide

theorem rtlSel1_eq_spec (cDst : BitVec 36) :
    rtlSel1 cDst = opCodeOf (slice cDst 6 6) := by
  simp only [rtlSel1, opCodeOf, slice]
  bv_decide

theorem rtlSel2_eq_spec (cDst : BitVec 36) :
    rtlSel2 cDst = opCodeOf (slice cDst 12 6) := by
  simp only [rtlSel2, opCodeOf, slice]
  bv_decide

theorem rtlSel3_eq_spec (cDst : BitVec 36) :
    rtlSel3 cDst = opCodeOf (slice cDst 18 6) := by
  simp only [rtlSel3, opCodeOf, slice]
  bv_decide

theorem rtlSel4_eq_spec (cDst : BitVec 36) :
    rtlSel4 cDst = opCodeOf (slice cDst 24 6) := by
  simp only [rtlSel4, opCodeOf, slice]
  bv_decide

theorem rtlSel5_eq_spec (cDst : BitVec 36) :
    rtlSel5 cDst = opCodeOf (slice cDst 30 6) := by
  simp only [rtlSel5, opCodeOf, slice]
  bv_decide

/-! ## Trace lifting -/

def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun state input => rtlStep state input) inputs initial n

/-- Every sampled cycle must respect the write-group contract. -/
theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State)
    (h : ∀ n, OneHotOrZero (inputs n).hit) (n : Nat) :
    rtlStateAt inputs initial n = stateAt inputs initial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show rtlStateAt inputs initial (n + 1) =
          rtlStep (rtlStateAt inputs initial n) (inputs n) from rfl,
        show stateAt inputs initial (n + 1) =
          step (stateAt inputs initial n) (inputs n) from rfl,
        ih, rtlStep_eq_step _ _ (h n)]

theorem rtl_trace_result (inputs : Nat → Input) (initial : State)
    (h : ∀ n, OneHotOrZero (inputs n).hit) (n : Nat) :
    rtlStep (rtlStateAt inputs initial n) (inputs n) =
      step (stateAt inputs initial n) (inputs n) := by
  rw [rtlStateAt_eq inputs initial h n, rtlStep_eq_step _ _ (h n)]

#print axioms rtlA
#print axioms rtlZ
#print axioms rtlC
#print axioms rtlN
#print axioms rtlR
#print axioms rtlStep_eq_step
#print axioms rtlSel0_eq_spec
#print axioms rtlStateAt_eq
#print axioms Metronome.Units.Acc.slotsPacked_eq_winner
#print axioms Metronome.Units.Acc.unpack_pack

end Metronome.Units.Acc

#print axioms Metronome.Units.Counter.rtlStep_eq_step
#print axioms Metronome.Units.Shifter.rtlStep_eq_step
#print axioms Metronome.Units.Lfsr.rtlStep_eq_step
#print axioms Metronome.Units.Acc.rtlStep_eq_step
