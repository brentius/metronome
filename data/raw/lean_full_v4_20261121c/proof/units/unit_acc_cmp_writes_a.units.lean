import Metronome.Units

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: f3f045a2765684d7ac8b271aac4017bd41094936dfa1c5281bb8482d8621e8bf
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
  let rtl3 := (if (input.sel == (0 : BitVec 2)) then (1 : BitVec 1) else 0)
  let rtl4 := (if (rtl3 != 0) then input.d else (BitVec.truncate 8 (BitVec.ushiftRight state.v 0)))
  let rtl5 := (if ((BitVec.truncate 1 (BitVec.ushiftRight input.sel 1)) != 0) then ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl2 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else rtl4)
  let rtl6 := (if ((if input.we then (1 : BitVec 1) else 0) != 0) then rtl5 else (BitVec.truncate 8 (BitVec.ushiftRight state.v 0)))
  let rtl7 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl6 else (0 : BitVec 8))
  let rtl8 := (if (input.sel == (1 : BitVec 2)) then (1 : BitVec 1) else 0)
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
  let rtl35 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 0)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl36 := (if (rtl35 != 0) then (1 : BitVec 1) else (if (rtl34 != 0) then (1 : BitVec 1) else (if (rtl33 != 0) then (1 : BitVec 1) else (if (rtl32 != 0) then (1 : BitVec 1) else (if (rtl31 != 0) then (1 : BitVec 1) else (if (rtl30 != 0) then (1 : BitVec 1) else (if (rtl29 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))))))
  let rtl37 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))) &&& ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl13 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if (rtl18 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if (rtl24 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if (rtl28 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if (rtl36 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let rtl38 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))) + ((if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 8)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 9)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 10)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 11)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 12)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 13)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 14)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 15)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))))
  let rtl39 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl40 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl41 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl42 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl43 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl44 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl45 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl46 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl47 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl48 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl49 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl50 := (if (rtl49 != 0) then rtl48 else (if (rtl47 != 0) then rtl46 else (if (rtl45 != 0) then rtl44 else (if (rtl43 != 0) then rtl42 else (if (rtl41 != 0) then rtl40 else (if (rtl39 != 0) then ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl38 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl38 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl38 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl38 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl38 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl38 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl38 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl38 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 8))))))))
  let rtl51 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl52 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl53 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 8)))
  let rtl54 := (if (rtl49 != 0) then rtl48 else (if (rtl47 != 0) then rtl53 else (if (rtl45 != 0) then rtl52 else (if (rtl43 != 0) then rtl51 else (if (rtl41 != 0) then rtl40 else (if (rtl39 != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl38 0)) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 8))))))))
  let rtl55 := (if (rtl54 == (0 : BitVec 8)) then (1 : BitVec 1) else 0)
  let rtl56 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl57 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 8))) then (1 : BitVec 1) else 0)
  let rtl58 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl59 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 8))) then (1 : BitVec 1) else 0)
  let rtl60 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl61 := (if (rtl60 != 0) then rtl59 else (if (rtl58 != 0) then rtl57 else (if (rtl56 != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl38 8)) else (if state.c then (1 : BitVec 1) else 0))))
  let rtl62 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl63 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl64 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl65 := (if (rtl64 != 0) then (1 : BitVec 1) else (if (rtl63 != 0) then (1 : BitVec 1) else (if (rtl62 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))
  let rtl66 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (0 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl67 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl68 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl69 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl70 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl71 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl72 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 3)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl73 := (if (rtl72 != 0) then (1 : BitVec 1) else (if (rtl71 != 0) then (1 : BitVec 1) else (if (rtl70 != 0) then (1 : BitVec 1) else (if (rtl69 != 0) then (1 : BitVec 1) else (if (rtl68 != 0) then (1 : BitVec 1) else (if (rtl67 != 0) then (1 : BitVec 1) else (if (rtl66 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))))))
  let rtl74 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))) &&& ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl50 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl50 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl50 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl50 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl50 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl50 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl50 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl50 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl50 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if (rtl55 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if (rtl61 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if (rtl65 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if (rtl73 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let rtl75 := (rtl37 ||| rtl74)
  let rtl76 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))) + ((if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 16)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 17)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 18)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 19)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 20)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 21)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 22)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 23)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))))
  let rtl77 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl78 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl79 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl80 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl81 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl82 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl83 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl84 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl85 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl86 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl87 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl88 := (if (rtl87 != 0) then rtl86 else (if (rtl85 != 0) then rtl84 else (if (rtl83 != 0) then rtl82 else (if (rtl81 != 0) then rtl80 else (if (rtl79 != 0) then rtl78 else (if (rtl77 != 0) then ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl76 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl76 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl76 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl76 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl76 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl76 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl76 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl76 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 16))))))))
  let rtl89 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl90 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl91 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 16)))
  let rtl92 := (if (rtl87 != 0) then rtl86 else (if (rtl85 != 0) then rtl91 else (if (rtl83 != 0) then rtl90 else (if (rtl81 != 0) then rtl89 else (if (rtl79 != 0) then rtl78 else (if (rtl77 != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl76 0)) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 16))))))))
  let rtl93 := (if (rtl92 == (0 : BitVec 8)) then (1 : BitVec 1) else 0)
  let rtl94 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl95 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 16))) then (1 : BitVec 1) else 0)
  let rtl96 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl97 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 16))) then (1 : BitVec 1) else 0)
  let rtl98 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl99 := (if (rtl98 != 0) then rtl97 else (if (rtl96 != 0) then rtl95 else (if (rtl94 != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl76 8)) else (if state.c then (1 : BitVec 1) else 0))))
  let rtl100 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl101 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl102 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl103 := (if (rtl102 != 0) then (1 : BitVec 1) else (if (rtl101 != 0) then (1 : BitVec 1) else (if (rtl100 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))
  let rtl104 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (0 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl105 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl106 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl107 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl108 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl109 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl110 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 6)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl111 := (if (rtl110 != 0) then (1 : BitVec 1) else (if (rtl109 != 0) then (1 : BitVec 1) else (if (rtl108 != 0) then (1 : BitVec 1) else (if (rtl107 != 0) then (1 : BitVec 1) else (if (rtl106 != 0) then (1 : BitVec 1) else (if (rtl105 != 0) then (1 : BitVec 1) else (if (rtl104 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))))))
  let rtl112 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))) &&& ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl88 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl88 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl88 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl88 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl88 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl88 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl88 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl88 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl88 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if (rtl93 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if (rtl99 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if (rtl103 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if (rtl111 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let rtl113 := (rtl75 ||| rtl112)
  let rtl114 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))) + ((if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 24)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 25)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 26)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 27)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 28)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 29)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 30)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 31)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))))
  let rtl115 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl116 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl117 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl118 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl119 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl120 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl121 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl122 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl123 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl124 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl125 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl126 := (if (rtl125 != 0) then rtl124 else (if (rtl123 != 0) then rtl122 else (if (rtl121 != 0) then rtl120 else (if (rtl119 != 0) then rtl118 else (if (rtl117 != 0) then rtl116 else (if (rtl115 != 0) then ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl114 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl114 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl114 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl114 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl114 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl114 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl114 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl114 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 24))))))))
  let rtl127 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl128 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl129 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 24)))
  let rtl130 := (if (rtl125 != 0) then rtl124 else (if (rtl123 != 0) then rtl129 else (if (rtl121 != 0) then rtl128 else (if (rtl119 != 0) then rtl127 else (if (rtl117 != 0) then rtl116 else (if (rtl115 != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl114 0)) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 24))))))))
  let rtl131 := (if (rtl130 == (0 : BitVec 8)) then (1 : BitVec 1) else 0)
  let rtl132 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl133 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 24))) then (1 : BitVec 1) else 0)
  let rtl134 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl135 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 24))) then (1 : BitVec 1) else 0)
  let rtl136 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl137 := (if (rtl136 != 0) then rtl135 else (if (rtl134 != 0) then rtl133 else (if (rtl132 != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl114 8)) else (if state.c then (1 : BitVec 1) else 0))))
  let rtl138 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl139 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl140 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl141 := (if (rtl140 != 0) then (1 : BitVec 1) else (if (rtl139 != 0) then (1 : BitVec 1) else (if (rtl138 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))
  let rtl142 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (0 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl143 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl144 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl145 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl146 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl147 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl148 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 9)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl149 := (if (rtl148 != 0) then (1 : BitVec 1) else (if (rtl147 != 0) then (1 : BitVec 1) else (if (rtl146 != 0) then (1 : BitVec 1) else (if (rtl145 != 0) then (1 : BitVec 1) else (if (rtl144 != 0) then (1 : BitVec 1) else (if (rtl143 != 0) then (1 : BitVec 1) else (if (rtl142 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))))))
  let rtl150 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))) &&& ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl126 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl126 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl126 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl126 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl126 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl126 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl126 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl126 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl126 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if (rtl131 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if (rtl137 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if (rtl141 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if (rtl149 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let rtl151 := (rtl113 ||| rtl150)
  let rtl152 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))) + ((if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 32)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 33)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 34)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 35)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 36)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 37)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 38)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 39)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))))
  let rtl153 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl154 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl155 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl156 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl157 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl158 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl159 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl160 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl161 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl162 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl163 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl164 := (if (rtl163 != 0) then rtl162 else (if (rtl161 != 0) then rtl160 else (if (rtl159 != 0) then rtl158 else (if (rtl157 != 0) then rtl156 else (if (rtl155 != 0) then rtl154 else (if (rtl153 != 0) then ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl152 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl152 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl152 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl152 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl152 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl152 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl152 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl152 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 32))))))))
  let rtl165 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl166 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl167 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 32)))
  let rtl168 := (if (rtl163 != 0) then rtl162 else (if (rtl161 != 0) then rtl167 else (if (rtl159 != 0) then rtl166 else (if (rtl157 != 0) then rtl165 else (if (rtl155 != 0) then rtl154 else (if (rtl153 != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl152 0)) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 32))))))))
  let rtl169 := (if (rtl168 == (0 : BitVec 8)) then (1 : BitVec 1) else 0)
  let rtl170 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl171 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 32))) then (1 : BitVec 1) else 0)
  let rtl172 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl173 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 32))) then (1 : BitVec 1) else 0)
  let rtl174 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl175 := (if (rtl174 != 0) then rtl173 else (if (rtl172 != 0) then rtl171 else (if (rtl170 != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl152 8)) else (if state.c then (1 : BitVec 1) else 0))))
  let rtl176 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl177 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl178 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl179 := (if (rtl178 != 0) then (1 : BitVec 1) else (if (rtl177 != 0) then (1 : BitVec 1) else (if (rtl176 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))
  let rtl180 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (0 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl181 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl182 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl183 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl184 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl185 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl186 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 12)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl187 := (if (rtl186 != 0) then (1 : BitVec 1) else (if (rtl185 != 0) then (1 : BitVec 1) else (if (rtl184 != 0) then (1 : BitVec 1) else (if (rtl183 != 0) then (1 : BitVec 1) else (if (rtl182 != 0) then (1 : BitVec 1) else (if (rtl181 != 0) then (1 : BitVec 1) else (if (rtl180 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))))))
  let rtl188 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))) &&& ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl164 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl164 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl164 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl164 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl164 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl164 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl164 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl164 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl164 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if (rtl169 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if (rtl175 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if (rtl179 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if (rtl187 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let rtl189 := (rtl151 ||| rtl188)
  let rtl190 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight state.a 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))) + ((if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 40)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 0) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 41)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 1) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 42)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 2) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 43)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 3) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 44)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 4) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 45)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 5) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 46)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 6) else (0 : BitVec 9)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.d 47)) != 0) then (BitVec.shiftLeft (1 : BitVec 9) 7) else (0 : BitVec 9)) ||| (if false then (BitVec.shiftLeft (1 : BitVec 9) 8) else (0 : BitVec 9))))
  let rtl191 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl192 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl193 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl194 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl195 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl196 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl197 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl198 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl199 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl200 := (state.a - (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl201 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl202 := (if (rtl201 != 0) then rtl200 else (if (rtl199 != 0) then rtl198 else (if (rtl197 != 0) then rtl196 else (if (rtl195 != 0) then rtl194 else (if (rtl193 != 0) then rtl192 else (if (rtl191 != 0) then ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl190 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl190 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl190 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl190 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl190 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl190 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl190 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl190 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 40))))))))
  let rtl203 := (state.a &&& (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl204 := (state.a ||| (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl205 := (state.a ^^^ (BitVec.truncate 8 (BitVec.ushiftRight input.d 40)))
  let rtl206 := (if (rtl201 != 0) then rtl200 else (if (rtl199 != 0) then rtl205 else (if (rtl197 != 0) then rtl204 else (if (rtl195 != 0) then rtl203 else (if (rtl193 != 0) then rtl192 else (if (rtl191 != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl190 0)) else (BitVec.truncate 8 (BitVec.ushiftRight input.d 40))))))))
  let rtl207 := (if (rtl206 == (0 : BitVec 8)) then (1 : BitVec 1) else 0)
  let rtl208 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl209 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 40))) then (1 : BitVec 1) else 0)
  let rtl210 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl211 := (if (state.a >= (BitVec.truncate 8 (BitVec.ushiftRight input.d 40))) then (1 : BitVec 1) else 0)
  let rtl212 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl213 := (if (rtl212 != 0) then rtl211 else (if (rtl210 != 0) then rtl209 else (if (rtl208 != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl190 8)) else (if state.c then (1 : BitVec 1) else 0))))
  let rtl214 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl215 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl216 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl217 := (if (rtl216 != 0) then (1 : BitVec 1) else (if (rtl215 != 0) then (1 : BitVec 1) else (if (rtl214 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))
  let rtl218 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (0 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl219 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (1 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl220 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (2 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl221 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (3 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl222 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (4 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl223 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (5 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl224 := (if ((BitVec.truncate 3 (BitVec.ushiftRight input.sel 15)) == (6 : BitVec 3)) then (1 : BitVec 1) else 0)
  let rtl225 := (if (rtl224 != 0) then (1 : BitVec 1) else (if (rtl223 != 0) then (1 : BitVec 1) else (if (rtl222 != 0) then (1 : BitVec 1) else (if (rtl221 != 0) then (1 : BitVec 1) else (if (rtl220 != 0) then (1 : BitVec 1) else (if (rtl219 != 0) then (1 : BitVec 1) else (if (rtl218 != 0) then (1 : BitVec 1) else (0 : BitVec 1))))))))
  let rtl226 := (((if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight input.hit 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))) &&& ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl202 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 0) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl202 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 1) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl202 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 2) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl202 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 3) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl202 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 4) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl202 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 5) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl202 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 6) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl202 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 7) else (0 : BitVec 13)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl202 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 13) 8) else (0 : BitVec 13)) ||| (if (rtl207 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 9) else (0 : BitVec 13)) ||| (if (rtl213 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 10) else (0 : BitVec 13)) ||| (if (rtl217 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 11) else (0 : BitVec 13)) ||| (if (rtl225 != 0) then (BitVec.shiftLeft (1 : BitVec 13) 12) else (0 : BitVec 13))))
  let rtl227 := (rtl189 ||| rtl226)
  let rtl228 := (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl227 12)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight rtl227 0)) else state.a)
  let rtl229 := (if (rtl0 != 0) then rtl228 else state.a)
  let rtl230 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl229 else (0 : BitVec 8))
  let rtl231 := (if (rtl0 != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl227 9)) else (if state.z then (1 : BitVec 1) else 0))
  let rtl232 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl231 else (0 : BitVec 1))
  let rtl233 := (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl227 11)) != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl227 10)) else (if state.c then (1 : BitVec 1) else 0))
  let rtl234 := (if (rtl0 != 0) then rtl233 else (if state.c then (1 : BitVec 1) else 0))
  let rtl235 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl234 else (0 : BitVec 1))
  let rtl236 := (if (rtl0 != 0) then (BitVec.truncate 1 (BitVec.ushiftRight rtl227 8)) else (if state.n then (1 : BitVec 1) else 0))
  let rtl237 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl236 else (0 : BitVec 1))
  let rtl238 := (if ((BitVec.truncate 1 (BitVec.ushiftRight input.rWe 0)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.rD 0)) else (BitVec.truncate 8 (BitVec.ushiftRight state.r 0)))
  let rtl239 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl238 else (0 : BitVec 8))
  let rtl240 := (if ((BitVec.truncate 1 (BitVec.ushiftRight input.rWe 1)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.rD 8)) else (BitVec.truncate 8 (BitVec.ushiftRight state.r 8)))
  let rtl241 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl240 else (0 : BitVec 8))
  let rtl242 := (if ((BitVec.truncate 1 (BitVec.ushiftRight input.rWe 2)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.rD 16)) else (BitVec.truncate 8 (BitVec.ushiftRight state.r 16)))
  let rtl243 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl242 else (0 : BitVec 8))
  let rtl244 := (if ((BitVec.truncate 1 (BitVec.ushiftRight input.rWe 3)) != 0) then (BitVec.truncate 8 (BitVec.ushiftRight input.rD 24)) else (BitVec.truncate 8 (BitVec.ushiftRight state.r 24)))
  let rtl245 := (if ((if input.resetN then (1 : BitVec 1) else 0) != 0) then rtl244 else (0 : BitVec 8))
  ⟨rtl230, (rtl232 != 0), (rtl235 != 0), (rtl237 != 0), ((if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 0) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 1) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 2) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 3) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 4) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 5) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 6) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl239 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 7) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl241 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 8) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl241 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 9) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl241 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 10) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl241 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 11) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl241 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 12) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl241 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 13) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl241 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 14) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl241 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 15) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl243 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 16) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl243 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 17) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl243 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 18) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl243 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 19) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl243 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 20) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl243 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 21) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl243 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 22) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl243 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 23) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl245 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 24) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl245 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 25) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl245 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 26) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl245 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 27) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl245 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 28) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl245 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 29) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl245 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 30) else (0 : BitVec 32)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight rtl245 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 32) 31) else (0 : BitVec 32)))⟩

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
