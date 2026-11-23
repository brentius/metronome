import Metronome.Transition
import Std.Tactic.BVDecide

/-!
# Engine data units: counter, shifter, LFSR/CRC and accumulator

This module is the independent specification of the four data units of
SPEC_V2 §6.1, written from the specification text and its references, not from
the RTL.  SPEC_V2 §6.1 delegates the per-unit equations to SPEC v1 §6.1 for the
accumulator, shifter, counter and LFSR, and fixes the write groups in §6.  The
destination-port codes (`LO`/`HI`/`DEC`, `LD`/`SH`/`CFG`, `ST`/`B0..B3`, the
seven accumulator ops) come from `wiki/ISA_TABLES_V2.md`; the encodings of
those codes as Verilog constants are read from `src/md2_defs.vh` and
`src/md2_map.vh` by the adapter and checked against the elaborated cells.

The RTL side is `UnitsEquivalence.lean.in`, filled by `units_check.py`: it
extracts each register's next-state cone from the elaborated netlist as a Lean
function, proves it equal to the specification below, and lifts the one-step
equality to traces by induction.

## Cycle boundary

`stateAt inputs initial n` is the register state during chip cycle `n`, after
`n` sampled edges: the same convention as `Metronome.Transition` and the other
cuts in this directory.  A move in cycle `n` writes at the edge at the end of
cycle `n`, so it is visible in the state of cycle `n + 1`.

## Reset

`rst_n` is a synchronous input of all four units (each `always @(posedge clk)`
tests it first, and the chip top drives it with the synchronised `rst_q`).  The
inputs here therefore carry `resetN : Bool`, and a cycle with `resetN = false`
leaves the documented reset state and ignores writes.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Metronome.Units

/-- One net bit as a `Bool`, the shape of a scalar RTL operand. -/
def bitAt {w : Nat} (x : BitVec w) (i : Nat) : Bool :=
  ((BitVec.truncate 1 (BitVec.ushiftRight x i)) != 0)

/-- Bits `off … off+w-1` of `x`, the shape the RTL adapter emits for a bus slice. -/
def slice {n : Nat} (x : BitVec n) (off w : Nat) : BitVec w :=
  BitVec.truncate w (BitVec.ushiftRight x off)

/-! ## Counter (SPEC_V2 §6.1, "Counters `CNT0..CNT2`: as SPEC v1 6.1")

SPEC v1 §6.1: state `V` (16 bits).  `LO: V[7:0]' = v`, `HI: V[15:8]' = v`,
`DEC: V' = V ? V-1 : 0` (saturating at zero, data ignored), and
`Z = (V == 0)`.  ISA_TABLES_V2 fixes the destination codes `CNTk.LO`,
`CNTk.HI`, `CNTk.DEC`; the RTL's two-bit port code is 0 = `LO`, 1 = `HI`,
2 = `DEC` (the adapter checks the code map).
-/
namespace Counter

/-- `sel` codes of the counter port, from `src/md2_counter.v` and project.v's
`op_lo ? 0 : op_hi ? 1 : 2`.  `LO` and `HI` load one byte; `DEC` saturates. -/
abbrev SEL_LO : BitVec 2 := 0
abbrev SEL_HI : BitVec 2 := 1
abbrev SEL_DEC : BitVec 2 := 2

/-- Program state: the 16-bit counter `V`. -/
structure State where
  /-- `V`, the counter value. -/
  v : BitVec 16
  deriving DecidableEq, Repr

/-- Sampled unit inputs: the cycle's move (write enable, port select, 8-bit
data) and the synchronous reset. -/
structure Input where
  resetN : Bool
  we : Bool
  sel : BitVec 2
  d : BitVec 8
  deriving DecidableEq, Repr

/-- The state left by a sampled reset edge. -/
def resetState : State := ⟨0⟩

/-- `LO: V[7:0]' = v`, the high byte unchanged. -/
def loadLow (s : State) (i : Input) : BitVec 16 :=
  (s.v &&& (0xFF00 : BitVec 16)) ||| i.d.setWidth 16

/-- `HI: V[15:8]' = v`, the low byte unchanged. -/
def loadHigh (s : State) (i : Input) : BitVec 16 :=
  (s.v &&& (0x00FF : BitVec 16)) ||| (i.d.setWidth 16 <<< 8)

/-- `DEC: V' = V ? V-1 : 0`: saturating at zero. -/
def decrement (s : State) : BitVec 16 :=
  if s.v = 0 then 0 else s.v - 1

/-- The counter's next value, one equation per SPEC v1 §6.1 write.  The port
code is total: 2 and 3 both select `DEC`, matching the RTL's `sel[1]` test (code
3 is not a documented destination and the group decode never emits it). -/
def vNext (s : State) (i : Input) : BitVec 16 :=
  if !i.resetN then 0
  else if !i.we then s.v
  else if i.sel = SEL_LO then loadLow s i
  else if i.sel = SEL_HI then loadHigh s i
  else decrement s

/-- The one-step transition. -/
def step (s : State) (i : Input) : State := ⟨vNext s i⟩

/-- The counter port-code map: `LO` = 0, `HI` = 1, `DEC` = 2.  project.v forms
it as `op_lo ? 0 : op_hi ? 1 : 2`; `units_check.py` proves the elaborated
priority mux implements this map. -/
def selOf (lo hi : Bool) : BitVec 2 :=
  if lo then 0 else if hi then 1 else 2

/-- `Z = (V == 0)`. -/
def zOut (s : State) : Bool := s.v == 0

/-- The counter trace: state during cycle `n`. -/
def stateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => step s i) inputs initial n

theorem stateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    stateAt inputs initial (n + 1) = step (stateAt inputs initial n) (inputs n) := rfl

/-- `DEC` at zero stays at zero (saturation). -/
theorem dec_zero : decrement ⟨0⟩ = 0 := rfl

/-- A decrement from a non-zero value subtracts one. -/
theorem dec_one : decrement ⟨1⟩ = 0 := rfl

end Counter

/-! ## Shifter (SPEC_V2 §6.1, "Shifters `SH0, SH1`: as SPEC v1 6.1")

SPEC v1 §6.1: state `D` (8), `CNT` (4), `LEN` (4, 0 means 8), `MSB`.
`LD: D' = v, CNT' = LEN ? LEN : 8`.
`SH: D' = MSB ? {D[6:0], v[0]} : {v[0], D[7:1]}, CNT' = CNT ? CNT-1 : 0`.
`CFG: LEN' = v[3:0], MSB' = v[4]`.  Outputs `O = MSB ? D[7] : D[0]` and
`DONE = (CNT == 0)`.  `SHk.{LD,SH}` and `SHk.CFG` are two write groups
(SPEC_V2 §6), so a cycle may carry both a data move and the configuration move;
SPEC_V2 §6 says all moves read cycle-`t` state, so `LD` uses the `LEN` of the
cycle and `CFG` takes effect at its end.
-/
namespace Shifter

/-- Program state: shift register `D`, count `CNT`, and the `LEN`/`MSB`
configuration set by `SHk.CFG`. -/
structure State where
  /-- `D`, the shift register. -/
  dr : BitVec 8
  /-- `CNT`, remaining shifts. -/
  cnt : BitVec 4
  /-- `LEN`, 0 means 8. -/
  len : BitVec 4
  /-- `MSB`, shift direction (MSB first when set). -/
  msb : Bool
  deriving DecidableEq, Repr

/-- Sampled unit inputs: the data move (`we`, `sel` 0 = `LD` / 1 = `SH`, `d`)
and the separate `SHk.CFG` move, plus the synchronous reset. -/
structure Input where
  resetN : Bool
  we : Bool
  sel : Bool
  d : BitVec 8
  cfgWe : Bool
  cfgD : BitVec 5
  deriving DecidableEq, Repr

/-- The state left by a sampled reset edge. -/
def resetState : State := ⟨0, 0, 0, false⟩

/-- `O = MSB ? D[7] : D[0]`. -/
def out (s : State) : Bool :=
  if s.msb then (s.dr &&& (0x80 : BitVec 8)) != 0
  else (s.dr &&& (0x01 : BitVec 8)) != 0

/-- `DONE = (CNT == 0)`. -/
def done (s : State) : Bool := s.cnt == 0

/-- `CNT' = LEN ? LEN : 8` on `LD`. -/
def loadCount (s : State) : BitVec 4 :=
  if s.len = 0 then 8 else s.len

/-- `CNT' = CNT ? CNT-1 : 0` on `SH`. -/
def shiftCount (s : State) : BitVec 4 :=
  if s.cnt = 0 then 0 else s.cnt - 1

/-- `SH`'s next data: MSB first shifts `D` left and shifts `v[0]` in at bit 0;
LSB first shifts right and shifts `v[0]` in at bit 7. -/
def shifted (s : State) (i : Input) : BitVec 8 :=
  if s.msb then (s.dr <<< 1) ||| (if bitAt i.d 0 then 1 else 0)
  else (s.dr >>> 1) ||| (if bitAt i.d 0 then (0x80 : BitVec 8) else 0)

/-- `D'`: reset, then `LD` (`sel = 0`), then `SH` (`sel = 1`), else hold. -/
def drNext (s : State) (i : Input) : BitVec 8 :=
  if !i.resetN then 0
  else if i.we && !i.sel then i.d
  else if i.we then shifted s i
  else s.dr

/-- `CNT'`: reset, then the `LD`/`SH` counts, else hold. -/
def cntNext (s : State) (i : Input) : BitVec 4 :=
  if !i.resetN then 0
  else if i.we && !i.sel then loadCount s
  else if i.we then shiftCount s
  else s.cnt

/-- `LEN'`: reset clears it; `SHk.CFG` takes `v[3:0]`. -/
def lenNext (s : State) (i : Input) : BitVec 4 :=
  if !i.resetN then 0
  else if i.cfgWe then slice i.cfgD 0 4
  else s.len

/-- `MSB'`: reset clears it; `SHk.CFG` takes `v[4]`. -/
def msbNext (s : State) (i : Input) : Bool :=
  if !i.resetN then false
  else if i.cfgWe then bitAt i.cfgD 4
  else s.msb

/-- The one-step transition: the data move and the configuration move both take
effect, as two write groups of one cycle. -/
def step (s : State) (i : Input) : State :=
  ⟨drNext s i, cntNext s i, lenNext s i, msbNext s i⟩

/-- The shifter trace: state during cycle `n`. -/
def stateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => step s i) inputs initial n

theorem stateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    stateAt inputs initial (n + 1) = step (stateAt inputs initial n) (inputs n) := rfl

/-- `LEN = 0` means eight on `LD`. -/
theorem loadCount_zero : loadCount ⟨0, 0, 0, false⟩ = 8 := rfl

/-- `SH` at `CNT = 0` saturates at zero. -/
theorem shiftCount_zero : shiftCount ⟨0, 0, 0, false⟩ = 0 := rfl

end Shifter

/-! ## LFSR / CRC (SPEC_V2 §6.1, "LFSR/CRC `LF0, LF1`: as SPEC v1 6.1")

SPEC v1 §6.1: state `S` (32) and `POLY` (32, configuration).  `ST`:
`fb = S[0] ^ v[0]; S' = (S >> 1) ^ (fb ? POLY : 0)`.  `Bk: S[8k+7:8k]' = v`.
`OUT = S[0]`.  The form is the reflected (LSB-first) Galois LFSR; `POLY` is a
latch configuration input and not part of this cut's state.  ISA_TABLES_V2
fixes the codes `ST`, `B0..B3` and the guard/source `LFk.OUT`/`LFk.O`.
-/
namespace Lfsr

/-- Program state: the 32-bit register `S`. -/
structure State where
  /-- `S`, the shift state. -/
  s : BitVec 32
  deriving DecidableEq, Repr

/-- Sampled unit inputs: the move (`we`, `sel` 0 = `ST` / 1..4 = `B0..B3`, `d`)
and the `POLY` configuration. -/
structure Input where
  resetN : Bool
  we : Bool
  sel : BitVec 3
  d : BitVec 8
  poly : BitVec 32
  deriving DecidableEq, Repr

/-- The state left by a sampled reset edge. -/
def resetState : State := ⟨0⟩

/-- `fb = S[0] ^ v[0]`. -/
def feedback (s : State) (i : Input) : Bool :=
  bitAt s.s 0 != bitAt i.d 0

/-- `ST`: `S' = (S >> 1) ^ (fb ? POLY : 0)`. -/
def stepBit (s : State) (i : Input) : BitVec 32 :=
  (s.s >>> 1) ^^^ (if feedback s i then i.poly else 0)

/-- `B0`: `S[7:0]' = v`. -/
def loadByte0 (s : State) (i : Input) : BitVec 32 :=
  (s.s &&& (0xFFFFFF00 : BitVec 32)) ||| i.d.setWidth 32

/-- `B1`: `S[15:8]' = v`. -/
def loadByte1 (s : State) (i : Input) : BitVec 32 :=
  (s.s &&& (0xFFFF00FF : BitVec 32)) ||| (i.d.setWidth 32 <<< 8)

/-- `B2`: `S[23:16]' = v`. -/
def loadByte2 (s : State) (i : Input) : BitVec 32 :=
  (s.s &&& (0xFF00FFFF : BitVec 32)) ||| (i.d.setWidth 32 <<< 16)

/-- `B3`: `S[31:24]' = v`. -/
def loadByte3 (s : State) (i : Input) : BitVec 32 :=
  (s.s &&& (0x00FFFFFF : BitVec 32)) ||| (i.d.setWidth 32 <<< 24)

/-- `S'`: reset, then the five documented writes; codes 5..7 do not select a
documented write and hold (the RTL's `default: ;`). -/
def sNext (s : State) (i : Input) : BitVec 32 :=
  if !i.resetN then 0
  else if !i.we then s.s
  else if i.sel = 0 then stepBit s i
  else if i.sel = 1 then loadByte0 s i
  else if i.sel = 2 then loadByte1 s i
  else if i.sel = 3 then loadByte2 s i
  else if i.sel = 4 then loadByte3 s i
  else s.s

/-- The one-step transition. -/
def step (s : State) (i : Input) : State := ⟨sNext s i⟩

/-- The LFSR port-code map: `ST` = 0, `B0..B3` = 1..4.  project.v forms it as
`op_st ? 0 : op_b0 ? 1 : op_b1 ? 2 : op_b2 ? 3 : 4`; `units_check.py` proves the
elaborated priority mux implements this map. -/
def selOf (st b0 b1 b2 : Bool) : BitVec 3 :=
  if st then 0 else if b0 then 1 else if b1 then 2 else if b2 then 3 else 4

/-- `OUT = S[0]`, read by source `LFk.O` and guard `LFk.OUT`. -/
def out (s : State) : Bool := bitAt s.s 0

/-- The LFSR trace: state during cycle `n`. -/
def stateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => step s i) inputs initial n

theorem stateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    stateAt inputs initial (n + 1) = step (stateAt inputs initial n) (inputs n) := rfl

/-- With `fb = 0` a step is a bare right shift. -/
theorem stepBit_noFeedback (s : State) (i : Input) (h : feedback s i = false) :
    stepBit s i = s.s >>> 1 := by
  simp [stepBit, h]

end Lfsr

/-! ## Accumulator (SPEC_V2 §6.1, "Accumulator `A` (8), `Z, C, N`, scratch
`R0..R3`: as SPEC v1 6.1")

SPEC v1 §6.1: `LD: A'=v`.  `ADD: r=A+v, A'=r[7:0], C'=r[8]`.
`SUB: r=A-v, A'=r[7:0], C'=(A>=v)`.  `AND/OR/XOR: A'=A op v`.
`CMP: r=A-v, C'=(A>=v)`, `A` unchanged.  Every op sets `Z'=(result==0)` and
`N'=result[7]` (result = `r` or the new `A`).  Scratch `Rk' = v`.
ISA_TABLES_V2 fixes the seven destination codes and the op order `LD, ADD, SUB,
AND, OR, XOR, CMP`.

The accumulator is one write group: in a cycle at most one move writes it, and
only the lowest `(core, move index)` does (SPEC_V2 §6).  The RTL therefore
receives a `hit` vector with one bit per move slot and per-slot `sel`/`d`, and
it computes one ALU result per slot and selects the one whose `hit` bit is set.
The specification's `winnerResult` states the SPEC reading directly (the one
hit slot's op and data); `slotsPacked_eq_winner` proves the per-slot restructure
equal to it under the explicit one-hot-or-zero premise.

The elaborated instance has `NM = 6` move slots and `NR = 4` scratch registers
(project.v instantiates `md2_acc #(.NR(4))`, and `NM` defaults to 6); the
adapter checks those parameters before emitting anything.
-/

namespace Acc

/-- Move slots of the elaborated `md2_acc` instance. -/
abbrev NM : Nat := 6
/-- Scratch registers of the elaborated `md2_acc` instance. -/
abbrev NR : Nat := 4

/-- Program state: `A`, the flags `Z, C, N`, and the four scratch bytes
`R0..R3` packed little-endian in `r`. -/
structure State where
  /-- `A`, the accumulator. -/
  a : BitVec 8
  /-- `Z`, result zero. -/
  z : Bool
  /-- `C`, carry / no borrow. -/
  c : Bool
  /-- `N`, result bit 7. -/
  n : Bool
  /-- `R0..R3`, one byte each, little-endian. -/
  r : BitVec 32
  deriving DecidableEq, Repr

/-- Sampled unit inputs.  `hit` is one-hot or zero; `sel` is 3 bits per slot
(the op code), `d` 8 bits per slot (that move's data); `rWe`/`rD` are the four
`Rk` write groups. -/
structure Input where
  resetN : Bool
  hit : BitVec 6
  sel : BitVec 18
  d : BitVec 48
  rWe : BitVec 4
  rD : BitVec 32
  deriving DecidableEq, Repr

/-- The state left by a sampled reset edge. -/
def resetState : State := ⟨0, false, false, false, 0⟩

/-- The ALU result of one slot: `{wa, wc, cy, z, n, res}`.  `wa`/`wc` are the
write enables of `A`/`C`, so `CMP` (`wa = false`) leaves `A` alone and `LD`,
`AND`, `OR`, `XOR` leave `C` alone. -/
structure Alu where
  /-- The op writes `A`. -/
  wa : Bool
  /-- The op writes `C`. -/
  wc : Bool
  /-- The `C` value when the op writes it. -/
  cy : Bool
  /-- `Z = (result == 0)`. -/
  z : Bool
  /-- `N = result[7]`. -/
  n : Bool
  /-- `result`: `r`, or the new `A`. -/
  res : BitVec 8
  deriving DecidableEq, Repr

/-! The ALU is written as one function per result field so that the generated
proofs can unfold it to plain bit-vector terms: projecting a field out of an
`if` that returns a whole structure does not reduce.  `alu` is the record of
the six fields. -/

/-- `A` is written by `LD..XOR` (op codes 0..5); `CMP` (6) and the unused
code 7 leave it unchanged. -/
def aluWa (sel : BitVec 3) : Bool := sel != 6 && sel != 7

/-- `C` is written by `ADD`, `SUB` and `CMP`. -/
def aluWc (sel : BitVec 3) : Bool := sel = 1 || sel = 2 || sel = 6

/-- The `C` result: `ADD`'s carry out, `SUB`/`CMP`'s no-borrow, otherwise the
held flag. -/
def aluCy (a : BitVec 8) (c : Bool) (sel : BitVec 3) (v : BitVec 8) : Bool :=
  if sel = 1 then bitAt (a.setWidth 9 + v.setWidth 9) 8
  else if sel = 2 then v.ule a
  else if sel = 6 then v.ule a
  else c

/-- `Z = (result == 0)` of the op. -/
def aluZ (a : BitVec 8) (sel : BitVec 3) (v : BitVec 8) : Bool :=
  if sel = 0 then v == 0
  else if sel = 1 then (a.setWidth 9 + v.setWidth 9).truncate 8 == 0
  else if sel = 2 then (a - v) == 0
  else if sel = 3 then (a &&& v) == 0
  else if sel = 4 then (a ||| v) == 0
  else if sel = 5 then (a ^^^ v) == 0
  else if sel = 6 then (a - v) == 0
  else v == 0

/-- `N = result[7]` of the op. -/
def aluN (a : BitVec 8) (sel : BitVec 3) (v : BitVec 8) : Bool :=
  if sel = 0 then bitAt v 7
  else if sel = 1 then bitAt ((a.setWidth 9 + v.setWidth 9).truncate 8) 7
  else if sel = 2 then bitAt (a - v) 7
  else if sel = 3 then bitAt (a &&& v) 7
  else if sel = 4 then bitAt (a ||| v) 7
  else if sel = 5 then bitAt (a ^^^ v) 7
  else if sel = 6 then bitAt (a - v) 7
  else bitAt v 7

/-- The op result: `LD` presents `v`, `ADD` the low byte of the 9-bit sum,
`SUB`/`CMP` the difference, the bitwise ops their value, otherwise `v`. -/
def aluRes (a : BitVec 8) (sel : BitVec 3) (v : BitVec 8) : BitVec 8 :=
  if sel = 0 then v
  else if sel = 1 then (a.setWidth 9 + v.setWidth 9).truncate 8
  else if sel = 2 then a - v
  else if sel = 3 then a &&& v
  else if sel = 4 then a ||| v
  else if sel = 5 then a ^^^ v
  else if sel = 6 then a - v
  else v

/-- One slot's ALU, SPEC v1 §6.1 equations.  Op codes 0..6 are `LD`, `ADD`,
`SUB`, `AND`, `OR`, `XOR`, `CMP`; code 7 is the RTL `default:` and is
unreachable (`opCodeOf`). -/
def alu (a : BitVec 8) (c : Bool) (sel : BitVec 3) (v : BitVec 8) : Alu :=
  ⟨aluWa sel, aluWc sel, aluCy a c sel v, aluZ a sel v, aluN a sel v, aluRes a sel v⟩

/-- Slot `m`'s op code. -/
def opSel (i : Input) (m : Nat) : BitVec 3 := slice i.sel (3 * m) 3

/-- Slot `m`'s move data. -/
def opData (i : Input) (m : Nat) : BitVec 8 := slice i.d (8 * m) 8

/-- Slot `m`'s ALU result on the current `A`/`C`. -/
def slot (s : State) (i : Input) (m : Nat) : Alu :=
  alu s.a s.c (opSel i m) (opData i m)

/-- No slot hits: a zero result, matching the RTL's all-zero OR. -/
def noResult : Alu := ⟨false, false, false, false, false, 0⟩

/-- The accumulator destination-code map of ISA_TABLES_V2: `ACC.LD..ACC.CMP`
are destination codes 7..13 and the RTL's per-slot op code is 0..6.  Any other
destination code takes the RTL `default:` (CMP, code 6); project.v forms this
with one `case` per slot and `units_check.py` proves the elaborated slices
implement it. -/
def opCodeOf (dst : BitVec 6) : BitVec 3 :=
  if dst = 7 then 0
  else if dst = 8 then 1
  else if dst = 9 then 2
  else if dst = 10 then 3
  else if dst = 11 then 4
  else if dst = 12 then 5
  else 6

/-- The SPEC reading of one cycle, field by field: the one hit slot's op and
data are applied.  With several hits the lowest slot wins here; the RTL's
committed contract has at most one (`OneHotOrZero`), and the restructure
theorem assumes it. -/
def winnerWa (_s : State) (i : Input) : Bool :=
  if i.hit = 0 then false
  else if bitAt i.hit 0 then aluWa (opSel i 0)
  else if bitAt i.hit 1 then aluWa (opSel i 1)
  else if bitAt i.hit 2 then aluWa (opSel i 2)
  else if bitAt i.hit 3 then aluWa (opSel i 3)
  else if bitAt i.hit 4 then aluWa (opSel i 4)
  else aluWa (opSel i 5)

def winnerWc (_s : State) (i : Input) : Bool :=
  if i.hit = 0 then false
  else if bitAt i.hit 0 then aluWc (opSel i 0)
  else if bitAt i.hit 1 then aluWc (opSel i 1)
  else if bitAt i.hit 2 then aluWc (opSel i 2)
  else if bitAt i.hit 3 then aluWc (opSel i 3)
  else if bitAt i.hit 4 then aluWc (opSel i 4)
  else aluWc (opSel i 5)

def winnerCy (s : State) (i : Input) : Bool :=
  if i.hit = 0 then false
  else if bitAt i.hit 0 then aluCy s.a s.c (opSel i 0) (opData i 0)
  else if bitAt i.hit 1 then aluCy s.a s.c (opSel i 1) (opData i 1)
  else if bitAt i.hit 2 then aluCy s.a s.c (opSel i 2) (opData i 2)
  else if bitAt i.hit 3 then aluCy s.a s.c (opSel i 3) (opData i 3)
  else if bitAt i.hit 4 then aluCy s.a s.c (opSel i 4) (opData i 4)
  else aluCy s.a s.c (opSel i 5) (opData i 5)

def winnerZ (s : State) (i : Input) : Bool :=
  if i.hit = 0 then false
  else if bitAt i.hit 0 then aluZ s.a (opSel i 0) (opData i 0)
  else if bitAt i.hit 1 then aluZ s.a (opSel i 1) (opData i 1)
  else if bitAt i.hit 2 then aluZ s.a (opSel i 2) (opData i 2)
  else if bitAt i.hit 3 then aluZ s.a (opSel i 3) (opData i 3)
  else if bitAt i.hit 4 then aluZ s.a (opSel i 4) (opData i 4)
  else aluZ s.a (opSel i 5) (opData i 5)

def winnerN (s : State) (i : Input) : Bool :=
  if i.hit = 0 then false
  else if bitAt i.hit 0 then aluN s.a (opSel i 0) (opData i 0)
  else if bitAt i.hit 1 then aluN s.a (opSel i 1) (opData i 1)
  else if bitAt i.hit 2 then aluN s.a (opSel i 2) (opData i 2)
  else if bitAt i.hit 3 then aluN s.a (opSel i 3) (opData i 3)
  else if bitAt i.hit 4 then aluN s.a (opSel i 4) (opData i 4)
  else aluN s.a (opSel i 5) (opData i 5)

def winnerRes (s : State) (i : Input) : BitVec 8 :=
  if i.hit = 0 then 0
  else if bitAt i.hit 0 then aluRes s.a (opSel i 0) (opData i 0)
  else if bitAt i.hit 1 then aluRes s.a (opSel i 1) (opData i 1)
  else if bitAt i.hit 2 then aluRes s.a (opSel i 2) (opData i 2)
  else if bitAt i.hit 3 then aluRes s.a (opSel i 3) (opData i 3)
  else if bitAt i.hit 4 then aluRes s.a (opSel i 4) (opData i 4)
  else aluRes s.a (opSel i 5) (opData i 5)

/-- The SPEC reading as one record, for the restructure theorem. -/
def winnerResult (s : State) (i : Input) : Alu :=
  ⟨winnerWa s i, winnerWc s i, winnerCy s i, winnerZ s i, winnerN s i,
   winnerRes s i⟩

/-- `A'`: a writing op takes its result; otherwise `A` holds. -/
def aNext (s : State) (i : Input) : BitVec 8 :=
  if !i.resetN then 0
  else if winnerWa s i then winnerRes s i else s.a

/-- `C'`: an op that writes the flag takes its carry/borrow; otherwise `C`
holds.  `LD`, `AND`, `OR` and `XOR` do not write `C`. -/
def cNext (s : State) (i : Input) : Bool :=
  if !i.resetN then false
  else if winnerWc s i then winnerCy s i else s.c

/-- `Z'`: every applied op sets it; with no hit it holds. -/
def zNext (s : State) (i : Input) : Bool :=
  if !i.resetN then false
  else if i.hit = 0 then s.z else winnerZ s i

/-- `N'`: every applied op sets it; with no hit it holds. -/
def nNext (s : State) (i : Input) : Bool :=
  if !i.resetN then false
  else if i.hit = 0 then s.n else winnerN s i

/-- `Rk' = v` for each writing `Rk` group; the four groups are independent. -/
def rNext (s : State) (i : Input) : BitVec 32 :=
  if !i.resetN then 0
  else
  ((if bitAt i.rWe 0 then i.rD else s.r) &&& (0x000000FF : BitVec 32)) |||
  ((if bitAt i.rWe 1 then i.rD else s.r) &&& (0x0000FF00 : BitVec 32)) |||
  ((if bitAt i.rWe 2 then i.rD else s.r) &&& (0x00FF0000 : BitVec 32)) |||
  ((if bitAt i.rWe 3 then i.rD else s.r) &&& (0xFF000000 : BitVec 32))

/-- The one-step transition. -/
def step (s : State) (i : Input) : State :=
  ⟨aNext s i, zNext s i, cNext s i, nNext s i, rNext s i⟩

/-- The accumulator trace: state during cycle `n`. -/
def stateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => step s i) inputs initial n

theorem stateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    stateAt inputs initial (n + 1) = step (stateAt inputs initial n) (inputs n) := rfl

/-- `hit` is zero or one-hot: the write-group contract that at most one move
writes the accumulator group (SPEC_V2 §6).  For six slots this is exactly the
seven vectors of Hamming weight at most one. -/
def OneHotOrZero (x : BitVec 6) : Prop :=
  x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 8 ∨ x = 16 ∨ x = 32

/-- A one-hot hit vector at slot `m` satisfies the contract. -/
theorem oneHotOrZero_shift (m : Nat) (hm : m < 6) :
    OneHotOrZero ((1 : BitVec 6) <<< m) := by
  have h : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [OneHotOrZero]
  all_goals decide

/-- The ALU result packed as the RTL's 13-bit `{wa, wc, cy, z, n, res}`. -/
def pack (r : Alu) : BitVec 13 :=
  (if r.wa then (1 : BitVec 13) <<< 12 else 0) |||
  (if r.wc then (1 : BitVec 13) <<< 11 else 0) |||
  (if r.cy then (1 : BitVec 13) <<< 10 else 0) |||
  (if r.z then (1 : BitVec 13) <<< 9 else 0) |||
  (if r.n then (1 : BitVec 13) <<< 8 else 0) |||
  r.res.setWidth 13

/-- The field extraction of the packed result. -/
def unpack (x : BitVec 13) : Alu :=
  ⟨bitAt x 12, bitAt x 11, bitAt x 10, bitAt x 9, bitAt x 8, x.truncate 8⟩

theorem unpack_pack (r : Alu) : unpack (pack r) = r := by
  rcases r with ⟨wa, wc, cy, z, n, res⟩
  cases wa <;> cases wc <;> cases cy <;> cases z <;> cases n <;>
    simp [pack, unpack, bitAt]
  all_goals bv_decide

/-- The RTL restructure: one masked ALU result per slot, OR-ed together
(`o` in `src/md2_acc.v`). -/
def slotsPacked (s : State) (i : Input) : BitVec 13 :=
  (0 : BitVec 13) |||
  (if bitAt i.hit 0 then pack (slot s i 0) else 0) |||
  (if bitAt i.hit 1 then pack (slot s i 1) else 0) |||
  (if bitAt i.hit 2 then pack (slot s i 2) else 0) |||
  (if bitAt i.hit 3 then pack (slot s i 3) else 0) |||
  (if bitAt i.hit 4 then pack (slot s i 4) else 0) |||
  (if bitAt i.hit 5 then pack (slot s i 5) else 0)

/-- With no hit the OR of masked slots is zero. -/
theorem slotsPacked_zero (s : State) (i : Input) (h : i.hit = 0) :
    slotsPacked s i = 0 := by
  simp [slotsPacked, h, bitAt]

/-- With one hit at `m` the OR of masked slots is exactly slot `m`'s pack. -/
theorem slotsPacked_onehot (s : State) (i : Input) (m : Nat) (hm : m < 6)
    (h : i.hit = (1 : BitVec 6) <<< m) :
    slotsPacked s i = pack (slot s i m) := by
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [slotsPacked, h] <;>
    simp [bitAt]

/-- The SPEC reading is exactly slot `m` when only `m` hits. -/
theorem winnerResult_eq_slot (s : State) (i : Input) (m : Nat) (hm : m < 6)
    (h : i.hit = (1 : BitVec 6) <<< m) :
    winnerResult s i = slot s i m := by
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [winnerResult, winnerWa, winnerWc, winnerCy, winnerZ, winnerN,
      winnerRes, slot, alu, h, bitAt]

/-- With no hit the SPEC reading is the zero result. -/
theorem winnerResult_zero (s : State) (i : Input) (h : i.hit = 0) :
    winnerResult s i = noResult := by
  simp [winnerResult, winnerWa, winnerWc, winnerCy, winnerZ, winnerN,
    winnerRes, noResult, h]

/-- The restructure equals the specification under the one-hot-or-zero
premise: the per-slot ALUs plus the hit mask compute exactly the winner's op on
the winner's data. -/
theorem slotsPacked_eq_winner (s : State) (i : Input) (h : OneHotOrZero i.hit) :
    unpack (slotsPacked s i) = winnerResult s i := by
  rcases h with h | h | h | h | h | h | h
  · rw [slotsPacked_zero s i h, winnerResult_zero s i h]
    simp [unpack, noResult, bitAt]
  · rw [slotsPacked_onehot s i 0 (by decide) h, unpack_pack,
        winnerResult_eq_slot s i 0 (by decide) h]
  · rw [slotsPacked_onehot s i 1 (by decide) h, unpack_pack,
        winnerResult_eq_slot s i 1 (by decide) h]
  · rw [slotsPacked_onehot s i 2 (by decide) h, unpack_pack,
        winnerResult_eq_slot s i 2 (by decide) h]
  · rw [slotsPacked_onehot s i 3 (by decide) h, unpack_pack,
        winnerResult_eq_slot s i 3 (by decide) h]
  · rw [slotsPacked_onehot s i 4 (by decide) h, unpack_pack,
        winnerResult_eq_slot s i 4 (by decide) h]
  · rw [slotsPacked_onehot s i 5 (by decide) h, unpack_pack,
        winnerResult_eq_slot s i 5 (by decide) h]

/-- `CMP` leaves `A` unchanged and writes `C`; SPEC v1 §6.1. -/
theorem cmp_leaves_a (x : BitVec 8) (c : Bool) (v : BitVec 8) :
    (alu x c 6 v).wa = false := by
  simp only [alu]
  decide

end Acc

end Metronome.Units
