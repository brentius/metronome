import Metronome.Transition
import Std.Tactic.BVDecide

/-!
# Chip-top debug, pin-replay, program-memory and reset logic

This module is the independent specification of the last chip-top logic of
[src/project.v](../../src/project.v) that the other cuts leave outside
their boundaries:

* the pin level and edge vectors (`pins_level`, `pins_prev`, `lvl`, `rise`,
  `fall`) under the v4 replay mask, from SPEC_V2 §2 and §13.2;
* the v3/v4 debug registers of the control block: the execution digest
  (`MCTL`, `MISR`, SPEC_V2 §12.2), the edge-capture/replay control (`ECTL`,
  `EMASK`, `RLV`, `DC`, `cev`, SPEC_V2 §12.4 and §13.2);
* the host/fetch port muxing of the two program memories, from SPEC_V2 §5,
  §9 and 9a.8;
* the reset synchroniser `rst_m`/`rst_q`, from SPEC_V2 §1.

`debug_check.py` re-elaborates the chip top with Yosys, extracts the cones
fail-closed and proves the generated `rtl*` definitions equal to the
specifications below.  Everything here is written from the specification text,
not from the RTL.  Where the RTL is more explicit than the text (the frozen
branch of `DC`, the byte-split host/CW priority) the difference is recorded in
`DEBUG_NOTES.md`.

## Cycle boundary

`run` (from `Metronome.Transition`) is the register state during cycle `n`,
after `n` sampled rising edges, as in every other cut of the suite.  A sampled
`resetN` low is a cycle in which the RTL's synchronous reset branch is taken;
the asynchronous assertion between edges is outside the discrete model.
-/

set_option autoImplicit false

namespace Metronome.Debug

/-- One net bit as a `Bool`, the shape of a scalar RTL operand. -/
def bitAt {w : Nat} (x : BitVec w) (i : Nat) : Bool :=
  ((BitVec.truncate 1 (BitVec.ushiftRight x i)) != 0)

/-- Bits `off … off+n-1` of `x`, the shape the RTL adapter emits for a slice. -/
def slice {w : Nat} (x : BitVec w) (off n : Nat) : BitVec n :=
  BitVec.truncate n (BitVec.ushiftRight x off)

/-- A 13-bit vector is its high five bits and its low byte, in the RTL's
concatenation order. -/
theorem slice13 (x : BitVec 13) : (slice x 8 5) ++ (slice x 0 8) = x := by
  unfold slice
  bv_decide

/-! ## (a) Pin levels and edges under the replay mask

SPEC_V2 §2: the synchronised level of input pin `k` is `PIN[k] = s2[k]`,
`RISE[k] = s2 & !sp` and `FALL[k] = !s2 & sp`; the input pins P0..P12 are
`uio_in[0..7]`, `ui_in[3..7]`, and a select of 13..15 reads constant 0.

SPEC_V2 §13.2: while `RPL` is set, the synchronised level of every pin in
`EMASK` is `RLV`, its previous level is `RLV` of the previous cycle, and the pad
is ignored.  That is a per-pin substitution on the two synchroniser words: the
replay mask is `EMASK & {13{RPL}}`.
-/

namespace Pins

/-- The synchronised pin vector `{s2[15:11], s2[7:0]}` of SPEC_V2 §2: bit `k` is
input pin P`k` for `k < 13` (`k < 8` is `uio_in[k]`, `8 ≤ k < 13` is
`ui_in[k-3]`); selects 13..15 are not part of the vector. -/
def pinVec (raw : BitVec 16) : BitVec 13 := (slice raw 11 5) ++ (slice raw 0 8)

/-- `{13{replay}}`: all ones while `RPL`, zero otherwise. -/
def maskOf (replay : Bool) : BitVec 13 := if replay then (0x1FFF : BitVec 13) else 0

/-- The replay mask `EMASK & {13{RPL}}` of SPEC_V2 §13.2. -/
def mask (emask : BitVec 13) (replay : Bool) : BitVec 13 := emask &&& maskOf replay

/-- The synchronised pin level of the cycle: unmasked pins read `s2`, masked pins
read `RLV` (SPEC_V2 §13.2). -/
def level (s2 rlv emask : BitVec 13) (replay : Bool) : BitVec 13 :=
  (s2 &&& ~~~mask emask replay) ||| (rlv &&& mask emask replay)

/-- The previous synchronised level: `sp` and `RLV` of the previous cycle. -/
def previous (sp rlvPrev emask : BitVec 13) (replay : Bool) : BitVec 13 :=
  (sp &&& ~~~mask emask replay) ||| (rlvPrev &&& mask emask replay)

/-- The 16-bit level vector `lvl = {3'd0, pins_level}`: pins 13..15 read 0
(SPEC_V2 §2). -/
def lvl (l : BitVec 13) : BitVec 16 := (0 : BitVec 3) ++ l

/-- `RISE = level & !previous` on the 13 input pins, zero above (SPEC_V2 §2). -/
def rise (l p : BitVec 13) : BitVec 16 := (0 : BitVec 3) ++ (l &&& ~~~p)

/-- `FALL = !level & previous` on the 13 input pins, zero above. -/
def fall (l p : BitVec 13) : BitVec 16 := (0 : BitVec 3) ++ (~~~l &&& p)

theorem maskOf_false : maskOf false = 0 := rfl

theorem maskOf_true : maskOf true = (0x1FFF : BitVec 13) := rfl

/-- With `RPL` clear the mask is zero. -/
theorem mask_off (emask : BitVec 13) : mask emask false = 0 := by
  unfold mask maskOf
  simp

/-- Masked pins read `RLV`, whatever `s2` holds (SPEC_V2 §13.2). -/
theorem level_masked (s2 rlv emask : BitVec 13) (replay : Bool) :
    level s2 rlv emask replay &&& mask emask replay = rlv &&& mask emask replay := by
  unfold level
  bv_decide

/-- Unmasked pins read the synchronised level, whatever `RLV` holds. -/
theorem level_unmasked (s2 rlv emask : BitVec 13) (replay : Bool) :
    level s2 rlv emask replay &&& ~~~mask emask replay = s2 &&& ~~~mask emask replay := by
  unfold level
  bv_decide

/-- With `RPL` clear the level is the synchronised pins. -/
theorem level_no_replay (s2 rlv emask : BitVec 13) :
    level s2 rlv emask false = s2 := by
  unfold level mask maskOf
  simp
  bv_decide

/-- With `RPL` set the pad bits of every masked pin do not matter: two
synchroniser words that agree outside the mask give the same level. -/
theorem level_replay_ignores_pad (s2 s2' rlv emask : BitVec 13)
    (h : s2 &&& ~~~emask = s2' &&& ~~~emask) :
    level s2 rlv emask true = level s2' rlv emask true := by
  unfold level mask maskOf
  simp only [ite_true]
  bv_decide

/-- Pins 13..15 are constant 0 (SPEC_V2 §2). -/
theorem lvl_high_zero (l : BitVec 13) :
    bitAt (lvl l) 13 = false ∧ bitAt (lvl l) 14 = false ∧ bitAt (lvl l) 15 = false := by
  unfold lvl bitAt
  bv_decide

/-- The low 13 bits of `lvl` are the pin level. -/
theorem lvl_low (l : BitVec 13) : slice (lvl l) 0 13 = l := by
  unfold lvl slice
  bv_decide

/-- `RISE`/`FALL` are the level/previous comparison of the 13 pins, zero above
(SPEC_V2 §2). -/
theorem rise_spec (l p : BitVec 13) : rise l p = (0 : BitVec 3) ++ (l &&& ~~~p) := rfl

theorem fall_spec (l p : BitVec 13) : fall l p = (0 : BitVec 3) ++ (~~~l &&& p) := rfl

/-- A rise and a fall of one pin cannot both be asserted. -/
theorem rise_fall_exclusive (l p : BitVec 13) :
    (slice (rise l p) 0 13) &&& (slice (fall l p) 0 13) = 0 := by
  unfold rise fall slice
  bv_decide

/-- An edge vector is nonzero exactly when some pin changed. -/
theorem edge_nonzero (l p : BitVec 13) :
    ((slice (rise l p) 0 13 ||| slice (fall l p) 0 13) != 0) = (l != p) := by
  unfold rise fall slice
  bv_decide

end Pins

/-! ## (b1) Execution digest: `MCTL` and `MISR` (SPEC_V2 §12.2)

`D = {OEN[7:0], OUT[13:0]}` (22 bits: `OUT[o]` in bit `o`, `OEN[o]` in bit
`14+o`), the pin registers' values in cycle t.  `MEN` is `MCTL` bit 0, and

```
if the host writes MCTL with bit 1 set in cycle t:  M' = 0
elif MEN && !FRZ:  M' = ((M << 1) mod 2^32) ^ (M[31] ? 0x04C11DB7 : 0) ^ D
else:              M' = M
```
-/

namespace Digest

/-- The CRC-32 generator polynomial in Galois form, shifting left
(`machine.MISR_POLY`). -/
def poly : BitVec 32 := 0x04C11DB7

/-- The digest input register vector `{OEN[7:0], OUT[13:0]}` (SPEC_V2 §12.2). -/
def dataVec (oEe : BitVec 8) (oOut : BitVec 14) : BitVec 32 :=
  (0 : BitVec 10) ++ oEe ++ oOut

/-- The digest state: `MEN` and `M`. -/
structure State where
  /-- `MEN`, `MCTL` bit 0. -/
  men : Bool
  /-- `M`, the 32-bit signature. -/
  misr : BitVec 32
  deriving DecidableEq, Repr

@[ext] theorem State.ext {a b : State} (h1 : a.men = b.men) (h2 : a.misr = b.misr) :
    a = b := by
  obtain ⟨x1, x2⟩ := a
  obtain ⟨y1, y2⟩ := b
  simp_all

/-- The sampled inputs of the digest block. -/
structure Input where
  /-- `rst_q`, the synchronised reset (`resetN`). -/
  resetN : Bool
  /-- The host write strobe of `MCTL` (`d_wr_mctl`). -/
  dWrMctl : Bool
  /-- The written byte `h_wd`; bit 0 is `MEN`, bit 1 clears `M`. -/
  hWd : BitVec 8
  /-- `FRZ`: a frozen cycle holds `M`. -/
  frz : Bool
  /-- The output-enable pin registers `OEN[7:0]`. -/
  oEe : BitVec 8
  /-- The output pin registers `OUT[13:0]`. -/
  oOut : BitVec 14
  deriving DecidableEq, Repr

/-- `MEN` next: a host `MCTL` write loads bit 0, otherwise it holds. -/
def menNext (men : Bool) (i : Input) : Bool := if i.dWrMctl then bitAt i.hWd 0 else men

/-- The `MISR` next state of SPEC_V2 §12.2. -/
def misrNext (men : Bool) (m : BitVec 32) (i : Input) : BitVec 32 :=
  if i.dWrMctl && bitAt i.hWd 1 then 0
  else if men && !i.frz then
    (BitVec.shiftLeft m 1) ^^^ (if bitAt m 31 then poly else 0) ^^^ dataVec i.oEe i.oOut
  else m

/-- The reset state: all v3 registers are 0 after reset. -/
def resetState : State := ⟨false, 0⟩

/-- One cycle of the digest block, with the synchronous reset sample. -/
def step (s : State) (i : Input) : State :=
  if i.resetN then ⟨menNext s.men i, misrNext s.men s.misr i⟩ else resetState

/-- A host `MCTL` write with bit 1 clears `M`, whatever `MEN` and `FRZ` say. -/
theorem misr_clear (men : Bool) (m : BitVec 32) (i : Input) (h0 : i.dWrMctl = true)
    (h1 : bitAt i.hWd 1 = true) : misrNext men m i = 0 := by
  unfold misrNext
  simp [h0, h1]

/-- A frozen cycle holds `M` (SPEC_V2 §12.3: `M` holds). -/
theorem misr_frozen_holds (men : Bool) (m : BitVec 32) (i : Input) (hf : i.frz = true)
    (hc : (i.dWrMctl && bitAt i.hWd 1) = false) : misrNext men m i = m := by
  unfold misrNext
  simp [hc, hf]

/-- Without a host `MCTL` write and with reset released, `MEN` holds. -/
theorem men_holds (men : Bool) (i : Input) (h : i.dWrMctl = false) :
    menNext men i = men := by
  unfold menNext
  simp [h]

/-- A host `MCTL` write loads `MEN` from bit 0. -/
theorem men_write (men : Bool) (i : Input) (h : i.dWrMctl = true) :
    menNext men i = bitAt i.hWd 0 := by
  unfold menNext
  simp [h]

/-- The `M` equation is SPEC_V2 §12.2's shift, conditional xor and data xor when
it advances. -/
theorem misr_advances (men : Bool) (m : BitVec 32) (i : Input)
    (hc : (i.dWrMctl && bitAt i.hWd 1) = false)
    (hm : men = true) (hf : i.frz = false) :
    misrNext men m i =
      (BitVec.shiftLeft m 1) ^^^ (if bitAt m 31 then poly else 0) ^^^ dataVec i.oEe i.oOut := by
  unfold misrNext
  simp [hc, hm, hf]

/-- A device with `MEN = 0` never changes `M` (SPEC_V2 §12.2's "else"). -/
theorem misr_disabled_holds (men : Bool) (m : BitVec 32) (i : Input)
    (hc : (i.dWrMctl && bitAt i.hWd 1) = false) (hm : men = false) :
    misrNext men m i = m := by
  unfold misrNext
  simp [hc, hm]

/-- The polynomial is the CRC-32 generator. -/
theorem poly_spec : poly = (0x04C11DB7 : BitVec 32) := rfl

/-- The data vector puts `OUT[o]` in bit `o` and `OEN[o]` in bit `14 + o`. -/
theorem dataVec_spec (oEe : BitVec 8) (oOut : BitVec 14) :
    dataVec oEe oOut = (0 : BitVec 10) ++ oEe ++ oOut := rfl

/-- The data vector's low half is `OUT` and its high byte is `OEN`
(SPEC_V2 §12.2's bit order). -/
theorem dataVec_split (oEe : BitVec 8) (oOut : BitVec 14) :
    slice (dataVec oEe oOut) 0 14 = oOut ∧ slice (dataVec oEe oOut) 14 8 = oEe := by
  unfold dataVec slice
  constructor <;> bv_decide

end Digest

/-! ## (b2) Edge capture and replay: `ECTL`, `EMASK`, `RLV`, `DC` (SPEC_V2 §12.4, §13.2)

The runtime registers are `RPL`, `CEN` (`ECTL` bits 1, 0), `EMASK` (13),
`RLV` (13), `RLV` of the previous cycle and the 19-bit counter `DC`.  The host
writes these bytes, and a drained core write (`CW.D`) may target the same bytes;
SPEC_V2 §13.1: a runtime write happens "before a host write in the same cycle,
which wins".  The two strobes enter this specification as
`dWrEctl`/`hEctl`, `dWrEm0`/`hEm0`, …: `dWr*` is the combined strobe and `h*`
selects the host source, so the priority is the `if h then host else core`
below.

`DC` (SPEC_V2 §12.4, §13.2) counts cycles since the previous edge event, is
cleared by every `ECTL` write (host priority, also while frozen), saturates at
`2^19 - 1`, is zero while capture is off, is reused as the replay timer, and
holds in a frozen cycle (SPEC_V2 §12.3).
-/

namespace Ctrl

/-- `{1'b0, dc} + 1`, the RTL's `replay_tick` (`dc + 1` compared with the
record interval). -/
def tick (dc : BitVec 19) : BitVec 20 := ((0 : BitVec 1) ++ dc) + 1

/-- `{1'b0, WB[31:13]}`, the record's `DC` field as the replay interval. -/
def interval (word : BitVec 32) : BitVec 20 := (0 : BitVec 1) ++ slice word 13 19

/-- §13.2's `apply = RPL && WV && DC + 1 >= WB.DC` (the RTL also gates it on
`!FRZ`, which is §12.4's "in an unfrozen cycle"). -/
def apply (replay : Bool) (frz : Bool) (valid : Bool) (dc : BitVec 19)
    (word : BitVec 32) : Bool :=
  replay && !frz && valid && decide (tick dc >= interval word)

/-- §13.2's `late = apply && DC + 1 > WB.DC`.  Since `tick > interval` implies
`tick >= interval`, this is `apply`'s terms with the strict comparison. -/
def late (replay : Bool) (frz : Bool) (valid : Bool) (dc : BitVec 19)
    (word : BitVec 32) : Bool :=
  replay && !frz && valid && decide (tick dc > interval word)

/-- §13.2's level substitution: `RLV' = (RLV & ~EMASK) | (WB[12:0] & EMASK)` in
an apply cycle, `RLV` otherwise. -/
def replayLevels (rlv emask : BitVec 13) (apply : Bool) (word : BitVec 32) : BitVec 13 :=
  if apply then (rlv &&& ~~~emask) ||| (slice word 0 13 &&& emask) else rlv

/-- §12.4's `cev = CEN && ((RISE | FALL)[12:0] & EMASK) != 0` in an unfrozen,
non-replay cycle (§13.2: `RPL` takes priority over `CEN`). -/
def cev (cen replay frz : Bool) (rise fall : BitVec 16) (emask : BitVec 13) : Bool :=
  cen && !replay && !frz && (slice (rise ||| fall) 0 13 &&& emask) != 0

/-- The capture/replay state. -/
structure State where
  /-- `ECTL` bit 1, `RPL`. -/
  replay : Bool
  /-- `ECTL` bit 0, `CEN`. -/
  cen : Bool
  /-- `EMASK`, 13 pins. -/
  emask : BitVec 13
  /-- `RLV`, 13 pins. -/
  rlv : BitVec 13
  /-- `RLV` of the previous cycle. -/
  rlvPrev : BitVec 13
  /-- `DC`, the capture counter / replay timer. -/
  dc : BitVec 19
  deriving DecidableEq, Repr

@[ext] theorem State.ext {a b : State} (h1 : a.replay = b.replay) (h2 : a.cen = b.cen)
    (h3 : a.emask = b.emask) (h4 : a.rlv = b.rlv) (h5 : a.rlvPrev = b.rlvPrev)
    (h6 : a.dc = b.dc) : a = b := by
  obtain ⟨x1, x2, x3, x4, x5, x6⟩ := a
  obtain ⟨y1, y2, y3, y4, y5, y6⟩ := b
  simp_all

/-- The sampled inputs of the capture/replay block. -/
structure Input where
  /-- `rst_q`, the synchronised reset. -/
  resetN : Bool
  /-- `FRZ`. -/
  frz : Bool
  /-- Host write strobe of `ECTL`. -/
  hEctl : Bool
  /-- Combined host-or-drain strobe of `ECTL`. -/
  dWrEctl : Bool
  /-- Host write strobe of `EMASK` byte 0. -/
  hEm0 : Bool
  /-- Combined strobe of `EMASK` byte 0. -/
  dWrEm0 : Bool
  /-- Host write strobe of `EMASK` byte 1. -/
  hEm1 : Bool
  /-- Combined strobe of `EMASK` byte 1. -/
  dWrEm1 : Bool
  /-- Host write strobe of `RLV` byte 0. -/
  hRlv0 : Bool
  /-- Combined strobe of `RLV` byte 0. -/
  dWrRlv0 : Bool
  /-- Host write strobe of `RLV` byte 1. -/
  hRlv1 : Bool
  /-- Combined strobe of `RLV` byte 1. -/
  dWrRlv1 : Bool
  /-- The host write byte `h_wd`. -/
  hWd : BitVec 8
  /-- The queued core write byte `cw_pending_data` (drained here as a runtime
  write, SPEC_V2 §13.1). -/
  cwData : BitVec 8
  /-- S0's `replay_valid`, two bits in the RTL; bit 0 is the select stream. -/
  replayValid : BitVec 2
  /-- S0's `replay_word`, the queued capture record. -/
  replayWord : BitVec 32
  /-- `rise[15:0]` from the pin cut. -/
  rise : BitVec 16
  /-- `fall[15:0]` from the pin cut. -/
  fall : BitVec 16
  deriving DecidableEq, Repr

/-- The `ECTL` replay bit: a host write wins to the same byte (SPEC_V2 §13.1);
without a write it holds. -/
def replayNext (s : State) (i : Input) : Bool :=
  if i.dWrEctl then (if i.hEctl then bitAt i.hWd 1 else bitAt i.cwData 1) else s.replay

/-- The `ECTL` capture-enable bit, same priority. -/
def cenNext (s : State) (i : Input) : Bool :=
  if i.dWrEctl then (if i.hEctl then bitAt i.hWd 0 else bitAt i.cwData 0) else s.cen

/-- The `EMASK` next state: byte 0 from `h_wd`/`cw_pending_data`, byte 1 from
their low five bits, each byte independently. -/
def emaskNext (emask : BitVec 13) (i : Input) : BitVec 13 :=
  (if i.dWrEm1 then (if i.hEm1 then slice i.hWd 0 5 else slice i.cwData 0 5)
   else slice emask 8 5) ++
  (if i.dWrEm0 then (if i.hEm0 then i.hWd else i.cwData) else slice emask 0 8)

/-- The `RLV` next state: the applied replay byte or the shifted replay levels,
with the host/core write covering the byte it targets. -/
def rlvNext (s : State) (i : Input) : BitVec 13 :=
  let lv := replayLevels s.rlv s.emask (apply s.replay i.frz (bitAt i.replayValid 0) s.dc
    i.replayWord) i.replayWord
  (if i.dWrRlv1 then (if i.hRlv1 then slice i.hWd 0 5 else slice i.cwData 0 5)
   else slice lv 8 5) ++
  (if i.dWrRlv0 then (if i.hRlv0 then i.hWd else i.cwData) else slice lv 0 8)

/-- The `RLV` previous-level register: `FRZ` holds it (SPEC_V2 §12.3). -/
def rlvPrevNext (s : State) (i : Input) : BitVec 13 := if i.frz then s.rlvPrev else s.rlv

/-- The `DC` next state: `ECTL` write clears (also frozen), `FRZ` holds,
`apply` clears, capture off clears, an edge event sets 1, otherwise it counts and
saturates at `2^19 - 1`. -/
def dcNext (s : State) (i : Input) : BitVec 19 :=
  if i.dWrEctl then 0
  else if i.frz then s.dc
  else if apply s.replay i.frz (bitAt i.replayValid 0) s.dc i.replayWord ||
      (!s.replay && !s.cen) then 0
  else if cev s.cen s.replay i.frz i.rise i.fall s.emask then 1
  else if s.dc != (0x7FFFF : BitVec 19) then s.dc + 1 else s.dc

/-- The reset state: all v3 registers are 0 after reset. -/
def resetState : State := ⟨false, false, 0, 0, 0, 0⟩

/-- One cycle of the capture/replay block, with the synchronous reset sample. -/
def step (s : State) (i : Input) : State :=
  if i.resetN then
    ⟨replayNext s i, cenNext s i, emaskNext s.emask i, rlvNext s i,
     rlvPrevNext s i, dcNext s i⟩
  else resetState

/-- A host `ECTL` write wins over a core drain in the same cycle (SPEC_V2 §13.1):
the byte comes from `h_wd`, independent of `cw_pending_data`. -/
theorem host_ectl_wins (s : State) (i : Input) (h : i.dWrEctl = true) (hh : i.hEctl = true) :
    replayNext s i = bitAt i.hWd 1 ∧ cenNext s i = bitAt i.hWd 0 := by
  unfold replayNext cenNext
  simp [h, hh]

/-- Without a host source, the same strobe takes the drained core byte. -/
theorem core_ectl_wins (s : State) (i : Input) (h : i.dWrEctl = true) (hh : i.hEctl = false) :
    replayNext s i = bitAt i.cwData 1 ∧ cenNext s i = bitAt i.cwData 0 := by
  unfold replayNext cenNext
  simp [h, hh]

/-- Every `ECTL` write clears `DC`, also in a frozen cycle (SPEC_V2 §12.4). -/
theorem dc_write_clears (s : State) (i : Input) (h : i.dWrEctl = true) :
    dcNext s i = 0 := by
  unfold dcNext
  simp [h]

/-- A frozen cycle without any of the four writes holds the whole block: the
pads, `EMASK`, `RLV` and `DC` keep their values (SPEC_V2 §12.3). -/
theorem frozen_holds (s : State) (i : Input) (hr : i.resetN = true) (hf : i.frz = true)
    (h0 : i.dWrEctl = false) (h1 : i.dWrEm0 = false) (h2 : i.dWrEm1 = false)
    (h3 : i.dWrRlv0 = false) (h4 : i.dWrRlv1 = false) : step s i = s := by
  have hstep : step s i =
      ⟨s.replay, s.cen, s.emask, s.rlv, s.rlvPrev, s.dc⟩ := by
    unfold step
    simp only [hr, ite_true]
    unfold replayNext cenNext emaskNext rlvNext rlvPrevNext dcNext replayLevels apply
    simp [h0, h1, h2, h3, h4, hf, slice13]
  rw [hstep]

/-- With capture off and no replay the counter is zero (SPEC_V2 §12.4's
`DC' = !CEN ? 0` under `!RPL`). -/
theorem dc_idle_zero (s : State) (i : Input) (hw : i.dWrEctl = false)
    (hf : i.frz = false) (hr : s.replay = false) (hc : s.cen = false) :
    dcNext s i = 0 := by
  unfold dcNext
  simp [hw, hf, hr, hc]

/-- `DC` saturates at 524,287 cycles (SPEC_V2 §12.4). -/
theorem dc_saturates (s : State) (i : Input) (hw : i.dWrEctl = false)
    (hf : i.frz = false) (ha : apply s.replay i.frz (bitAt i.replayValid 0) s.dc
      i.replayWord = false)
    (hr : s.replay = true) (hcev : cev s.cen s.replay i.frz i.rise i.fall s.emask = false)
    (hd : s.dc = 0x7FFFF) : dcNext s i = s.dc := by
  unfold dcNext
  simp_all

/-- An edge event in an unfrozen, non-replay capture cycle sets `DC` to 1
(SPEC_V2 §12.4's `DC' = cev ? 1 : …`). -/
theorem dc_edge_sets_one (s : State) (i : Input) (hw : i.dWrEctl = false)
    (hf : i.frz = false) (ha : apply s.replay i.frz (bitAt i.replayValid 0) s.dc
      i.replayWord = false)
    (hr : s.replay = false) (hc : s.cen = true)
    (hcev : cev s.cen s.replay i.frz i.rise i.fall s.emask = true) :
    dcNext s i = 1 := by
  unfold dcNext
  simp_all

/-- An `apply` cycle shifts the replay levels from the record, masked by `EMASK`
(SPEC_V2 §13.2). -/
theorem replay_levels_apply (rlv emask : BitVec 13) (word : BitVec 32) :
    replayLevels rlv emask true word = (rlv &&& ~~~emask) ||| (slice word 0 13 &&& emask) := by
  unfold replayLevels
  simp

/-- Masked bits of the replay levels come from the record (§13.2's per-pin
substitution). -/
theorem replay_levels_masked (rlv emask : BitVec 13) (word : BitVec 32) :
    replayLevels rlv emask true word &&& emask = slice word 0 13 &&& emask := by
  unfold replayLevels
  simp only [ite_true]
  bv_decide

/-- `cev` is exactly "some masked pin rose or fell in this cycle" (SPEC_V2
§12.4), in an unfrozen non-replay capture cycle. -/
theorem cev_spec (cen replay frz : Bool) (rise fall : BitVec 16) (emask : BitVec 13) :
    cev cen replay frz rise fall emask =
      (cen && !replay && !frz &&
       ((slice (rise ||| fall) 0 13) &&& emask) != 0) := rfl

/-- `cev` is false with `CEN` clear. -/
theorem cev_off (replay frz : Bool) (rise fall : BitVec 16) (emask : BitVec 13) :
    cev false replay frz rise fall emask = false := by
  unfold cev
  simp

/-- `cev` is false while `RPL` is set: replay takes priority over capture
(SPEC_V2 §13.2). -/
theorem cev_replay (cen frz : Bool) (rise fall : BitVec 16) (emask : BitVec 13) :
    cev cen true frz rise fall emask = false := by
  unfold cev
  simp

end Ctrl

/-! ## (c) Program-memory host/fetch port muxing (SPEC_V2 §5, §9, 9a.8)

Each core has a 256 x 64 program memory with a synchronous read.  The host
writes a program byte by byte lane: byte `k` of word `w` of core `c` at
`c*0x800 + 8w + k` holds word bits `8k+7..8k`.  So the word address is
`(ha - PROG_LO)[10:3]`, the lane is one-hot `1 << (ha - PROG_LO)[2:0]`, and
`a_prg[11]` selects the core.  Host writes take the memory port in that cycle
(§9); a fetch in the same cycle returns an undefined word (9a.8), which the cut
states as "the port carries the host's word address" — the word's content is
the SRAM macro's business.
-/

namespace Pmem

/-- `PRG_SH` of the RTL: the program window is split into two 0x800-byte core
halves, so bit 11 of the window offset selects the core. -/
def prgSh : Nat := 11

theorem prgSh_eq : prgSh = 11 := rfl

/-- The host write strobe of core 0's program memory. -/
def we0 (hWr inPrg : Bool) (a : BitVec 16) : Bool := hWr && inPrg && !bitAt a 11

/-- The host write strobe of core 1's program memory. -/
def we1 (hWr inPrg : Bool) (a : BitVec 16) : Bool := hWr && inPrg && bitAt a 11

/-- The one-hot byte lane of a host program write (§9's `[2:0]`). -/
def be (a : BitVec 16) : BitVec 8 := (1 : BitVec 8) <<< (slice a 0 3).toNat

/-- The word address of a host program write: `(ha - PROG_LO)[10:3]`. -/
def wordAddr (a : BitVec 16) : BitVec 8 := slice a 3 8

/-- The memory port address: the host's word address on a write, the core's
fetch address otherwise (§5's single port). -/
def portAddr (we : Bool) (host fetch : BitVec 8) : BitVec 8 := if we then host else fetch

/-- Core 0's fetch address is `fadr[7:0]`. -/
def fetchAddr0 (fadr : BitVec 16) : BitVec 8 := slice fadr 0 8

/-- Core 1's fetch address is `fadr[15:8]`. -/
def fetchAddr1 (fadr : BitVec 16) : BitVec 8 := slice fadr 8 8

theorem we0_spec (hWr inPrg : Bool) (a : BitVec 16) :
    we0 hWr inPrg a = (hWr && inPrg && !bitAt a prgSh) := rfl

theorem we1_spec (hWr inPrg : Bool) (a : BitVec 16) :
    we1 hWr inPrg a = (hWr && inPrg && bitAt a prgSh) := rfl

/-- At most one core's strobe is asserted for one host write. -/
theorem we_exclusive (hWr inPrg : Bool) (a : BitVec 16) :
    (we0 hWr inPrg a && we1 hWr inPrg a) = false := by
  unfold we0 we1
  cases hWr <;> cases inPrg <;> cases bitAt a 11 <;> simp

/-- The byte lane is one-hot: lane `k` is enabled exactly for the host byte
`hi ++ k` whose low three bits are `k` (§9's little-endian byte lane). -/
theorem be_low3 (hi : BitVec 13) (k : BitVec 3) :
    be (hi ++ k) = (1 : BitVec 8) <<< k.toNat := by
  unfold be slice
  bv_decide

/-- A byte lane is never zero: every host program write enables one lane. -/
theorem be_ne_zero (a : BitVec 16) : be a != 0 := by
  unfold be
  bv_decide

/-- The word address is the window offset's `[10:3]` (§5's 256 words of eight
bytes). -/
theorem wordAddr_spec (a : BitVec 16) : wordAddr a = slice a 3 8 := rfl

/-- A host write takes the port: the address presented is the host's word
address, not the core's fetch address (§9; 9a.8 calls the same-cycle fetch word
undefined). -/
theorem port_host (host fetch : BitVec 8) : portAddr true host fetch = host := rfl

/-- Without a host write the core's fetch address is presented. -/
theorem port_fetch (host fetch : BitVec 8) : portAddr false host fetch = fetch := rfl

end Pmem

/-! ## (d) The reset synchroniser (SPEC_V2 §1)

`rst_n` is asserted asynchronously and released synchronously through two flops;
`rst_q` is `rst_n` delayed by two rising edges, and every register is 0 while it
is low.  The discrete model samples `rst_n` once per cycle: a sampled low is the
asynchronous clear, and a sampled high advances the two-flop chain.  The
asynchronous assertion *between* sampled edges, and metastability, are outside
the model; the structural check ties the two registers to the RTL's
`always @(posedge clk or negedge rst_n)` with the active-low clear from `rst_n`.
-/

namespace Reset

/-- The two reset flops. -/
structure State where
  /-- `rst_m`, the first stage. -/
  rstM : Bool
  /-- `rst_q`, the internal synchronised reset. -/
  rstQ : Bool
  deriving DecidableEq, Repr

@[ext] theorem State.ext {a b : State} (h1 : a.rstM = b.rstM) (h2 : a.rstQ = b.rstQ) :
    a = b := by
  obtain ⟨x1, x2⟩ := a
  obtain ⟨y1, y2⟩ := b
  simp_all

/-- The sampled reset input. -/
structure Input where
  /-- The `rst_n` pin. -/
  rstN : Bool
  deriving DecidableEq, Repr

/-- The cleared state. -/
def resetState : State := ⟨false, false⟩

/-- SPEC_V2 §1: the asynchronous clear sets both flops low; a released edge
shifts `1` into the first flop and `rst_m` into the second. -/
def step (s : State) (i : Input) : State :=
  if i.rstN then ⟨true, s.rstM⟩ else resetState

/-- A sampled low clears both flops at the end of that cycle. -/
theorem step_low (s : State) : step s ⟨false⟩ = resetState := by
  unfold step resetState
  simp

/-- A released edge sets the first stage and shifts the old first stage into
`rst_q`. -/
theorem step_high (s : State) : step s ⟨true⟩ = ⟨true, s.rstM⟩ := by
  unfold step
  simp

/-- The sampled low, stated on an arbitrary input record. -/
theorem step_low_of (s : State) (i : Input) (h : i.rstN = false) :
    step s i = resetState := by
  unfold step resetState
  simp [h]

/-- The released edge, stated on an arbitrary input record. -/
theorem step_high_of (s : State) (i : Input) (h : i.rstN = true) :
    step s i = ⟨true, s.rstM⟩ := by
  unfold step
  simp [h]

/-- After one sampled reset edge `rst_q` is low. -/
theorem rstq_low_after_reset (inputs : Nat → Input) (initial : State) (n : Nat)
    (h : (inputs n).rstN = false) : (run step inputs initial (n + 1)).rstQ = false := by
  rw [run_succ, step_low_of _ _ h]
  rfl

/-- After one sampled reset edge the first stage is low too. -/
theorem rstm_low_after_reset (inputs : Nat → Input) (initial : State) (n : Nat)
    (h : (inputs n).rstN = false) : (run step inputs initial (n + 1)).rstM = false := by
  rw [run_succ, step_low_of _ _ h]
  rfl

/-- `rst_q` is still low in the cycle after a sampled reset, because the first
stage was cleared too: two rising edges are needed for release. -/
theorem rstq_low_one_more (inputs : Nat → Input) (initial : State) (n : Nat)
    (h : (inputs n).rstN = false) : (run step inputs initial (n + 2)).rstQ = false := by
  rw [show n + 2 = (n + 1) + 1 from rfl, run_succ]
  cases hi : (inputs (n + 1)).rstN
  · rw [step_low_of _ _ hi]
    rfl
  · rw [step_high_of _ _ hi, rstm_low_after_reset inputs initial n h]

/-- Two released edges after a reset release `rst_q`. -/
theorem rstq_after_two (inputs : Nat → Input) (initial : State) (n : Nat)
    (h0 : (inputs n).rstN = false) (h1 : (inputs (n + 1)).rstN = true)
    (h2 : (inputs (n + 2)).rstN = true) :
    (run step inputs initial (n + 3)).rstQ = true := by
  rw [show n + 3 = (n + 2) + 1 from rfl, run_succ,
      show n + 2 = (n + 1) + 1 from rfl, run_succ,
      show n + 1 = n + 1 from rfl, run_succ,
      step_low_of _ _ h0, step_high_of _ _ h1, step_high_of _ _ h2]

/-- `rst_q` is `rst_m` delayed by one released edge. -/
theorem rstq_shift (inputs : Nat → Input) (initial : State) (n : Nat)
    (h : (inputs n).rstN = true) :
    (run step inputs initial (n + 1)).rstQ = (run step inputs initial n).rstM := by
  rw [run_succ, step_high_of _ _ h]

/-- After a released edge the first stage is high. -/
theorem rstm_high (inputs : Nat → Input) (initial : State) (n : Nat)
    (h : (inputs n).rstN = true) : (run step inputs initial (n + 1)).rstM = true := by
  rw [run_succ, step_high_of _ _ h]

end Reset

end Metronome.Debug
