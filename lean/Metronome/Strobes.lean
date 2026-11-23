import Metronome.Moves
import Metronome.Units

/-!
# Chip-top operation strobes: the winner's destination is the unit's control

This module is the independent specification of the chip-top *operation strobe*
network in [project.v](../../src/project.v): the `hits` / `dsteq` / `OPG`
macros (SPEC_V2 §6) that turn the picked write-group winner into the per-unit
write op of each data unit, the data-RAM pointer's port select, the line symbol
operation, the stream control strobes (§6.3, §13.2) and the debug-register write
strobes (§12.4, §13.1).

The RTL side lives in `StrobesEquivalence.lean.in`, which `strobes_check.py`
fills from the elaborated netlist.  Every definition here is stated over the six
move slots and the write-group pick of `Metronome.Moves`; the destination codes
are transcribed from `src/md2_defs.vh` and the group codes from
`src/md2_map.vh` (both generated from `code/md2/machine.json`).

## The strobe rule

`OPG(G, D)` is "the winner of write group `G` writes destination `D`".  The RTL
forms it as `|(HITG(G) & dsteq(c_dst, D))` — the group's priority mask ANDed
with the six destination comparators — instead of decoding the late picked
destination.  `opg` is the same predicate stated on the pick:
`(pickWord (hitsMask …) dst dat).we && dst == D`.  `opg_eq_pick` proves the two
forms agree for every move bus, because `hits` is at most one-hot.

Two consequences are used by the unit cuts:

* a unit's op strobes of one group are mutually exclusive when their
  destination codes differ (`opg_exclusive`), so the counter's `LO`/`HI` and the
  LFSR's `ST`/`B0..B3` can never fire together;
* the accumulator's hit mask `HITG(DG_ACC)` is zero or one-hot
  (`accHit_oneHotOrZero`), which is exactly the `OneHotOrZero` premise of
  `Metronome.Units.Acc.rtlStep_eq_step`.
-/

set_option autoImplicit false
set_option exponentiation.threshold 1024
set_option maxHeartbeats 8000000

namespace Metronome.Strobes

open Metronome.CoreCtl (bitAt slice chain GroupWord makeWord)
open Metronome.Moves (atMostOne bits6 hitAt hitsMask pickWord)

/-! ## Write-group codes (`md2_map.vh`) -/

/-- `DG_ACC`. -/
abbrev dgAcc : BitVec 5 := 3
/-- `DG_SH0`. -/
abbrev dgSh0 : BitVec 5 := 8
/-- `DG_SH1`. -/
abbrev dgSh1 : BitVec 5 := 9
/-- `DG_CNT0`. -/
abbrev dgCnt0 : BitVec 5 := 12
/-- `DG_CNT1`. -/
abbrev dgCnt1 : BitVec 5 := 13
/-- `DG_CNT2`. -/
abbrev dgCnt2 : BitVec 5 := 14
/-- `DG_LF0`. -/
abbrev dgLf0 : BitVec 5 := 15
/-- `DG_LF1`. -/
abbrev dgLf1 : BitVec 5 := 16
/-- `DG_P0`. -/
abbrev dgP0 : BitVec 5 := 17
/-- `DG_S0`. -/
abbrev dgS0 : BitVec 5 := 18
/-- `DG_S1`. -/
abbrev dgS1 : BitVec 5 := 19

/-! ## Destination codes (`md2_defs.vh`) -/

/-- `D_L_SYM`. -/
abbrev dLSym : BitVec 6 := 1
/-- `D_L_DBIT`. -/
abbrev dLDBit : BitVec 6 := 2
/-- `D_L_XOR`. -/
abbrev dLXor : BitVec 6 := 3
/-- `D_SH0_SH`. -/
abbrev dSh0Sh : BitVec 6 := 20
/-- `D_SH1_SH`. -/
abbrev dSh1Sh : BitVec 6 := 21
/-- `D_CNT0_LO`. -/
abbrev dCnt0Lo : BitVec 6 := 24
/-- `D_CNT0_HI`. -/
abbrev dCnt0Hi : BitVec 6 := 27
/-- `D_CNT1_LO`. -/
abbrev dCnt1Lo : BitVec 6 := 25
/-- `D_CNT1_HI`. -/
abbrev dCnt1Hi : BitVec 6 := 28
/-- `D_CNT2_LO`. -/
abbrev dCnt2Lo : BitVec 6 := 26
/-- `D_CNT2_HI`. -/
abbrev dCnt2Hi : BitVec 6 := 29
/-- `D_CNT0_DEC` (the port-code fallback, no `OPG` strobe). -/
abbrev dCnt0Dec : BitVec 6 := 30
/-- `D_CNT1_DEC`. -/
abbrev dCnt1Dec : BitVec 6 := 31
/-- `D_CNT2_DEC`. -/
abbrev dCnt2Dec : BitVec 6 := 32
/-- `D_LF0_ST`. -/
abbrev dLf0St : BitVec 6 := 33
/-- `D_LF1_ST`. -/
abbrev dLf1St : BitVec 6 := 34
/-- `D_LF0_B0`. -/
abbrev dLf0B0 : BitVec 6 := 35
/-- `D_LF0_B1`. -/
abbrev dLf0B1 : BitVec 6 := 36
/-- `D_LF0_B2`. -/
abbrev dLf0B2 : BitVec 6 := 37
/-- `D_LF0_B3` (the port-code fallback, no `OPG` strobe). -/
abbrev dLf0B3 : BitVec 6 := 38
/-- `D_LF1_B0`. -/
abbrev dLf1B0 : BitVec 6 := 39
/-- `D_LF1_B1`. -/
abbrev dLf1B1 : BitVec 6 := 40
/-- `D_LF1_B2`. -/
abbrev dLf1B2 : BitVec 6 := 41
/-- `D_LF1_B3`. -/
abbrev dLf1B3 : BitVec 6 := 42
/-- `D_P0_AL`. -/
abbrev dP0Al : BitVec 6 := 43
/-- `D_P0_AH`. -/
abbrev dP0Ah : BitVec 6 := 44
/-- `D_P0_W`. -/
abbrev dP0W : BitVec 6 := 45
/-- `D_P0_R`. -/
abbrev dP0R : BitVec 6 := 46
/-- `D_S0_ADV`. -/
abbrev dS0Adv : BitVec 6 := 47
/-- `D_S1_ADV`. -/
abbrev dS1Adv : BitVec 6 := 48
/-- `D_S0_RX`. -/
abbrev dS0Rx : BitVec 6 := 49
/-- `D_S1_RX`. -/
abbrev dS1Rx : BitVec 6 := 50
/-- `D_S0_CTL`. -/
abbrev dS0Ctl : BitVec 6 := 51
/-- `D_S1_CTL`. -/
abbrev dS1Ctl : BitVec 6 := 52

/-! ## The destination comparator mask and the strobe predicate -/

/-- `dsteq(c_dst, D)`: move `q`'s destination slice equals `D`, as a six-bit
mask (bit `q` at position `q`). -/
def dsteqMask (hit : BitVec 6) (dst : BitVec 36) (D : BitVec 6) : Bool :=
  (bitAt hit 0 && (slice dst 0 6 == D)) || (bitAt hit 1 && (slice dst 6 6 == D)) ||
  (bitAt hit 2 && (slice dst 12 6 == D)) || (bitAt hit 3 && (slice dst 18 6 == D)) ||
  (bitAt hit 4 && (slice dst 24 6 == D)) || (bitAt hit 5 && (slice dst 30 6 == D))

/-- `OPG(G, D)`: some winner of write group `G` has destination `D`.  Because
`hits` is at most one-hot this is "the group's winner writes `D`". -/
def opg (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) (G : BitVec 5)
    (D : BitVec 6) : Bool := dsteqMask (hitsMask en grp G) dst D

/-- The group mask has at most one bit set: `hits` is a prefix mask over the six
slots (`v[q] & ~|(v & ((1<<q)-1))`). -/
theorem hitsMask_atMostOne (en : BitVec 6) (grp : BitVec 30) (G : BitVec 5) :
    atMostOne (hitsMask en grp G) = true := by
  simp only [atMostOne, hitsMask, bits6, hitAt, bitAt]
  bv_decide

/-- For a one-hot-or-zero mask, "some set bit's destination is `D`" is "the
picked word's destination is `D`". -/
theorem dsteqMask_pick (hit : BitVec 6) (dst : BitVec 36) (dat : BitVec 48)
    (D : BitVec 6) (h : atMostOne hit = true) :
    dsteqMask hit dst D =
      ((pickWord hit dst dat).we && ((pickWord hit dst dat).dst == D)) := by
  revert h
  simp only [atMostOne, dsteqMask, pickWord, chain, bitAt, slice]
  bv_decide

/-- **The strobe rule.**  `opg G D` is exactly "the group's winner has `we` set
and destination `D`", i.e. `(pickWord …).we && (pickWord …).dst == D`, the form
the RTL's `w[14] & (w[13:8] == D)` would have. -/
theorem opg_eq_pick (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36)
    (dat : BitVec 48) (G : BitVec 5) (D : BitVec 6) :
    opg en grp dst G D =
      ((pickWord (hitsMask en grp G) dst dat).we &&
        ((pickWord (hitsMask en grp G) dst dat).dst == D)) := by
  unfold opg
  exact dsteqMask_pick _ _ _ _ (hitsMask_atMostOne en grp G)

/-- A strobe implies that the group has a winner. -/
theorem opg_imp_we {en : BitVec 6} {grp : BitVec 30} {dst : BitVec 36}
    {dat : BitVec 48} {G : BitVec 5} {D : BitVec 6} (h : opg en grp dst G D = true) :
    (pickWord (hitsMask en grp G) dst dat).we = true := by
  have := opg_eq_pick en grp dst dat G D
  rw [this] at h
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- A strobe implies the winner's destination. -/
theorem opg_imp_dst {en : BitVec 6} {grp : BitVec 30} {dst : BitVec 36}
    {dat : BitVec 48} {G : BitVec 5} {D : BitVec 6} (h : opg en grp dst G D = true) :
    (pickWord (hitsMask en grp G) dst dat).dst = D := by
  have := opg_eq_pick en grp dst dat G D
  rw [this] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- **Strobe exclusivity.**  Two different destinations of one group never fire
in one cycle: the group has one winner and one destination. -/
theorem opg_exclusive (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36)
    (G : BitVec 5) (D1 D2 : BitVec 6) (h : D1 ≠ D2) :
    (opg en grp dst G D1 && opg en grp dst G D2) = false := by
  by_cases h1 : opg en grp dst G D1 = true
  · have hw := opg_imp_we (dat := 0) h1
    have hd1 := opg_imp_dst (dat := 0) h1
    have h2 : opg en grp dst G D2 = false := by
      by_cases h2 : opg en grp dst G D2 = true
      · have hd2 := opg_imp_dst (dat := 0) h2
        exact absurd (hd1.symm.trans hd2) h
      · simpa using h2
    rw [h1, h2]
    rfl
  · simp [h1]

/-! ## The accumulator's hit mask -/

/-- A six-bit mask satisfying `atMostOne` is zero or one-hot. -/
theorem atMostOne_cases {hit : BitVec 6} (h : atMostOne hit = true) :
    hit = 0 ∨ hit = 1 ∨ hit = 2 ∨ hit = 4 ∨ hit = 8 ∨ hit = 16 ∨ hit = 32 := by
  revert h
  simp only [atMostOne, bitAt]
  bv_decide

/-- `atMostOne` implies `Metronome.Units.Acc.OneHotOrZero`. -/
theorem atMostOne_oneHotOrZero {hit : BitVec 6} (h : atMostOne hit = true) :
    Metronome.Units.Acc.OneHotOrZero hit := by
  rcases atMostOne_cases h with h0 | h0 | h0 | h0 | h0 | h0 | h0 <;>
    simp [Metronome.Units.Acc.OneHotOrZero, h0]

/-- **The accumulator hit premise, discharged.**  `HITG(DG_ACC)` is zero or
one-hot, the `OneHotOrZero` premise of `Metronome.Units.Acc.rtlStep_eq_step`. -/
theorem accHit_oneHotOrZero (en : BitVec 6) (grp : BitVec 30) :
    Metronome.Units.Acc.OneHotOrZero (hitsMask en grp dgAcc) :=
  atMostOne_oneHotOrZero (hitsMask_atMostOne en grp dgAcc)

/-! ## Per-unit selector encodings

Each unit's port selector is the priority mux of its `OPG` strobes in
`project.v`.  These are the documented maps of SPEC v1 §6.1 as reused by SPEC_V2
§6.1, and they are the maps `units_check.py` proves the elaborated muxes
implement; this module states them over `opg` so the strobes compose with the
unit cuts. -/

/-- The counter port code: `LO` = 0, `HI` = 1, `DEC` = 2. -/
def counterSel (lo hi : Bool) : BitVec 2 := Metronome.Units.Counter.selOf lo hi

/-- The LFSR port code: `ST` = 0, `B0..B3` = 1..4. -/
def lfsrSel (st b0 b1 b2 : Bool) : BitVec 3 := Metronome.Units.Lfsr.selOf st b0 b1 b2

/-- The shifter port code: `LD` = 0, `SH` = 1.  The RTL's `sel` is the `SH`
strobe itself, so `LD` is the fallback. -/
def shifterSel (sh : Bool) : BitVec 1 := if sh then 1 else 0

/-- The pointer port code: `AL` = 0, `AH` = 1, `W` = 2, `R` (and any other
destination, including "no winner") = 3. -/
def p0Sel (dst : BitVec 6) : BitVec 2 :=
  if dst == dP0Al then 0 else if dst == dP0Ah then 1 else if dst == dP0W then 2 else 3

/-- The line symbol operation: `SYM` = 0, `DBIT` = 1, `XOR` (the RTL's
`default:`) = 2. -/
def lineSop (dst : BitVec 6) : BitVec 2 :=
  if dst == dLSym then 0 else if dst == dLDBit then 1 else 2

/-- Slot `m`'s accumulator op code from the destination bus: the ISA map
`ACC.LD..ACC.CMP` = 7..13 → 0..6, everything else the RTL `default:` = CMP. -/
def accSel (dst : BitVec 36) (m : Nat) : BitVec 3 :=
  Metronome.Units.Acc.opCodeOf (slice dst (6 * m) 6)

theorem counterSel_lo (hi : Bool) : counterSel true hi = 0 := rfl

theorem counterSel_hi : counterSel false true = 1 := rfl

theorem counterSel_dec : counterSel false false = 2 := rfl

theorem lfsrSel_st (b0 b1 b2 : Bool) : lfsrSel true b0 b1 b2 = 0 := rfl

theorem lfsrSel_b0 (st b1 b2 : Bool) : lfsrSel st true b1 b2 = if st then 0 else 1 := rfl

theorem lfsrSel_b1 (st b0 b2 : Bool) :
    lfsrSel st b0 true b2 = if st then 0 else if b0 then 1 else 2 := rfl

theorem lfsrSel_b2 (st b0 b1 : Bool) :
    lfsrSel st b0 b1 true = if st then 0 else if b0 then 1 else if b1 then 2 else 3 := rfl

theorem lfsrSel_none (st b0 b1 b2 : Bool) :
    lfsrSel st b0 b1 b2 = if st then 0 else if b0 then 1 else if b1 then 2 else if b2 then 3 else 4 :=
  rfl

theorem shifterSel_ld : shifterSel false = 0 := rfl

theorem shifterSel_sh : shifterSel true = 1 := rfl

theorem p0Sel_al : p0Sel dP0Al = 0 := by simp [p0Sel]

theorem p0Sel_ah : p0Sel dP0Ah = 1 := by simp [p0Sel]

theorem p0Sel_w : p0Sel dP0W = 2 := by simp [p0Sel]

theorem p0Sel_r : p0Sel dP0R = 3 := by simp [p0Sel]

theorem lineSop_sym : lineSop dLSym = 0 := by simp [lineSop]

theorem lineSop_dbit : lineSop dLDBit = 1 := by simp [lineSop]

theorem lineSop_xor : lineSop dLXor = 2 := by simp [lineSop]

/-- The accumulator's per-slot op code, slot by slot. -/
theorem accSel_eq (dst : BitVec 36) (m : Nat) :
    accSel dst m = Metronome.Units.Acc.opCodeOf (slice dst (6 * m) 6) := rfl

/-! ## The groups' selectors from the strobes -/

/-- A counter's `sel` from its two destination strobes: `LO` wins, then `HI`,
then `DEC`.  `opg_exclusive` is why `LO` and `HI` never both fire. -/
theorem counterSel_of_opg (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36)
    (G : BitVec 5) (Dlo Dhi : BitVec 6) :
    counterSel (opg en grp dst G Dlo) (opg en grp dst G Dhi) =
      (if opg en grp dst G Dlo then (0 : BitVec 2)
       else if opg en grp dst G Dhi then 1 else 2) := rfl

/-- An LFSR's `sel` from its four destination strobes. -/
theorem lfsrSel_of_opg (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36)
    (G : BitVec 5) (Dst Db0 Db1 Db2 : BitVec 6) :
    lfsrSel (opg en grp dst G Dst) (opg en grp dst G Db0)
        (opg en grp dst G Db1) (opg en grp dst G Db2) =
      (if opg en grp dst G Dst then (0 : BitVec 3)
       else if opg en grp dst G Db0 then 1
       else if opg en grp dst G Db1 then 2
       else if opg en grp dst G Db2 then 3 else 4) := rfl

/-- The two counter op strobes never fire together. -/
theorem counter_ops_exclusive (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36)
    (G : BitVec 5) (Dlo Dhi : BitVec 6) (h : Dlo ≠ Dhi) :
    (opg en grp dst G Dlo && opg en grp dst G Dhi) = false :=
  opg_exclusive en grp dst G Dlo Dhi h

/-- Any two of an LFSR's four op strobes with different destinations are
exclusive. -/
theorem lfsr_ops_exclusive (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36)
    (G : BitVec 5) (D1 D2 : BitVec 6) (h : D1 ≠ D2) :
    (opg en grp dst G D1 && opg en grp dst G D2) = false :=
  opg_exclusive en grp dst G D1 D2 h

/-! ## The packed group word

The stream control reads the winner's data byte from the picked word `w`; these
two round-trip facts let the strobe statement be phrased on the pick. -/

theorem pack_dst (w : GroupWord) : slice (GroupWord.pack w) 8 6 = w.dst := by
  obtain ⟨we, dst, dat⟩ := w
  simp only [GroupWord.pack, makeWord, slice]
  bv_decide

/-- `slice (pack w) 0 8 = w.data`: the packed word's low byte is the data. -/
theorem pack_data (w : GroupWord) : slice (GroupWord.pack w) 0 8 = w.data := by
  obtain ⟨we, dst, dat⟩ := w
  simp only [GroupWord.pack, makeWord, slice]
  bv_decide

theorem pack_data_0 (w : GroupWord) : bitAt (GroupWord.pack w) 0 = bitAt w.data 0 := by
  obtain ⟨we, dst, dat⟩ := w
  simp only [GroupWord.pack, makeWord, bitAt]
  bv_decide

theorem pack_data_1 (w : GroupWord) : bitAt (GroupWord.pack w) 1 = bitAt w.data 1 := by
  obtain ⟨we, dst, dat⟩ := w
  simp only [GroupWord.pack, makeWord, bitAt]
  bv_decide

/-! ## Stream control (SPEC_V2 §6.3, §13.2)

A stream's `CTL` byte is written by a move to `Sk.CTL` and by a host write of
the stream's `SRT.CTL` byte; §6.3 says "requests from both in one cycle
combine".  The move's bits are the winning word's data bits 0 (rewind), 1
(flush) and the host's bits 0/1/7 (rewind / flush / clear `STARVED`). -/

/-- `cap_en = cen & ~replay`: §12.4's capture enable, with §13.2's replay
priority. -/
def capEn (cen replay : Bool) : Bool := cen && !replay

/-- Which stream `CTL` byte address this is; `SRT_SH = 2` and `HS_SRT - 1 = 3`
from `md2_map.vh`. -/
def hostCtl (wSrt : Bool) (a : BitVec 16) (k : Nat) : Bool :=
  wSrt && ((BitVec.ushiftRight a 2) == (BitVec.ofNat 16 k)) &&
    (((BitVec.setWidth 32 a) &&& 3) == (2 : BitVec 32))

/-- The three stream control strobes of one cycle. -/
structure StreamCtl where
  /-- `rewind`: move `Sk.CTL` bit 0 or host `SRT.CTL` bit 0. -/
  rewind : Bool
  /-- `flush`: move `Sk.CTL` bit 1 or host `SRT.CTL` bit 1. -/
  flush : Bool
  /-- `clr_starved`: host `SRT.CTL` bit 7. -/
  clrStarved : Bool

/-- The control strobes from the winning word's data and the host write. -/
def streamCtlOf (data : BitVec 8) (mctl : Bool) (hctl : Bool) (hd : BitVec 8) : StreamCtl where
  rewind := (mctl && bitAt data 0) || (hctl && bitAt hd 0)
  flush := (mctl && bitAt data 1) || (hctl && bitAt hd 1)
  clrStarved := hctl && bitAt hd 7

/-- The same strobes from the pick: the move term is the group winner's `CTL`
destination and the winner's data bits. -/
theorem streamCtlOf_opg (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36)
    (dat : BitVec 48) (G : BitVec 5) (Dctl : BitVec 6) (hctl : Bool) (hd : BitVec 8) :
    streamCtlOf (pickWord (hitsMask en grp G) dst dat).data
        (opg en grp dst G Dctl) hctl hd =
      streamCtlOf (pickWord (hitsMask en grp G) dst dat).data
        ((pickWord (hitsMask en grp G) dst dat).we &&
          ((pickWord (hitsMask en grp G) dst dat).dst == Dctl)) hctl hd := by
  rw [opg_eq_pick]

/-! ## Debug write strobes (SPEC_V2 §12.4, §13.1)

The `DBG` register bytes are written by the host (`w_dbg` at the byte's offset)
and by a drained core configuration write (`cw_drain` at a `DBG` window offset).
The five bytes with a write strobe are `ECTL` (2), `EMASK` (8, 9) and `RLV`
(18, 19); `DBG`/`MCTL` have their own strobes in the core-control cut. -/

/-- `HA_DBG_BASE`. -/
abbrev haDbgBase : BitVec 16 := 9312
/-- `HO_DBG_ECTL`. -/
abbrev hoDbgEctl : Nat := 2
/-- `HO_DBG_EMASK`. -/
abbrev hoDbgEmask : Nat := 8
/-- `HO_DBG_EMASK + 1`. -/
abbrev hoDbgEmaskPlus1 : Nat := 9
/-- `HO_DBG_RLV`. -/
abbrev hoDbgRlv : Nat := 18
/-- `HO_DBG_RLV + 1`. -/
abbrev hoDbgRlvPlus1 : Nat := 19

/-- `cw_dbg_off`: the queued configuration address as a `DBG` window offset, in
the RTL's 32-bit arithmetic. -/
def cwDbgOff (addr : BitVec 16) : BitVec 32 :=
  (BitVec.setWidth 32 addr) - (BitVec.setWidth 32 haDbgBase)

/-- A host write of `DBG` byte `D`. -/
def hostDbg (wDbg : Bool) (a : BitVec 16) (D : Nat) : Bool :=
  wDbg && ((BitVec.setWidth 32 a) == (BitVec.ofNat 32 D))

/-- A `DBG` byte's write strobe: host write OR core drain at that offset. -/
def dbgByteWrite (wDbg : Bool) (a : BitVec 16) (drain : Bool) (addr : BitVec 16)
    (D : Nat) : Bool :=
  hostDbg wDbg a D || (drain && (cwDbgOff addr == (BitVec.ofNat 32 D)))

theorem dbg_host_write (wDbg : Bool) (a : BitVec 16) (drain : Bool) (addr : BitVec 16)
    (D : Nat) :
    dbgByteWrite wDbg a drain addr D = (hostDbg wDbg a D || (drain && cwDbgOff addr ==
      BitVec.ofNat 32 D)) := rfl

/-- A host write of `DBG.ECTL` and a core drain to `DBG.ECTL` both set the
`ECTL` strobe, so "host write wins" is a decision made downstream by the
converter's write data, not by the strobe. -/
theorem dbg_ectl_both (a addr : BitVec 16) :
    dbgByteWrite true a true addr hoDbgEctl =
      (hostDbg true a hoDbgEctl || (cwDbgOff addr == BitVec.ofNat 32 hoDbgEctl)) := rfl

/-- The five `DBG` write offsets are distinct, so their strobes never alias. -/
theorem dbg_offsets_distinct :
    hoDbgEctl ≠ hoDbgEmask ∧ hoDbgEctl ≠ hoDbgEmask + 1 ∧ hoDbgEctl ≠ hoDbgRlv ∧
      hoDbgEctl ≠ hoDbgRlv + 1 ∧ hoDbgEmask ≠ hoDbgEmask + 1 ∧ hoDbgEmask ≠ hoDbgRlv ∧
      hoDbgEmask ≠ hoDbgRlv + 1 ∧ hoDbgEmask + 1 ≠ hoDbgRlv ∧
      hoDbgEmask + 1 ≠ hoDbgRlv + 1 ∧ hoDbgRlv ≠ hoDbgRlv + 1 := by
  decide

end Metronome.Strobes
