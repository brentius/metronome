import Metronome.Debug
import Metronome.Machine
import Std.Tactic.BVDecide

/-!
# Bridge: the chip-top debug cut (`Metronome.Debug`) and the machine debug block

`Metronome/Debug.lean` is the independent specification of the chip-top debug logic
(pin level/edge vectors with the replay mask, the execution digest, the edge
capture/replay registers, the program-memory port muxing and the reset
synchroniser) that `debug_check.py` proves the elaborated RTL equal to.
`Metronome/Machine/**` is the whole-chip executable machine.

## What is bridged here

* The §2/§13.2 pin level and previous-level vectors: the cut's `level`/`previous`
  `Nat` values are the machine's `pinView` substitution (`lvl`, `prev`).
* The §2 per-bit `RISE`/`FALL` (`rise_bit`/`fall_bit`) and the §12.4 edge event
  (`cev_bridge` against `Machine.captureEvent`).
* The §12.2 execution digest: `MISR`/`MEN` against `Machine.misrNext` (`misr_bridge`).
* The §13.2 level substitution: the cut's `replayLevels` value is the machine's
  `dbgNext` `RLV` substitution, and the replay `apply`/`late` flags are
  `Machine.replayApply`'s pair (`apply_bridge`, `late_bridge`).
* The §12.4/§13.1 capture/replay register transition (`ECTL`, `EMASK`, `RLV`, `DC`)
  against `Machine.dbgNext`, through the explicit `Option`↔strobe abstraction (`Port`,
  `pickByte`, `byteWOf`, `writeBytes`, `byteW2_bridge`) and the assembled
  `dbg_step_bridge`.
* The §1 reset synchroniser: the cut's `Reset.step` is the machine's `resetStep`
  flop pair `r1`/`rq`.
* The §5/§9/9a.8 program-memory write strobes, byte lane and port select.
* One disagreement with a witness: `RLV`'s previous level in a frozen cycle
  (`dbg_step_bridge` states that field under `i.frz = false`).
  (The replay `late` flag agrees: both use §13.2's `>=`/`>`.)

## Gaps

Two host-selected (or two core-selected) byte strobes of one 13-bit register in the
same cycle are not machine-representable (`hSH`/`hSC`).  Program-memory *contents*
and `captureEvent`'s record are outside this file, as is `dbgNext`'s
`FREEZE`/`FRZD` bookkeeping (the cut's `Ctrl` has no `FREEZE` register).
See `BRIDGE_GLUE_DEBUG_NOTES.md` §2.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Metronome.Bridge.Debug

open Metronome
open Metronome.Machine Metronome.Machine.Util

/-- The cut's bit extractor is the machine's `nbit` of the value. -/
theorem bitAt_eq_nbit {w : Nat} (x : BitVec w) (i : Nat) :
    Metronome.Debug.bitAt x i = nbit x.toNat i := by
  rw [Bool.eq_iff_iff]
  simp only [Metronome.Debug.bitAt, nbit, BitVec.getLsbD, bne_iff_ne, ne_eq,
    BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod, Nat.reducePow,
    BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  rw [show BitVec.ushiftRight x i = (x >>> i) from rfl, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [show ((0 : BitVec 1)).toNat = 0 from by decide]
  rcases Nat.mod_two_eq_zero_or_one (x.toNat / 2 ^ i) with h | h <;> simp [h]

/-- The cut's slice has the machine's `nbits` value. -/
theorem slice_toNat {w : Nat} (x : BitVec w) (off n : Nat) :
    (Metronome.Debug.slice x off n).toNat = nbits x.toNat off n := by
  unfold Metronome.Debug.slice nbits
  rw [BitVec.truncate_eq_setWidth]
  simp only [BitVec.ushiftRight_eq, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]

/-! ## §2 pin levels and §13.2 replay substitution -/

/-- The cut's replay mask has the machine's `EMASK & {13{RPL}}` value. -/
theorem mask_toNat (emask : BitVec 13) (r : Bool) :
    (Metronome.Debug.Pins.mask emask r).toNat = (if r then emask.toNat else 0) := by
  unfold Metronome.Debug.Pins.mask Metronome.Debug.Pins.maskOf
  rw [BitVec.toNat_and]
  cases r
  · simp
  · simp [Nat.and_two_pow_sub_one_of_lt_two_pow emask.isLt]

/-- The cut's level vector is the machine's `pinView` level, as a `Nat`. -/
theorem level_toNat (s2 rlv emask : BitVec 13) (r : Bool) :
    (Metronome.Debug.Pins.level s2 rlv emask r).toNat =
      (s2.toNat &&& (2 ^ 13 - 1 - (if r then emask.toNat else 0))) |||
        (rlv.toNat &&& (if r then emask.toNat else 0)) := by
  unfold Metronome.Debug.Pins.level
  rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_not, mask_toNat]

/-- The cut's previous-level vector is the machine's `pinView` previous level. -/
theorem previous_toNat (sp rlvPrev emask : BitVec 13) (r : Bool) :
    (Metronome.Debug.Pins.previous sp rlvPrev emask r).toNat =
      (sp.toNat &&& (2 ^ 13 - 1 - (if r then emask.toNat else 0))) |||
        (rlvPrev.toNat &&& (if r then emask.toNat else 0)) := by
  unfold Metronome.Debug.Pins.previous
  rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_not, mask_toNat]

/-- The cut's `lvl` is `{3'd0, level}`, so its value is the level. -/
theorem lvl_toNat (level : BitVec 13) :
    (Metronome.Debug.Pins.lvl level).toNat = level.toNat := by
  unfold Metronome.Debug.Pins.lvl
  rw [BitVec.toNat_append]
  simp [Nat.shiftLeft_eq]
/-! ## §13.2 replay level substitution -/

/-- The cut's `replayLevels` value is the machine's `RLV'` substitution `Nat`. -/
theorem replayLevels_toNat (rlv emask : BitVec 13) (apply : Bool) (word : BitVec 32) :
    (Metronome.Debug.Ctrl.replayLevels rlv emask apply word).toNat =
      if apply then
        (rlv.toNat &&& (2 ^ 13 - 1 - emask.toNat)) ||| (nbits word.toNat 0 13 &&& emask.toNat)
      else rlv.toNat := by
  unfold Metronome.Debug.Ctrl.replayLevels
  by_cases h : apply
  · rw [if_pos h, if_pos h]
    rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_not, slice_toNat]
  · rw [if_neg h, if_neg h]

/-! ## The replay `late` flag

`Machine.replayApply` (Machine/Stream.lean) returns
`ap = !frozen && RPL && WV && DC + 1 ≥ WB.DC` and `late = ap && DC + 1 > WB.DC`,
which is SPEC_V2 §13.2.  The cut's `late` is the same comparison.  (An earlier
note here claimed the machine used `=`; that was a misreading and is withdrawn,
2026-11-21.)  The witness below exercises the cut side only. -/

/-- The cut's `late` is `DC + 1 > WB.DC` and is true for `DC = 5`, `WB.DC = 3`. -/
theorem cut_late_witness :
    Metronome.Debug.Ctrl.late true false true 5 (3 * 8192) = true := by
  unfold Metronome.Debug.Ctrl.late Metronome.Debug.Ctrl.tick Metronome.Debug.Ctrl.interval
  decide

/-! ## §1 reset synchroniser -/

/-- The cut's reset flop pair is the machine's `r1`/`rq`. -/
theorem reset_bridge (s : Metronome.Debug.Reset.State) (i : Metronome.Debug.Reset.Input)
    (r1 rq : Bool) (h1 : s.rstM = r1) (_h2 : s.rstQ = rq) :
    (Metronome.Debug.Reset.step s i).rstM = i.rstN ∧
    (Metronome.Debug.Reset.step s i).rstQ = (r1 && i.rstN) := by
  unfold Metronome.Debug.Reset.step Metronome.Debug.Reset.resetState
  by_cases h : i.rstN = true
  · simp [h, h1]
  · simp [h]

/-! ## §5 / §9 / 9a.8 program-memory port muxing -/

/-- At most one core's program write strobe is asserted. -/
theorem we_exclusive (hWr inPrg : Bool) (a : BitVec 16) :
    (Metronome.Debug.Pmem.we0 hWr inPrg a && Metronome.Debug.Pmem.we1 hWr inPrg a) = false := by
  unfold Metronome.Debug.Pmem.we0 Metronome.Debug.Pmem.we1
  cases hWr <;> cases inPrg <;> cases Metronome.Debug.bitAt a 11 <;> simp

/-- A host write takes the memory port: the address presented is the host's word address. -/
theorem port_host (host fetch : BitVec 8) :
    Metronome.Debug.Pmem.portAddr true host fetch = host := rfl

/-- Without a host write the fetch address is presented. -/
theorem port_fetch (host fetch : BitVec 8) :
    Metronome.Debug.Pmem.portAddr false host fetch = fetch := rfl

/-- The lane is the low three address bits: `be = 1 <<< a[2:0]`, so its value is a power
of two selected by those bits. -/
theorem be_ne_zero (a : BitVec 16) : Metronome.Debug.Pmem.be a != 0 := by
  unfold Metronome.Debug.Pmem.be
  rw [bne_iff_ne, ne_eq, BitVec.toNat_eq]
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have h : 2 ^ (Metronome.Debug.slice a 0 3).toNat < 2 ^ 8 := by
    apply Nat.pow_lt_pow_right (by decide)
    have := (Metronome.Debug.slice a 0 3).isLt
    omega
  rw [Nat.mod_eq_of_lt h]
  have := Nat.two_pow_pos (Metronome.Debug.slice a 0 3).toNat
  omega

/-! ## A disagreement: `RLV`'s previous level in a frozen cycle

SPEC_V2 §12.3 holds the registers in a frozen cycle, so the cut's `RLVP` holds
(`rlvPrevNext = frz ? rlvPrev : rlv`).  The machine's `dbgNext` sets `rlvp := d.rlv`
unconditionally.  A frozen cycle with an `RLV` byte write makes the two differ; the
witness fixes the numbers.  The agreeing fragment is `rlvp_agree`. -/

/-- The cut holds `RLVP` in a frozen cycle. -/
theorem rlvp_frozen_cut (s : Metronome.Debug.Ctrl.State) (i : Metronome.Debug.Ctrl.Input)
    (hf : i.frz = true) :
    Metronome.Debug.Ctrl.rlvPrevNext s i = s.rlvPrev := by
  unfold Metronome.Debug.Ctrl.rlvPrevNext
  simp [hf]

/-- The agreeing fragment: in an unfrozen cycle the cut's `RLVP'` is `RLV`, which is the
machine's `rlvp := RLV`. -/
theorem rlvp_agree (s : Metronome.Debug.Ctrl.State) (i : Metronome.Debug.Ctrl.Input)
    (d : DbgSt) (hf : i.frz = false) (hr : s.rlv = d.rlv) :
    Metronome.Debug.Ctrl.rlvPrevNext s i = d.rlv := by
  unfold Metronome.Debug.Ctrl.rlvPrevNext
  simp [hf, hr]

/-- Witness: with `RLV = 0x0AA` and `RLVP = 0x155`, the cut's frozen `RLVP` holds
`0x155`; the machine's `rlvp := RLV` is `0x0AA`. -/
theorem rlvp_frozen_witness :
    Metronome.Debug.Ctrl.rlvPrevNext
        { replay := false, cen := false, emask := 0, rlv := 0x0AA, rlvPrev := 0x155, dc := 0 }
        { resetN := true, frz := true, hEctl := false, dWrEctl := false, hEm0 := false,
          dWrEm0 := false, hEm1 := false, dWrEm1 := false, hRlv0 := true, dWrRlv0 := true,
          hRlv1 := false, dWrRlv1 := false, hWd := 255, cwData := 0, replayValid := 0,
          replayWord := 0, rise := 0, fall := 0 }
      = 0x155 ∧
    ({ replay := false, cen := false, emask := 0, rlv := 0x0AA, rlvPrev := 0x155, dc := 0 } :
      Metronome.Debug.Ctrl.State).rlv = 0x0AA := by
  decide

/-! ## §12.2 the execution digest: `MISR` and `MEN` against `Machine.misrNext`/`dbgNext`

`Metronome.Debug.Digest.misrNext` takes the clear condition as `dWrMctl && hWd[1]`, the
data vector as the cut's `{OEN, OUT}` and `MEN`/`FRZ` from its own state.
`Machine.misrNext` takes the clear as a `Bool` from `nbit (wMctl.getD 0) 1` and the data
vector as a `Nat`; `Machine.dbgNext` supplies both.  The value lemmas below put the two
on the same `Nat`; `misr_bridge`/`men_bridge` then identify the results.  Nothing here
needs a hypothesis beyond the interface equalities (`MEN`, `MISR`, `FRZ`, `OUT`, `OEN`
and the `MCTL` write byte), which is `dbgNext`'s view of the cut's inputs. -/

/-- The digest's data vector value is `OUT + OEN * 2^14` (SPEC_V2 §12.2's bit order). -/
theorem dataVec_toNat (oEe : BitVec 8) (oOut : BitVec 14) :
    (Metronome.Debug.Digest.dataVec oEe oOut).toNat = oOut.toNat + oEe.toNat * 2 ^ 14 := by
  unfold Metronome.Debug.Digest.dataVec
  rw [BitVec.toNat_append, BitVec.toNat_append]
  rw [show (BitVec.toNat (0 : BitVec 10)) = 0 from rfl]
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.zero_mul, Nat.zero_or]
  have h : oEe.toNat * 2 ^ 14 + oOut.toNat = oEe.toNat * 2 ^ 14 ||| oOut.toNat := by
    rw [← Nat.shiftLeft_eq]
    exact Nat.shiftLeft_add_eq_or_of_lt (i := 14) oOut.isLt oEe.toNat
  rw [← h]
  omega

/-- `2^14` is the machine's `N_OUT_PINS` shift for the data vector. -/
theorem nOutPins_eq : Tables.N_OUT_PINS = 14 := rfl

/-- The cut's `shiftLeft` value: `(M << 1)` on 32 bits is `(M * 2) mod 2^32`. -/
theorem shiftLeft_one_toNat (x : BitVec 32) :
    (BitVec.shiftLeft x 1).toNat = x.toNat * 2 % 2 ^ 32 := by
  rw [show BitVec.shiftLeft x 1 = x <<< 1 from rfl, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- The cut's `M'` as a `Nat`: SPEC_V2 §12.2's clear, shift, conditional xor and data xor. -/
theorem cut_misr_toNat (men : Bool) (m : BitVec 32) (i : Metronome.Debug.Digest.Input) :
    (Metronome.Debug.Digest.misrNext men m i).toNat =
      (if i.dWrMctl && Metronome.Debug.bitAt i.hWd 1 then 0
       else if men && !i.frz then
         ((m.toNat * 2) % 2 ^ 32) ^^^ (if nbit m.toNat 31 then 0x04C11DB7 else 0)
           ^^^ (i.oOut.toNat + i.oEe.toNat * 2 ^ 14)
       else m.toNat) := by
  unfold Metronome.Debug.Digest.misrNext Metronome.Debug.Digest.poly
  have hp : ((if Metronome.Debug.bitAt m 31 then (0x04C11DB7 : BitVec 32) else 0)).toNat =
      (if Metronome.Debug.bitAt m 31 then (0x04C11DB7 : Nat) else 0) := by
    by_cases h : Metronome.Debug.bitAt m 31 <;> simp [h]
  by_cases hc : i.dWrMctl && Metronome.Debug.bitAt i.hWd 1
  · simp only [hc, if_true]
    rfl
  · simp only [hc, Bool.false_eq_true, if_false]
    by_cases hm : men && !i.frz
    · simp only [hm, if_true]
      rw [BitVec.toNat_xor, BitVec.toNat_xor, hp, dataVec_toNat, bitAt_eq_nbit,
        shiftLeft_one_toNat]
    · simp only [hm, Bool.false_eq_true, if_false]

/-- `bv n x`'s value is `x mod 2^n` (the machine's `Util.bv`). -/
theorem bv_toNat' {n : Nat} (x : Nat) : (bv n x).toNat = x % 2 ^ n := by
  unfold bv
  rw [BitVec.toNat_ofNat]

/-- The machine's `M'` as a `Nat`. -/
theorem machine_misr_toNat (s : Machine.State) (hClr : Bool) :
    (Machine.misrNext s hClr).toNat =
      (if hClr then 0
       else if s.dbg.men && !s.dbg.frz then
         ((s.dbg.misr.toNat * 2) % 2 ^ 32) ^^^
           (if nbit s.dbg.misr.toNat 31 then 0x04C11DB7 else 0)
           ^^^ (s.out.toNat + s.oen.toNat * 2 ^ 14)
       else s.dbg.misr.toNat) := by
  unfold Machine.misrNext
  by_cases hc : hClr
  · simp only [hc, if_true]
    rfl
  · simp only [hc, Bool.false_eq_true, if_false, nOutPins_eq]
    split
    · rename_i h
      rw [bv_toNat']
      have hd : s.out.toNat + s.oen.toNat * 2 ^ 14 < 2 ^ 32 := by
        have := s.oen.isLt
        have := s.out.isLt
        omega
      have h1 : (s.dbg.misr.toNat * 2) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
      have h2 : (if nbit s.dbg.misr.toNat 31 then (0x04C11DB7 : Nat) else 0) < 2 ^ 32 := by
        by_cases h : nbit s.dbg.misr.toNat 31 <;> simp [h]
      have hx : ((s.dbg.misr.toNat * 2) % 2 ^ 32 ^^^
          (if nbit s.dbg.misr.toNat 31 then (0x04C11DB7 : Nat) else 0) ^^^
          (s.out.toNat + s.oen.toNat * 2 ^ 14)) < 2 ^ 32 :=
        Nat.xor_lt_two_pow (Nat.xor_lt_two_pow h1 h2) hd
      rw [Nat.mod_eq_of_lt hx]
    · rfl

/-- `dbgNext`'s `M` is `misrNext` with the `MCTL` clear bit (lifted `rfl` view). -/
theorem dbgNext_misr (ms : Machine.State) (hw cw : Option HostWr) (cev apply frozen : Bool) :
    (Machine.dbgNext ms hw cw cev apply frozen).misr =
      Machine.misrNext ms (nbit ((hwByte hw "DBG" 0 "MCTL").getD 0) 1) := rfl

/-- `dbgNext`'s `MEN` is the `MCTL` byte's bit 0 (lifted `rfl` view). -/
theorem dbgNext_men (ms : Machine.State) (hw cw : Option HostWr) (cev apply frozen : Bool) :
    (Machine.dbgNext ms hw cw cev apply frozen).men =
      (match hwByte hw "DBG" 0 "MCTL" with
       | some v => nbit v 0
       | none => ms.dbg.men) := rfl

/-- The machine's `MCTL` clear bit is the cut's `dWrMctl && hWd[1]` (host `MCTL` write). -/
theorem mctl_clear (i : Metronome.Debug.Digest.Input) (hw : Option HostWr)
    (hmctl : hwByte hw "DBG" 0 "MCTL" =
      (if i.dWrMctl then some i.hWd.toNat else none)) :
    nbit ((hwByte hw "DBG" 0 "MCTL").getD 0) 1 = (i.dWrMctl && Metronome.Debug.bitAt i.hWd 1) := by
  rw [hmctl]
  by_cases h : i.dWrMctl <;> simp [h, bitAt_eq_nbit, nbit]

/-- §12.2: `M'` is the same in the cut and the machine. -/
theorem misr_bridge (men : Bool) (m : BitVec 32) (i : Metronome.Debug.Digest.Input)
    (ms : Machine.State) (hw : Option HostWr)
    (hmen : ms.dbg.men = men) (hmisr : ms.dbg.misr = m) (hfrz : ms.dbg.frz = i.frz)
    (hout : ms.out = i.oOut) (hoen : ms.oen = i.oEe)
    (hmctl : hwByte hw "DBG" 0 "MCTL" =
      (if i.dWrMctl then some i.hWd.toNat else none)) :
    (Machine.dbgNext ms hw none true true false).misr =
      Metronome.Debug.Digest.misrNext men m i := by
  rw [dbgNext_misr, mctl_clear i hw hmctl]
  apply BitVec.toNat_eq.mpr
  rw [machine_misr_toNat, hmen, hmisr, hfrz, hout, hoen, cut_misr_toNat]

/-- §12.2: `MEN'` is the same in the cut and the machine (`MCTL` bit 0, held otherwise). -/
theorem men_bridge (men : Bool) (i : Metronome.Debug.Digest.Input) (ms : Machine.State)
    (hw : Option HostWr) (hmen : ms.dbg.men = men)
    (hmctl : hwByte hw "DBG" 0 "MCTL" =
      (if i.dWrMctl then some i.hWd.toNat else none)) :
    (Machine.dbgNext ms hw none true true false).men =
      Metronome.Debug.Digest.menNext men i := by
  rw [dbgNext_men, hmctl, hmen]
  unfold Metronome.Debug.Digest.menNext
  by_cases h : i.dWrMctl <;> simp [h, bitAt_eq_nbit]

/-! ## §9 / §13.1 the `Option`↔strobe abstraction for the capture/replay registers

`Machine.dbgNext` receives the host link's write and the drained core write as
`Option HostWr` values (`hwByte`/`hwAt` in `Machine/Host.lean`); the cut
(`Metronome.Debug.Ctrl.Input`) carries, per register byte, a *combined* strobe
(`dWr*`, host or drained core) plus a *host-source select* (`h*`), the host byte
`h_wd` and the drained core byte `cw_pending_data`.  A `Port` is exactly the cut's
three-way view of one byte write; `Port.hostAt`/`Port.coreAt` are the machine's two
`hwAt` options that the cut's three-way view denotes.  SPEC_V2 §13.1 fixes the
combination: the host wins the byte it targets, the core drain acts otherwise.

The abstraction is deliberately per byte: the host link writes one register byte per
cycle (§9) and the core drain carries one (§13.1), so the machine's two `Option`s
cannot express two host-selected (or two core-selected) byte strobes at once.  The
13-bit registers made of two bytes (`EMASK`, `RLV`) therefore carry that
representability side condition (`hSH`/`hSC` below). -/

/-- One register byte as the cut carries it. -/
structure Port where
  /-- The combined host-or-drain write strobe. -/
  strobe : Bool
  /-- Whether the host wins this byte (§13.1). -/
  host : Bool
  /-- The host write byte `h_wd`. -/
  hWd : BitVec 8
  /-- The drained core write byte `cw_pending_data`. -/
  cwData : BitVec 8
  deriving DecidableEq, Repr

/-- The byte the port writes: `none` without a strobe, the host byte when the host wins
the byte, the drained core byte otherwise (SPEC_V2 §13.1). -/
def Port.ok (p : Port) : Option Nat :=
  if p.strobe then some (if p.host then p.hWd.toNat else p.cwData.toNat) else none

/-- The port as the machine's host-write option at byte index `k` of its register. -/
def Port.hostAt (p : Port) (k : Nat) : Option (Nat × Nat) :=
  if p.strobe && p.host then some (k, p.hWd.toNat) else none

/-- The port as the machine's drained-core-write option at byte index `k`. -/
def Port.coreAt (p : Port) (k : Nat) : Option (Nat × Nat) :=
  if p.strobe && !p.host then some (k, p.cwData.toNat) else none

/-- The machine's host-then-core winning byte of one register (SPEC_V2 §13.1),
`dbgNext`'s local `pick`, lifted for reuse. -/
def pickByte (hw cw : Option HostWr) (r : String) : Option Nat :=
  match hwByte hw "DBG" 0 r with
  | some v => some v
  | none => hwByte cw "DBG" 0 r

/-- The machine's per-byte register write (`dbgNext`'s local `byteW`), lifted for use. -/
def byteWOf (hw cw : Option HostWr) (x : Nat) (r : String) : Nat :=
  let x1 := match hwAt cw "DBG" 0 r with
    | some (k, v) => (setByte (bv 16 x) k v).toNat
    | none => x
  match hwAt hw "DBG" 0 r with
    | some (k, v) => (setByte (bv 16 x1) k v).toNat
    | none => x1

/-- `dbgNext`'s `CEN` (lifted `rfl` view of its local `pick "ECTL"`). -/
theorem dbgNext_cen (ms : Machine.State) (hw cw : Option HostWr) (cev apply frozen : Bool) :
    (Machine.dbgNext ms hw cw cev apply frozen).cen =
      (match pickByte hw cw "ECTL" with | some v => nbit v 0 | none => ms.dbg.cen) := rfl

/-- `dbgNext`'s `RPL` (lifted `rfl` view). -/
theorem dbgNext_rpl (ms : Machine.State) (hw cw : Option HostWr) (cev apply frozen : Bool) :
    (Machine.dbgNext ms hw cw cev apply frozen).rpl =
      (match pickByte hw cw "ECTL" with | some v => nbit v 1 | none => ms.dbg.rpl) := rfl

/-- `dbgNext`'s `EMASK` (lifted `rfl` view). -/
theorem dbgNext_emask (ms : Machine.State) (hw cw : Option HostWr) (cev apply frozen : Bool) :
    (Machine.dbgNext ms hw cw cev apply frozen).emask =
      bv 13 (byteWOf hw cw ms.dbg.emask.toNat "EMASK") := rfl

/-- `dbgNext`'s `RLV` (lifted `rfl` view), with `rlv1` from SPEC_V2 §13.2. -/
theorem dbgNext_rlv (ms : Machine.State) (hw cw : Option HostWr) (cev apply frozen : Bool) :
    (Machine.dbgNext ms hw cw cev apply frozen).rlv =
      bv 13 (byteWOf hw cw
        (if apply then (ms.dbg.rlv.toNat &&& (2 ^ 13 - 1 - ms.dbg.emask.toNat)) |||
            ((vget ms.streams 0).wb.toNat &&& ms.dbg.emask.toNat)
         else ms.dbg.rlv.toNat) "RLV") := rfl

/-- `dbgNext`'s `RLVP` (lifted `rfl` view): the machine sets it to the current `RLV`
in an unfrozen cycle and holds it in a frozen one (machine-spec fix 2026-11-22, §12.3). -/
theorem dbgNext_rlvp (ms : Machine.State) (hw cw : Option HostWr) (cev apply frozen : Bool) :
    (Machine.dbgNext ms hw cw cev apply frozen).rlvp =
      (if frozen then ms.dbg.rlvp else ms.dbg.rlv) := rfl

/-- The unfrozen case of `dbgNext_rlvp` (the pre-fix statement, for existing callers). -/
theorem dbgNext_rlvp_unfrozen (ms : Machine.State) (hw cw : Option HostWr) (cev apply : Bool) :
    (Machine.dbgNext ms hw cw cev apply false).rlvp = ms.dbg.rlv := rfl

/-- `dbgNext`'s `DC` (lifted `rfl` view): every `ECTL` write clears, `FRZ` holds, replay
applies or capture-off clears, an edge event sets 1, otherwise it counts and saturates. -/
theorem dbgNext_dc (ms : Machine.State) (hw cw : Option HostWr) (cev apply frozen : Bool) :
    (Machine.dbgNext ms hw cw cev apply frozen).dc =
      bv 19
        (if (pickByte hw cw "ECTL").isSome then 0
         else if frozen then ms.dbg.dc.toNat
         else if ms.dbg.rpl then
           (if apply then 0 else min (ms.dbg.dc.toNat + 1) (2 ^ 19 - 1))
         else if ms.dbg.cen then
           (if cev then 1 else min (ms.dbg.dc.toNat + 1) (2 ^ 19 - 1))
         else 0) := rfl

/-- The cut's one-byte choice against the machine's `Option`: the `n`-th bit of the
winning byte, or the state's bit without a write. -/
theorem port_bit (n : Nat) (strobe host : Bool) (hWd cwData : BitVec 8) (df : Bool) :
    (match (Port.mk strobe host hWd cwData).ok with
     | some v => nbit v n
     | none => df) =
      (if strobe then
        (if host then Metronome.Debug.bitAt hWd n else Metronome.Debug.bitAt cwData n)
       else df) := by
  unfold Port.ok
  cases strobe <;> cases host <;> simp [bitAt_eq_nbit]

/-- §12.4 / §13.2 / §13.1: `ECTL`'s `CEN` and `RPL` are the same in the cut and the
machine: a host write wins the byte, a core drain takes it otherwise, no strobe holds. -/
theorem ectl_bridge (s : Metronome.Debug.Ctrl.State) (ms : Machine.State)
    (i : Metronome.Debug.Ctrl.Input) (hw cw : Option HostWr) (cev apply frozen : Bool)
    (hcen : ms.dbg.cen = s.cen) (hrpl : ms.dbg.rpl = s.replay)
    (h : pickByte hw cw "ECTL" = (Port.mk i.dWrEctl i.hEctl i.hWd i.cwData).ok) :
    (Machine.dbgNext ms hw cw cev apply frozen).cen = Metronome.Debug.Ctrl.cenNext s i ∧
    (Machine.dbgNext ms hw cw cev apply frozen).rpl = Metronome.Debug.Ctrl.replayNext s i := by
  constructor
  · rw [dbgNext_cen, h, hcen, port_bit 0 i.dWrEctl i.hEctl i.hWd i.cwData s.cen]
    unfold Metronome.Debug.Ctrl.cenNext
    by_cases h1 : i.dWrEctl <;> by_cases h2 : i.hEctl <;> simp [h1, h2]
  · rw [dbgNext_rpl, h, hrpl, port_bit 1 i.dWrEctl i.hEctl i.hWd i.cwData s.replay]
    unfold Metronome.Debug.Ctrl.replayNext
    by_cases h1 : i.dWrEctl <;> by_cases h2 : i.hEctl <;> simp [h1, h2]

/-- `a ++ b` for an 8-bit low part has value `a * 256 + b`. -/
theorem append8_toNat {w : Nat} (a : BitVec w) (b : BitVec 8) :
    (a ++ b).toNat = a.toNat * 256 + b.toNat := by
  rw [BitVec.toNat_append]
  have h : a.toNat <<< 8 + b.toNat = a.toNat <<< 8 ||| b.toNat :=
    Nat.shiftLeft_add_eq_or_of_lt (i := 8) b.isLt a.toNat
  rw [← h, Nat.shiftLeft_eq]

/-- `bv n x.toNat` is `x` (the machine's `bv` is the identity on a vector's value). -/
theorem bv_self {n : Nat} (x : BitVec n) : bv n x.toNat = x := by
  apply BitVec.toNat_eq.mpr
  rw [bv_toNat', Nat.mod_eq_of_lt x.isLt]

/-- `bv 13`'s value. -/
theorem bv13_toNat (n : Nat) : (bv 13 n).toNat = n % 2 ^ 13 := bv_toNat' n

/-- The cut's per-byte write on a 13-bit register word: byte 0 is bits 0..7, byte 1 is
bits 8..12 (`EMASK`/`RLV` are 13 bits wide, so byte 1 contributes five bits). -/
def setByte13 (x : BitVec 13) (k : Nat) (v : BitVec 8) : BitVec 13 :=
  if k = 0 then Metronome.Debug.slice x 8 5 ++ v
  else Metronome.Debug.slice v 0 5 ++ Metronome.Debug.slice x 0 8

/-- `setByte13`'s value: the written byte replaces its lane, the other lane holds. -/
theorem setByte13_toNat (x : BitVec 13) (k : Nat) (v : BitVec 8) :
    (setByte13 x k v).toNat =
      (if k = 0 then nbits x.toNat 8 5 * 256 + v.toNat
       else nbits v.toNat 0 5 * 256 + nbits x.toNat 0 8) := by
  unfold setByte13
  by_cases h : k = 0 <;> simp only [h, if_true, if_false]
  · rw [append8_toNat, slice_toNat]
  · rw [append8_toNat, slice_toNat, slice_toNat]

/-- `nbits` at offset 0 is a plain modulus. -/
theorem nbits_zero_pow (x n : Nat) : nbits x 0 n = x % 2 ^ n := by
  unfold nbits
  rw [Nat.shiftRight_zero]

/-- The machine's 16-bit `setByte` at byte 0, before the truncation. -/
theorem setByte16_0_gen (x v : Nat) :
    (setByte (bv 16 x) 0 v).toNat = x % 2 ^ 16 - nbits x 0 8 + v % 256 := by
  unfold setByte bv nbits
  simp only [BitVec.toNat_ofNat, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.shiftRight_zero]
  have h16 : (2 : Nat) ^ 16 = 65536 := by decide
  have h8 : (2 : Nat) ^ 8 = 256 := by decide
  rw [h16, h8]
  have hm : x % 65536 % 256 = x % 256 := by
    rw [show (65536 : Nat) = 256 * 256 from rfl, Nat.mod_mul_right_mod]
  rw [hm, Nat.mod_eq_of_lt (by omega)]

/-- The machine's 16-bit `setByte` at byte 1, before the truncation. -/
theorem setByte16_1_gen (x v : Nat) :
    (setByte (bv 16 x) 1 v).toNat = x % 2 ^ 16 - nbits x 8 8 * 256 + (v % 256) * 256 := by
  unfold setByte bv nbits
  simp only [BitVec.toNat_ofNat, Nat.mul_one, Nat.shiftRight_eq_div_pow]
  have h16 : (2 : Nat) ^ 16 = 65536 := by decide
  have h8 : (2 : Nat) ^ 8 = 256 := by decide
  rw [h16, h8]
  have hd : x % 65536 / 256 % 256 = x / 256 % 256 := by omega
  rw [hd]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- The machine's 16-bit `setByte` at byte 0, truncated to 13 bits, is the cut's `setByte13`. -/
theorem nat_setByte0_13 (x v : Nat) (hx : x < 2 ^ 16) :
    (x - nbits x 0 8 + v % 256) % 2 ^ 13 =
      nbits (x % 2 ^ 13) 8 5 * 256 + v % 256 := by
  have h0 : nbits x 0 8 = x % 256 := by
    unfold nbits
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  have h13 : (2 : Nat) ^ 13 = 8192 := by decide
  have h5 : nbits (x % 2 ^ 13) 8 5 = x / 256 % 32 := by
    unfold nbits
    rw [Nat.shiftRight_eq_div_pow, h13]
    omega
  rw [h0, h13, h5]
  omega

/-- The machine's 16-bit `setByte` at byte 1, truncated to 13 bits. -/
theorem nat_setByte1_13 (x v : Nat) (hx : x < 2 ^ 16) :
    (x - nbits x 8 8 * 256 + (v % 256) * 256) % 2 ^ 13 =
      (v % 256) % 32 * 256 + nbits (x % 2 ^ 13) 0 8 := by
  have h8 : nbits x 8 8 = x / 256 := by
    unfold nbits
    rw [Nat.shiftRight_eq_div_pow]
    rw [show (2 : Nat) ^ 8 = 256 from rfl, Nat.mod_eq_of_lt (by omega)]
  have h13 : (2 : Nat) ^ 13 = 8192 := by decide
  have h0 : nbits (x % 2 ^ 13) 0 8 = x % 256 := by
    unfold nbits
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one, h13]
    omega
  rw [h8, h13, h0]
  omega

/-- The machine's `setByte` at byte 0 or 1 of a 16-bit word, seen as the cut's
`setByte13` on the 13-bit word (the 13-bit truncation absorbs the high bits). -/
theorem bv13_setByte (x : Nat) (k : Nat) (v : BitVec 8) (hk : k < 2) (hx : x < 2 ^ 16) :
    bv 13 ((setByte (bv 16 x) k v.toNat).toNat) = setByte13 (bv 13 x) k v := by
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with h | h
  · subst h
    apply BitVec.toNat_eq.mpr
    rw [bv13_toNat, setByte16_0_gen, Nat.mod_eq_of_lt hx, setByte13_toNat]
    rw [bv13_toNat, if_pos rfl]
    have hv : v.toNat % 256 = v.toNat := Nat.mod_eq_of_lt v.isLt
    rw [← hv, Nat.mod_mod]
    exact nat_setByte0_13 x v.toNat hx
  · subst h
    apply BitVec.toNat_eq.mpr
    rw [bv13_toNat, setByte16_1_gen, Nat.mod_eq_of_lt hx, setByte13_toNat]
    rw [bv13_toNat, if_neg (by decide : ¬ (1 = 0))]
    have hv : nbits v.toNat 0 5 = (v.toNat % 256) % 32 := by
      rw [nbits_zero_pow, Nat.mod_eq_of_lt v.isLt]
    rw [hv]
    exact nat_setByte1_13 x v.toNat hx

/-- Two machine byte writes, seen through `setByte13` (the outer write's input is the
machine's 16-bit register value). -/
theorem bv13_setByte_pair (x : Nat) (k1 k2 : Nat) (v1 v2 : BitVec 8)
    (h1 : k1 < 2) (h2 : k2 < 2) (hx : x < 2 ^ 16) :
    bv 13 ((setByte (bv 16 ((setByte (bv 16 x) k1 v1.toNat).toNat)) k2 v2.toNat).toNat) =
      setByte13 (setByte13 (bv 13 x) k1 v1) k2 v2 := by
  rw [bv13_setByte ((setByte (bv 16 x) k1 v1.toNat).toNat) k2 v2 h2 (Nat.mod_lt _ (by decide))]
  rw [bv13_setByte x k1 v1 h1 hx]

/-- Writing the same lane twice keeps the last byte. -/
theorem setByte13_same (x : BitVec 13) (k : Nat) (v1 v2 : BitVec 8) :
    setByte13 (setByte13 x k v1) k v2 = setByte13 x k v2 := by
  unfold setByte13 Metronome.Debug.slice
  by_cases h : k = 0 <;> simp only [h, if_true, if_false, Nat.reduceEqDiff] <;> bv_decide

/-- The two lanes of `setByte13` commute. -/
theorem setByte13_swap (x : BitVec 13) (v0 v1 : BitVec 8) :
    setByte13 (setByte13 x 0 v0) 1 v1 = setByte13 (setByte13 x 1 v1) 0 v0 := by
  unfold setByte13 Metronome.Debug.slice
  simp only [if_true, if_false, Nat.reduceEqDiff]
  bv_decide

/-- The machine's host write as one of a two-byte register's host-selected ports. -/
def hostOpt2 (p0 p1 : Port) : Option (Nat × Nat) :=
  if p0.strobe && p0.host then some (0, p0.hWd.toNat)
  else if p1.strobe && p1.host then some (1, p1.hWd.toNat) else none

/-- The machine's drained core write as one of a two-byte register's core-selected ports. -/
def coreOpt2 (p0 p1 : Port) : Option (Nat × Nat) :=
  if p0.strobe && !p0.host then some (0, p0.cwData.toNat)
  else if p1.strobe && !p1.host then some (1, p1.cwData.toNat) else none

/-- The cut's two-byte write of a 13-bit register, in the cut's own `hi ++ lo` shape:
each lane is its port's winning byte, or holds (SPEC_V2 §13.1). -/
def writeBytes (x : BitVec 13) (p0 p1 : Port) : BitVec 13 :=
  (if p1.strobe then
      Metronome.Debug.slice (if p1.host then p1.hWd else p1.cwData) 0 5
   else Metronome.Debug.slice x 8 5) ++
  (if p0.strobe then (if p0.host then p0.hWd else p0.cwData)
   else Metronome.Debug.slice x 0 8)

/-- The option/strobe abstraction in action: the machine's two `Option` writes and the
cut's two byte ports write the same 13-bit register (SPEC_V2 §13.1's host priority per
byte; the two sources each carry one byte, hence `hSH`). -/
theorem byteW2_bridge (x : Nat) (hx : x < 2 ^ 13) (p0 p1 : Port)
    (hw cw : Option HostWr) (r : String)
    (hH : hwAt hw "DBG" 0 r = hostOpt2 p0 p1)
    (hC : hwAt cw "DBG" 0 r = coreOpt2 p0 p1)
    (hSH : (p0.strobe && p0.host && p1.strobe && p1.host) = false)
    (hSC : (p0.strobe && !p0.host && p1.strobe && !p1.host) = false) :
    bv 13 (byteWOf hw cw x r) = writeBytes (bv 13 x) p0 p1 := by
  have hx16 : x < 2 ^ 16 := by omega
  rw [byteWOf, hC, hH]
  unfold hostOpt2 coreOpt2 writeBytes
  by_cases c0 : p0.strobe <;> by_cases c1 : p1.strobe <;>
    by_cases h0 : p0.host <;> by_cases h1 : p1.host
  all_goals
    simp only [c0, c1, h0, h1, Bool.true_and, Bool.false_and, Bool.and_true,
      Bool.and_false, Bool.not_true, Bool.not_false, if_true, if_false,
      Option.some.injEq, reduceCtorEq] at *
  all_goals
    first
    | rw [bv13_setByte_pair _ _ _ _ _ (by decide) (by decide) hx16]
    | rw [bv13_setByte _ _ _ (by decide) hx16]
    | skip
  all_goals
    first
    | (unfold setByte13 Metronome.Debug.slice
       simp only [if_true, if_false, Nat.reduceEqDiff]
       bv_decide)
    | (rw [Metronome.Debug.slice13])
    | rfl

/-- A `slice` of an `if` distributes. -/
theorem slice_ite {c : Prop} [Decidable c] (a b : BitVec 8) (off n : Nat) :
    Metronome.Debug.slice (if c then a else b) off n =
      (if c then Metronome.Debug.slice a off n else Metronome.Debug.slice b off n) := by
  by_cases h : c <;> simp [h]

/-- Masking a byte with a value below `2^n` only sees its low `n` bits. -/
theorem and_mod (a b n : Nat) (hb : b < 2 ^ n) : a &&& b = a % 2 ^ n &&& b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases h : i < n
  · simp [h]
  · have hbn : b.testBit i = false := by
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega))
    simp [h, hbn]

/-- The cut's low `EMASK` byte port. -/
def emaskPort0 (i : Metronome.Debug.Ctrl.Input) : Port :=
  ⟨i.dWrEm0, i.hEm0, i.hWd, i.cwData⟩

/-- The cut's high `EMASK` byte port. -/
def emaskPort1 (i : Metronome.Debug.Ctrl.Input) : Port :=
  ⟨i.dWrEm1, i.hEm1, i.hWd, i.cwData⟩

/-- The cut's low `RLV` byte port. -/
def rlvPort0 (i : Metronome.Debug.Ctrl.Input) : Port :=
  ⟨i.dWrRlv0, i.hRlv0, i.hWd, i.cwData⟩

/-- The cut's high `RLV` byte port. -/
def rlvPort1 (i : Metronome.Debug.Ctrl.Input) : Port :=
  ⟨i.dWrRlv1, i.hRlv1, i.hWd, i.cwData⟩

/-- §12.4 / §13.1: `EMASK` is the same in the cut and the machine; the host write is one
byte of the register and the drained core write is at most one other (§9, §13.1). -/
theorem emask_bridge (s : Metronome.Debug.Ctrl.State) (ms : Machine.State)
    (i : Metronome.Debug.Ctrl.Input) (hw cw : Option HostWr) (cev apply frozen : Bool)
    (hem : ms.dbg.emask = s.emask)
    (hH : hwAt hw "DBG" 0 "EMASK" = hostOpt2 (emaskPort0 i) (emaskPort1 i))
    (hC : hwAt cw "DBG" 0 "EMASK" = coreOpt2 (emaskPort0 i) (emaskPort1 i))
    (hSH : (i.dWrEm0 && i.hEm0 && i.dWrEm1 && i.hEm1) = false)
    (hSC : (i.dWrEm0 && !i.hEm0 && i.dWrEm1 && !i.hEm1) = false) :
    (Machine.dbgNext ms hw cw cev apply frozen).emask =
      Metronome.Debug.Ctrl.emaskNext s.emask i := by
  rw [dbgNext_emask, hem]
  rw [byteW2_bridge s.emask.toNat s.emask.isLt (emaskPort0 i) (emaskPort1 i) hw cw
    "EMASK" hH hC hSH hSC]
  rw [bv_self]
  unfold writeBytes emaskPort0 emaskPort1 Metronome.Debug.Ctrl.emaskNext
  by_cases h1 : i.hEm1 <;> by_cases h0 : i.hEm0 <;>
    simp [h1, h0, slice_ite]

/-- `a &&& b` for a 13-bit `b` only sees `a`'s low 13 bits. -/
theorem and_nbits13 (a : Nat) (b : BitVec 13) :
    a &&& b.toNat = nbits a 0 13 &&& b.toNat := by
  rw [nbits_zero_pow]
  exact and_mod a b.toNat 13 b.isLt

/-- §13.2: `RLV` is the same in the cut and the machine.  The replay level value
`(RLV & ~EMASK) | (WB[12:0] & EMASK)` is the same (SPEC_V2 §13.2), and the byte writes
act as `EMASK`'s. -/
theorem rlv_bridge (s : Metronome.Debug.Ctrl.State) (i : Metronome.Debug.Ctrl.Input)
    (ms : Machine.State) (wbw : BitVec 32) (hw cw : Option HostWr)
    (cev apply frozen : Bool)
    (hrlv : ms.dbg.rlv = s.rlv) (hem : ms.dbg.emask = s.emask)
    (hwb : (vget ms.streams 0).wb = wbw) (hword : i.replayWord = wbw)
    (happly : apply = Metronome.Debug.Ctrl.apply s.replay i.frz
      (Metronome.Debug.bitAt i.replayValid 0) s.dc i.replayWord)
    (hH : hwAt hw "DBG" 0 "RLV" = hostOpt2 (rlvPort0 i) (rlvPort1 i))
    (hC : hwAt cw "DBG" 0 "RLV" = coreOpt2 (rlvPort0 i) (rlvPort1 i))
    (hSH : (i.dWrRlv0 && i.hRlv0 && i.dWrRlv1 && i.hRlv1) = false)
    (hSC : (i.dWrRlv0 && !i.hRlv0 && i.dWrRlv1 && !i.hRlv1) = false) :
    (Machine.dbgNext ms hw cw cev apply frozen).rlv = Metronome.Debug.Ctrl.rlvNext s i := by
  rw [dbgNext_rlv]
  have hval :
      (if apply then (ms.dbg.rlv.toNat &&& (2 ^ 13 - 1 - ms.dbg.emask.toNat)) |||
          ((vget ms.streams 0).wb.toNat &&& ms.dbg.emask.toNat)
       else ms.dbg.rlv.toNat) =
      (Metronome.Debug.Ctrl.replayLevels s.rlv s.emask
        (Metronome.Debug.Ctrl.apply s.replay i.frz
          (Metronome.Debug.bitAt i.replayValid 0) s.dc i.replayWord) i.replayWord).toNat := by
    rw [replayLevels_toNat, ← happly, hrlv, hem, hwb, hword]
    by_cases h : apply
    · rw [if_pos h, if_pos h]
      have h1 : wbw.toNat &&& s.emask.toNat = nbits wbw.toNat 0 13 &&& s.emask.toNat :=
        and_nbits13 wbw.toNat s.emask
      rw [h1]
    · rw [if_neg h, if_neg h]
  rw [hval]
  have hlvlt : (Metronome.Debug.Ctrl.replayLevels s.rlv s.emask
      (Metronome.Debug.Ctrl.apply s.replay i.frz
        (Metronome.Debug.bitAt i.replayValid 0) s.dc i.replayWord) i.replayWord).toNat < 2 ^ 13 := by
    rw [replayLevels_toNat]
    by_cases h : Metronome.Debug.Ctrl.apply s.replay i.frz
        (Metronome.Debug.bitAt i.replayValid 0) s.dc i.replayWord
    · rw [if_pos h]
      have h1 : s.rlv.toNat &&& (2 ^ 13 - 1 - s.emask.toNat) < 2 ^ 13 := by
        have := s.rlv.isLt; have := s.emask.isLt
        exact Nat.and_lt_two_pow _ (by omega)
      have h2 : nbits i.replayWord.toNat 0 13 &&& s.emask.toNat < 2 ^ 13 :=
        Nat.and_lt_two_pow _ s.emask.isLt
      exact Nat.or_lt_two_pow h1 h2
    · rw [if_neg h]
      exact s.rlv.isLt
  rw [byteW2_bridge _ hlvlt (rlvPort0 i) (rlvPort1 i) hw cw "RLV" hH hC hSH hSC]
  rw [bv_self]
  unfold writeBytes rlvPort0 rlvPort1 Metronome.Debug.Ctrl.rlvNext
  by_cases h1 : i.hRlv1 <;> by_cases h0 : i.hRlv0 <;> simp [h1, h0, slice_ite]

/-- `DC`'s increment: the cut's 19-bit `DC + 1` with wrap at `0x7FFFF` is the machine's
saturating `min (DC + 1) (2^19 - 1)` (SPEC_V2 §12.4). -/
theorem dc_inc (d : BitVec 19) :
    bv 19 (min (d.toNat + 1) (2 ^ 19 - 1)) =
      (if d != (0x7FFFF : BitVec 19) then d + 1 else d) := by
  by_cases h : d = (0x7FFFF : BitVec 19)
  · subst h
    have hne : ¬ ((0x7FFFF : BitVec 19) != (0x7FFFF : BitVec 19)) := by simp
    rw [if_neg hne]
    apply BitVec.toNat_eq.mpr
    rw [bv_toNat']
    have hv : (0x7FFFF : BitVec 19).toNat = 2 ^ 19 - 1 := by decide
    rw [hv]
    rw [show min (2 ^ 19 - 1 + 1) (2 ^ 19 - 1) = 2 ^ 19 - 1 from by omega]
  · have hne : (d != (0x7FFFF : BitVec 19)) = true := by simpa using h
    rw [if_pos hne]
    apply BitVec.toNat_eq.mpr
    rw [bv_toNat', BitVec.toNat_add]
    have hd : d.toNat < 2 ^ 19 - 1 := by
      have hlt := d.isLt
      rcases Nat.lt_or_ge d.toNat (2 ^ 19 - 1) with h' | h'
      · exact h'
      · exfalso
        apply h
        apply BitVec.toNat_eq.mpr
        have : d.toNat = 2 ^ 19 - 1 := by omega
        rw [this]
        decide
    rw [Nat.mod_eq_of_lt (by omega)]
    rw [show ((1 : BitVec 19)).toNat = 1 from rfl]
    omega

/-- The machine's saturating increment as a `Nat`, matching the cut's wrap check. -/
theorem dc_inc_nat (d : BitVec 19) :
    min (d.toNat + 1) (2 ^ 19 - 1) % 2 ^ 19 =
      (if d != (0x7FFFF : BitVec 19) then d + 1 else d).toNat := by
  rw [← bv_toNat' (min (d.toNat + 1) (2 ^ 19 - 1)), dc_inc]

/-- `bv 19 (min …)`'s value, the shape `dbgNext`'s `DC` takes before the outer `if`s. -/
theorem bv_dc_inc_toNat (d : BitVec 19) :
    (bv 19 (min (d.toNat + 1) (2 ^ 19 - 1))).toNat =
      (if d != (0x7FFFF : BitVec 19) then d + 1 else d).toNat := by
  rw [dc_inc]

/-- §12.4 / §12.3: `DC` is the same in the cut and the machine: an `ECTL` write clears
(also frozen), `FRZ` holds, an apply or capture-off cycle clears, an edge event sets 1,
otherwise it counts and saturates. -/
theorem dc_bridge (s : Metronome.Debug.Ctrl.State) (ms : Machine.State)
    (i : Metronome.Debug.Ctrl.Input) (hw cw : Option HostWr) (cev apply frozen : Bool)
    (hdc : ms.dbg.dc = s.dc) (hrpl : ms.dbg.rpl = s.replay) (hcen : ms.dbg.cen = s.cen)
    (hsome : (pickByte hw cw "ECTL").isSome = i.dWrEctl) (hfrz : frozen = i.frz)
    (happly : apply = Metronome.Debug.Ctrl.apply s.replay i.frz
      (Metronome.Debug.bitAt i.replayValid 0) s.dc i.replayWord)
    (hcev : cev = Metronome.Debug.Ctrl.cev s.cen s.replay i.frz i.rise i.fall s.emask) :
    (Machine.dbgNext ms hw cw cev apply frozen).dc = Metronome.Debug.Ctrl.dcNext s i := by
  rw [dbgNext_dc, hsome, hfrz, hdc, hrpl, hcen]
  unfold Metronome.Debug.Ctrl.dcNext
  rw [← happly, ← hcev]
  apply BitVec.toNat_eq.mpr
  have hcev_false : s.replay = true → cev = false := by
    intro h
    rw [hcev, h, Metronome.Debug.Ctrl.cev_replay]
  have happly_false : s.replay = false → apply = false := by
    intro h
    rw [happly]
    unfold Metronome.Debug.Ctrl.apply
    simp [h]
  cases hw : i.dWrEctl
  · cases hf : i.frz
    · cases hr : s.replay
      · cases hc : s.cen
        · rw [bv_toNat']
          simp [hw, hf, hr, hc, happly_false hr, BitVec.toNat_ofNat]
        · cases he : cev
          · simp only [hw, hf, hr, hc, he, happly_false hr, Bool.false_eq_true,
              Bool.true_and, Bool.and_true, Bool.and_false, Bool.false_and, Bool.not_true,
              Bool.not_false, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
              if_true, if_false, reduceIte, ↓reduceIte]
            rw [bv_dc_inc_toNat]
          · rw [bv_toNat']
            simp [hw, hf, hr, hc, he, happly_false hr, BitVec.toNat_ofNat]
      · cases ha : apply
        · simp only [hw, hf, hr, ha, hcev_false hr, Bool.false_eq_true, Bool.true_and,
            Bool.and_true, Bool.and_false, Bool.false_and, Bool.not_true, Bool.not_false,
            Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
            if_true, if_false, reduceIte, ↓reduceIte]
          rw [bv_dc_inc_toNat]
        · rw [bv_toNat']
          simp [hw, hf, hr, ha, BitVec.toNat_ofNat]
    · rw [bv_toNat']
      simp [hw, hf, Nat.mod_eq_of_lt s.dc.isLt]
  · rw [bv_toNat']
    simp [hw, BitVec.toNat_ofNat]

/-- §13.2 replay timer: the cut's `{0,DC} + 1` value. -/
theorem tick_toNat (dc : BitVec 19) : (Metronome.Debug.Ctrl.tick dc).toNat = dc.toNat + 1 := by
  unfold Metronome.Debug.Ctrl.tick
  rw [BitVec.toNat_add, BitVec.toNat_append]
  rw [show (BitVec.toNat (0 : BitVec 1)) = 0 from rfl]
  rw [Nat.shiftLeft_eq, Nat.zero_mul, Nat.zero_or]
  rw [show (BitVec.toNat (1 : BitVec 20)) = 1 from rfl]
  omega

/-- §13.2 record interval: the cut's `{0,WB[31:13]}` value is `WB >>> 13`. -/
theorem interval_toNat (word : BitVec 32) :
    (Metronome.Debug.Ctrl.interval word).toNat = word.toNat >>> 13 := by
  unfold Metronome.Debug.Ctrl.interval
  rw [BitVec.toNat_append]
  rw [show (BitVec.toNat (0 : BitVec 1)) = 0 from rfl]
  rw [Nat.shiftLeft_eq, Nat.zero_mul, Nat.zero_or]
  rw [show (BitVec.toNat (Metronome.Debug.slice word 13 19)) =
    word.toNat / 2 ^ 13 % 2 ^ 19 from by
    rw [slice_toNat, nbits, Nat.shiftRight_eq_div_pow]]
  rw [Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt]
  have hw : word.toNat < 2 ^ 32 := word.isLt
  omega

/-- `tick DC ≥ interval WB` is `DC + 1 ≥ WB >>> 13` (SPEC_V2 §13.2's comparison). -/
theorem ge_eq (dc : BitVec 19) (word : BitVec 32) :
    decide (dc.toNat + 1 ≥ word.toNat >>> 13) =
      decide (Metronome.Debug.Ctrl.tick dc >= Metronome.Debug.Ctrl.interval word) := by
  rw [decide_eq_decide]
  rw [show (Metronome.Debug.Ctrl.tick dc >= Metronome.Debug.Ctrl.interval word) ↔
    (Metronome.Debug.Ctrl.interval word ≤ Metronome.Debug.Ctrl.tick dc) from Iff.rfl]
  rw [BitVec.le_def, tick_toNat, interval_toNat]

/-- `tick DC > interval WB` is `DC + 1 > WB >>> 13` (SPEC_V2 §13.2's `late`). -/
theorem gt_eq (dc : BitVec 19) (word : BitVec 32) :
    decide (dc.toNat + 1 > word.toNat >>> 13) =
      decide (Metronome.Debug.Ctrl.tick dc > Metronome.Debug.Ctrl.interval word) := by
  rw [decide_eq_decide]
  rw [show (Metronome.Debug.Ctrl.tick dc > Metronome.Debug.Ctrl.interval word) ↔
    (Metronome.Debug.Ctrl.interval word < Metronome.Debug.Ctrl.tick dc) from Iff.rfl]
  rw [BitVec.lt_def, tick_toNat, interval_toNat]

/-- `a < b` implies `a ≤ b`, as Bools. -/
theorem decide_le_of_lt (a b : BitVec 20) :
    (decide (a ≤ b) && decide (a < b)) = decide (a < b) := by
  by_cases h : a < b
  · have h2 : a ≤ b := by
      have hlt : a.toNat < b.toNat := by
        rw [BitVec.lt_def] at h
        exact h
      rw [BitVec.le_def]
      omega
    simp [h, h2]
  · simp [h]

/-- §13.2: the replay `apply` flag is the same in the cut and `Machine.replayApply`
(`!frozen && RPL && WV && DC + 1 ≥ WB.DC`). -/
theorem apply_bridge (replay frz valid : Bool) (dc : BitVec 19) (word : BitVec 32)
    (d : DbgSt) (st : StreamSt) (hrpl : d.rpl = replay) (hdc : d.dc = dc)
    (hwv : st.wv = valid) (hwb : st.wb = word) :
    (Machine.replayApply d st frz).1 = Metronome.Debug.Ctrl.apply replay frz valid dc word ∧
    (Machine.replayApply d st frz).2 = Metronome.Debug.Ctrl.late replay frz valid dc word := by
  unfold Machine.replayApply Metronome.Debug.Ctrl.apply Metronome.Debug.Ctrl.late
  dsimp only
  rw [hrpl, hdc, hwv, hwb]
  constructor
  · rw [ge_eq]
    simp [Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]
  · rw [ge_eq, gt_eq]
    simp [Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, decide_le_of_lt]

/-- §13.2: the replay `late` flag is the same in the cut and `Machine.replayApply`. -/
theorem late_bridge (replay frz valid : Bool) (dc : BitVec 19) (word : BitVec 32)
    (d : DbgSt) (st : StreamSt) (hrpl : d.rpl = replay) (hdc : d.dc = dc)
    (hwv : st.wv = valid) (hwb : st.wb = word) :
    (Machine.replayApply d st frz).2 = Metronome.Debug.Ctrl.late replay frz valid dc word :=
  (apply_bridge replay frz valid dc word d st hrpl hdc hwv hwb).2

/-- `nbit` on a `Nat` is the machine's bit read (`Nat.testBit`). -/
theorem nbit_eq_testBit (x k : Nat) : nbit x k = x.testBit k := by
  unfold nbit
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  by_cases h : x / 2 ^ k % 2 = 1
  · simp [h]
  · simp [h]

/-- `Nat.testBit` distributes over `^^^`. -/
theorem testBit_xor (a b k : Nat) : (a ^^^ b).testBit k = (a.testBit k ^^ b.testBit k) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    Nat.testBit_eq_decide_div_mod_eq]
  rw [Nat.xor_div_two_pow]
  rw [show (a / 2 ^ k ^^^ b / 2 ^ k) % 2 = ((a / 2 ^ k ^^^ b / 2 ^ k) % 2 ^ 1) from by
    rw [Nat.pow_one]]
  rw [Nat.xor_mod_two_pow, Nat.pow_one]
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ k) with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ k) with h' | h' <;> simp [h, h']

/-- The machine's edge fold over `List.range n` is the low-`n`-bit value of `x`
(SPEC_V2 §12.4's `cev` edge vector). -/
theorem foldl_bits (x n : Nat) :
    (List.range n).foldl (fun acc k => acc ||| (if nbit x k then 2 ^ k else 0)) 0 = x % 2 ^ n := by
  induction n with
  | zero => rw [show List.range 0 = [] from rfl, Nat.pow_zero, Nat.mod_one]; rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    rw [show ([n]).foldl (fun acc k => acc ||| (if nbit x k then 2 ^ k else 0)) (x % 2 ^ n) =
      x % 2 ^ n ||| (if nbit x n then 2 ^ n else 0) from rfl]
    rw [nbit_eq_testBit]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    have hstep : (if x.testBit n then (2 : Nat) ^ n else 0).testBit i =
        (x.testBit n && decide (n = i)) := by
      by_cases h : x.testBit n
      · simp [h, Nat.testBit_two_pow]
      · simp [h, Nat.zero_testBit]
    rw [hstep]
    by_cases h : i < n
    · have h1 : decide (i < n + 1) = true := by simp; omega
      have h2 : decide (n = i) = false := by simp; omega
      simp [h, h1, h2]
    · by_cases h2 : i = n
      · subst h2
        simp
      · have h1 : decide (i < n + 1) = false := by simp; omega
        have h3 : decide (n = i) = false := by simp; omega
        simp [h, h1, h3]

/-- `nbit` of a vector's value is its `getLsbD`. -/
theorem nbit_getLsbD {w : Nat} (x : BitVec w) (k : Nat) : nbit x.toNat k = x.getLsbD k := by
  rw [nbit_eq_testBit]
  rfl

/-- A masked-bit read: `l & ~p`'s bit `k`. -/
theorem nbit_and_not (l p : BitVec 13) (k : Nat) :
    nbit (l &&& ~~~p).toNat k = (k < 13 && nbit l.toNat k && !nbit p.toNat k) := by
  rw [nbit_eq_testBit, BitVec.toNat_and, BitVec.toNat_not]
  rw [Nat.testBit_and]
  by_cases hk : k < 13
  · have hb : (2 ^ 13 - 1 - p.toNat).testBit k = !p.toNat.testBit k := by
      rw [show (2 ^ 13 - 1 - p.toNat) = 2 ^ 13 - (p.toNat + 1) from by omega]
      rw [Nat.testBit_two_pow_sub_succ p.isLt k]
      simp [hk]
    rw [hb]
    rw [nbit_eq_testBit, nbit_eq_testBit]
    simp [hk]
  · have hb : (2 ^ 13 - 1 - p.toNat).testBit k = false := by
      rw [show (2 ^ 13 - 1 - p.toNat) = 2 ^ 13 - (p.toNat + 1) from by omega]
      rw [Nat.testBit_two_pow_sub_succ p.isLt k]
      simp [hk]
    rw [hb]
    rw [nbit_eq_testBit, nbit_eq_testBit]
    simp [hk]

/-- A masked-bit read: `~l & p`'s bit `k`. -/
theorem nbit_not_and (l p : BitVec 13) (k : Nat) :
    nbit (~~~l &&& p).toNat k = (k < 13 && !nbit l.toNat k && nbit p.toNat k) := by
  rw [nbit_eq_testBit, BitVec.toNat_and, BitVec.toNat_not]
  rw [Nat.testBit_and]
  by_cases hk : k < 13
  · have hb : (2 ^ 13 - 1 - l.toNat).testBit k = !l.toNat.testBit k := by
      rw [show (2 ^ 13 - 1 - l.toNat) = 2 ^ 13 - (l.toNat + 1) from by omega]
      rw [Nat.testBit_two_pow_sub_succ l.isLt k]
      simp [hk]
    rw [hb]
    rw [nbit_eq_testBit, nbit_eq_testBit]
    simp [hk]
  · have hb : (2 ^ 13 - 1 - l.toNat).testBit k = false := by
      rw [show (2 ^ 13 - 1 - l.toNat) = 2 ^ 13 - (l.toNat + 1) from by omega]
      rw [Nat.testBit_two_pow_sub_succ l.isLt k]
      simp [hk]
    rw [hb]
    rw [nbit_eq_testBit, nbit_eq_testBit]
    simp [hk]

/-- A bit read of `^` is the xor of the bit reads. -/
theorem nbit_xor (l p : BitVec 13) (k : Nat) :
    nbit (l ^^^ p).toNat k = (nbit l.toNat k != nbit p.toNat k) := by
  rw [nbit_eq_testBit, BitVec.toNat_xor, testBit_xor, nbit_eq_testBit, nbit_eq_testBit]

/-- §2: the cut's `RISE` bit `k` is the machine's `PinView.rise` of pin `k`. -/
theorem rise_bit (l p : BitVec 13) (pv : PinView) (k : Nat)
    (hl : pv.lvl = l.toNat) (hp : pv.prev = p.toNat) :
    Metronome.Debug.bitAt (Metronome.Debug.Pins.rise l p) k = pv.rise k := by
  unfold PinView.rise Metronome.Debug.Pins.rise
  rw [hl, hp, bitAt_eq_nbit]
  rw [show ((0 : BitVec 3) ++ (l &&& ~~~p)).toNat = (l &&& ~~~p).toNat from by
    rw [BitVec.toNat_append]
    show (0 <<< 13 ||| (l &&& ~~~p).toNat) = (l &&& ~~~p).toNat
    rw [Nat.shiftLeft_eq, Nat.zero_mul, Nat.zero_or]]
  rw [show Tables.N_IN_PINS = 13 from rfl, nbit_and_not]

/-- §2: the cut's `FALL` bit `k` is the machine's `PinView.fall` of pin `k`. -/
theorem fall_bit (l p : BitVec 13) (pv : PinView) (k : Nat)
    (hl : pv.lvl = l.toNat) (hp : pv.prev = p.toNat) :
    Metronome.Debug.bitAt (Metronome.Debug.Pins.fall l p) k = pv.fall k := by
  unfold PinView.fall Metronome.Debug.Pins.fall
  rw [hl, hp, bitAt_eq_nbit]
  rw [show ((0 : BitVec 3) ++ (~~~l &&& p)).toNat = (~~~l &&& p).toNat from by
    rw [BitVec.toNat_append]
    show (0 <<< 13 ||| (~~~l &&& p).toNat) = (~~~l &&& p).toNat
    rw [Nat.shiftLeft_eq, Nat.zero_mul, Nat.zero_or]]
  rw [show Tables.N_IN_PINS = 13 from rfl, nbit_not_and]

/-- §12.4: a pin's edge in the machine's `PinView` is the cut's `RISE ||| FALL` bit. -/
theorem rise_fall_bit (l pr : BitVec 13) (pv : PinView) (k : Nat)
    (hl : pv.lvl = l.toNat) (hp : pv.prev = pr.toNat) :
    (pv.rise k || pv.fall k) = nbit ((l ^^^ pr) : BitVec 13).toNat k := by
  unfold PinView.rise PinView.fall
  rw [show Tables.N_IN_PINS = 13 from rfl, hl, hp, nbit_xor]
  by_cases hk : k < 13
  · simp only [hk, if_true, Bool.true_and]
    cases hl' : nbit l.toNat k <;> cases hp' : nbit pr.toNat k <;> rfl
  · have hl' : nbit l.toNat k = false := by
      rw [nbit_eq_testBit]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le l.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
    have hp' : nbit pr.toNat k = false := by
      rw [nbit_eq_testBit]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le pr.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
    have hx' : nbit ((l ^^^ pr) : BitVec 13).toNat k = false := by
      rw [nbit_eq_testBit]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le (l ^^^ pr).isLt (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hk, hl', hp', hx']

/-- §12.4's edge vector: the machine's edge fold over the 13 pins is the cut's
`(RISE ||| FALL)[12:0]` value, i.e. the pins that changed. -/
theorem edges_bridge (l pr : BitVec 13) (pv : PinView)
    (hl : pv.lvl = l.toNat) (hp : pv.prev = pr.toNat) :
    (List.range Tables.N_IN_PINS).foldl
        (fun acc k => acc ||| (if pv.rise k || pv.fall k then 2 ^ k else 0)) 0 =
      ((l ^^^ pr) : BitVec 13).toNat := by
  have hbit : ∀ k, (pv.rise k || pv.fall k) = nbit ((l ^^^ pr) : BitVec 13).toNat k :=
    fun k => rise_fall_bit l pr pv k hl hp
  rw [show Tables.N_IN_PINS = 13 from rfl]
  simp only [hbit]
  rw [foldl_bits]
  exact Nat.mod_eq_of_lt (l ^^^ pr).isLt

/-- The cut's `RISE` value (pins 13..15 are zero). -/
theorem rise_toNat (l pr : BitVec 13) :
    (Metronome.Debug.Pins.rise l pr).toNat = (l &&& ~~~pr).toNat := by
  unfold Metronome.Debug.Pins.rise
  rw [BitVec.toNat_append]
  show (0 <<< 13 ||| (l &&& ~~~pr).toNat) = (l &&& ~~~pr).toNat
  rw [Nat.shiftLeft_eq, Nat.zero_mul, Nat.zero_or]

/-- The cut's `FALL` value (pins 13..15 are zero). -/
theorem fall_toNat (l pr : BitVec 13) :
    (Metronome.Debug.Pins.fall l pr).toNat = (~~~l &&& pr).toNat := by
  unfold Metronome.Debug.Pins.fall
  rw [BitVec.toNat_append]
  show (0 <<< 13 ||| (~~~l &&& pr).toNat) = (~~~l &&& pr).toNat
  rw [Nat.shiftLeft_eq, Nat.zero_mul, Nat.zero_or]

/-- `(l & ~p) | (~l & p)` is the changed-pin vector `l ^ p`, as `Nat` values. -/
theorem xor_or_toNat (l pr : BitVec 13) :
    ((l &&& ~~~pr).toNat ||| (~~~l &&& pr).toNat) = (l ^^^ pr).toNat := by
  rw [BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_not, BitVec.toNat_xor]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, testBit_xor]
  by_cases hk : k < 13
  · have h1 : (2 ^ 13 - 1 - l.toNat).testBit k = !l.toNat.testBit k := by
      rw [show (2 ^ 13 - 1 - l.toNat) = 2 ^ 13 - (l.toNat + 1) from by omega]
      rw [Nat.testBit_two_pow_sub_succ l.isLt k]
      simp [hk]
    have h2 : (2 ^ 13 - 1 - pr.toNat).testBit k = !pr.toNat.testBit k := by
      rw [show (2 ^ 13 - 1 - pr.toNat) = 2 ^ 13 - (pr.toNat + 1) from by omega]
      rw [Nat.testBit_two_pow_sub_succ pr.isLt k]
      simp [hk]
    rw [h1, h2]
    cases l.toNat.testBit k <;> cases pr.toNat.testBit k <;> simp
  · have h1 : (2 ^ 13 - 1 - l.toNat).testBit k = false := by
      rw [show (2 ^ 13 - 1 - l.toNat) = 2 ^ 13 - (l.toNat + 1) from by omega]
      rw [Nat.testBit_two_pow_sub_succ l.isLt k]
      simp [hk]
    have h2 : (2 ^ 13 - 1 - pr.toNat).testBit k = false := by
      rw [show (2 ^ 13 - 1 - pr.toNat) = 2 ^ 13 - (pr.toNat + 1) from by omega]
      rw [Nat.testBit_two_pow_sub_succ pr.isLt k]
      simp [hk]
    have h3 : l.toNat.testBit k = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le l.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
    have h4 : pr.toNat.testBit k = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le pr.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h1, h2, h3, h4]

/-- The cut's `(RISE ||| FALL)[12:0]` is the pins that changed: `l ^^^ p`. -/
theorem slice_rise_fall (l pr : BitVec 13) :
    Metronome.Debug.slice (Metronome.Debug.Pins.rise l pr ||| Metronome.Debug.Pins.fall l pr) 0 13 =
      l ^^^ pr := by
  apply BitVec.toNat_eq.mpr
  rw [slice_toNat, nbits_zero_pow, BitVec.toNat_or, rise_toNat, fall_toNat, xor_or_toNat,
    Nat.mod_eq_of_lt (l ^^^ pr).isLt]

/-- A 13-bit vector is nonzero exactly when its value is. -/
theorem bne_zero (b : BitVec 13) : (b != 0) = (b.toNat != 0) := by
  by_cases h : b = 0
  · subst h
    rfl
  · have hne : b.toNat ≠ 0 := by
      intro hc
      exact h (BitVec.toNat_eq.mpr (by simpa using hc))
    have hb : (b != 0) = true := by
      rw [bne_iff_ne]
      exact h
    have hn : (b.toNat != 0) = true := by
      rw [bne_iff_ne]
      exact hne
    rw [hb, hn]

/-- §12.4: `cev` is the same in the cut and `Machine.captureEvent`'s first component:
some masked pin rose or fell in an unfrozen, non-replay capture cycle. -/
theorem cev_bridge (d : DbgSt) (pv : PinView) (frozen : Bool) (l pr : BitVec 13)
    (rise fall : BitVec 16) (hl : pv.lvl = l.toNat) (hp : pv.prev = pr.toNat)
    (hr : rise = Metronome.Debug.Pins.rise l pr) (hf : fall = Metronome.Debug.Pins.fall l pr) :
    (Machine.captureEvent d pv frozen).1 =
      Metronome.Debug.Ctrl.cev d.cen d.rpl frozen rise fall d.emask := by
  unfold Machine.captureEvent Metronome.Debug.Ctrl.cev
  rw [hr, hf, edges_bridge l pr pv hl hp, slice_rise_fall, bne_zero,
    show (((l ^^^ pr) &&& d.emask).toNat) = ((l ^^^ pr).toNat &&& d.emask.toNat) from
      BitVec.toNat_and ..]
  simp [Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

/-- The `ECTL` option's presence is the cut's combined strobe (used for `DC`'s clear). -/
theorem ectl_isSome (i : Metronome.Debug.Ctrl.Input) (hw cw : Option HostWr)
    (h : pickByte hw cw "ECTL" = (Port.mk i.dWrEctl i.hEctl i.hWd i.cwData).ok) :
    (pickByte hw cw "ECTL").isSome = i.dWrEctl := by
  rw [h]
  unfold Port.ok
  by_cases hh : i.dWrEctl <;> simp [hh]

/-- §12.2 – §12.4, §13.1, §13.2: the whole chip-top debug cut's next state is the
machine's `dbgNext`, field by field.  `RLVP` needs `frozen = false` (the recorded
disagreement: the machine sets `rlvp := RLV` even in a frozen cycle, while the cut,
the RTL and SPEC_V2 §12.3 hold it). -/
theorem dbg_step_bridge (cs : Metronome.Debug.Ctrl.State) (ds : Metronome.Debug.Digest.State)
    (ms : Machine.State) (i : Metronome.Debug.Ctrl.Input) (di : Metronome.Debug.Digest.Input)
    (hw cw : Option HostWr) (cev apply frozen : Bool) (wbw : BitVec 32)
    (hcen : ms.dbg.cen = cs.cen) (hrpl : ms.dbg.rpl = cs.replay)
    (hem : ms.dbg.emask = cs.emask) (hrlv : ms.dbg.rlv = cs.rlv)
    (hdc : ms.dbg.dc = cs.dc) (hmen : ms.dbg.men = ds.men)
    (hmisr : ms.dbg.misr = ds.misr) (hdifrz : ms.dbg.frz = di.frz)
    (hout : ms.out = di.oOut) (hoen : ms.oen = di.oEe)
    (hmctl : hwByte hw "DBG" 0 "MCTL" =
      (if di.dWrMctl then some di.hWd.toNat else none))
    (hectl : pickByte hw cw "ECTL" = (Port.mk i.dWrEctl i.hEctl i.hWd i.cwData).ok)
    (hEH : hwAt hw "DBG" 0 "EMASK" = hostOpt2 (emaskPort0 i) (emaskPort1 i))
    (hEC : hwAt cw "DBG" 0 "EMASK" = coreOpt2 (emaskPort0 i) (emaskPort1 i))
    (hESH : (i.dWrEm0 && i.hEm0 && i.dWrEm1 && i.hEm1) = false)
    (hESC : (i.dWrEm0 && !i.hEm0 && i.dWrEm1 && !i.hEm1) = false)
    (hRH : hwAt hw "DBG" 0 "RLV" = hostOpt2 (rlvPort0 i) (rlvPort1 i))
    (hRC : hwAt cw "DBG" 0 "RLV" = coreOpt2 (rlvPort0 i) (rlvPort1 i))
    (hRSH : (i.dWrRlv0 && i.hRlv0 && i.dWrRlv1 && i.hRlv1) = false)
    (hRSC : (i.dWrRlv0 && !i.hRlv0 && i.dWrRlv1 && !i.hRlv1) = false)
    (hwb : (vget ms.streams 0).wb = wbw) (hword : i.replayWord = wbw)
    (happly : apply = Metronome.Debug.Ctrl.apply cs.replay i.frz
      (Metronome.Debug.bitAt i.replayValid 0) cs.dc i.replayWord)
    (hcev : cev = Metronome.Debug.Ctrl.cev cs.cen cs.replay i.frz i.rise i.fall cs.emask)
    (hfrozen : frozen = i.frz) (hifrz : i.frz = false) :
    (Machine.dbgNext ms hw cw cev apply frozen).cen =
        Metronome.Debug.Ctrl.cenNext cs i ∧
    (Machine.dbgNext ms hw cw cev apply frozen).rpl =
        Metronome.Debug.Ctrl.replayNext cs i ∧
    (Machine.dbgNext ms hw cw cev apply frozen).emask =
        Metronome.Debug.Ctrl.emaskNext cs.emask i ∧
    (Machine.dbgNext ms hw cw cev apply frozen).rlv =
        Metronome.Debug.Ctrl.rlvNext cs i ∧
    (Machine.dbgNext ms hw cw cev apply frozen).dc =
        Metronome.Debug.Ctrl.dcNext cs i ∧
    (Machine.dbgNext ms hw cw cev apply frozen).men =
        Metronome.Debug.Digest.menNext ds.men di ∧
    (Machine.dbgNext ms hw cw cev apply frozen).misr =
        Metronome.Debug.Digest.misrNext ds.men ds.misr di ∧
    (Machine.dbgNext ms hw cw cev apply frozen).rlvp =
        Metronome.Debug.Ctrl.rlvPrevNext cs i := by
  obtain ⟨hc1, hc2⟩ := ectl_bridge cs ms i hw cw cev apply frozen hcen hrpl hectl
  refine ⟨hc1, hc2, emask_bridge cs ms i hw cw cev apply frozen hem hEH hEC hESH hESC,
    rlv_bridge cs i ms wbw hw cw cev apply frozen hrlv hem hwb hword happly hRH hRC hRSH hRSC,
    dc_bridge cs ms i hw cw cev apply frozen hdc hrpl hcen
      (ectl_isSome i hw cw hectl) hfrozen happly hcev,
    men_bridge ds.men di ms hw hmen hmctl,
    misr_bridge ds.men ds.misr di ms hw hmen hmisr hdifrz hout hoen hmctl, ?_⟩
  rw [dbgNext_rlvp, hfrozen, hifrz, if_neg (by decide), rlvp_agree cs i ms.dbg hifrz hrlv.symm]

end Metronome.Bridge.Debug
