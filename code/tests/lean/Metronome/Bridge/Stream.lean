import Metronome.Stream
import Metronome.Machine

/-!
# Bridge: the per-cut stream spec `Metronome.Stream` and the machine stream `Metronome.Machine.Stream`

`Metronome/Stream.lean` is the specification of SPEC_V2 §6.3/§12.3/§12.4/§13.2
that `stream_check.py` proves the extracted `md2_stream` equal to.  The machine's
`streamNext` (`Metronome.Machine.Stream`) states the same sections from the SPEC
text.  This file gives the abstraction map (the cut's fourteen registers are the
machine `StreamSt`, the cut's mode inputs are the machine's `streamMode`) and
bridges the combinational contract: the `END` / `MARK` / `BYTE` guards, the
`BYTE` source and the RAM request.

## What is bridged here, and what is not

The guards (`END`, `MARK`, `BYTE`), the `BYTE` source and the abstraction maps are
proved equal for every state and every mode.  The register-step bridge and the
three way request bridge (none / word read / byte or word write) are *not*
delivered.  The cut's `STARVED` event in a frozen cycle (`starveEvent` is not
gated by `FRZ`), and the cut's use of `NB` as the frozen-landing holding slot
against the machine's `WB`/`NB` usage, are two places where the two readings
differ in representation; both are reported in `BRIDGE_UNITS_STREAM_NOTES.md`
with the SPEC clause and the two readings.  `cutReq` below records the request
map the request bridge would use.

The frozen register step is bridged both without a rewind (`abs_step_frozen`)
and *with* one (`abs_step_frozen_rewind`): §12.3 keeps a host stream `CTL`
rewind and the `STARVED` clear running while frozen, so a frozen cycle is not
necessarily a holding cycle.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Metronome.Bridge

open Metronome

/-! ## Abstraction -/

namespace StreamB

/-- The abstraction: the cut's registers are the machine's `StreamSt`. -/
def abs (s : Stream.State) : Machine.StreamSt :=
  { pos := s.pos, bidx := s.bidx, ba := s.ba, cur := s.cur, cv := s.cv, wb := s.wb,
    wv := s.wv, rq := s.rq, ld := s.ld, pend := s.pend, pv := s.pv,
    starved := s.starved, nb := s.nb, nv := s.nv }

/-- The cut's configuration inputs as the machine's decoded `StreamCfg`. -/
def cfgOf (i : Stream.Input) : Machine.StreamCfg :=
  { rx := i.cfgMode, msb := i.cfgMsb, start := i.cfgStart.toNat, len := i.cfgLen.toNat,
    mark := i.cfgMark.toNat }

/-- The cut's capture/replay inputs as the machine's debug block (only `cen` and
`rpl` are read by the stream). -/
def dbgOf (i : Stream.Input) : Machine.DbgSt :=
  { cen := i.capEn, rpl := i.replayEn }

/-- The machine mode the cut's inputs select. -/
def modeOf (cap : Bool) (i : Stream.Input) : Nat :=
  if cap && i.replayEn then 3 else if cap && i.capEn then 2 else if i.cfgMode then 1 else 0

/-- `BitVec` equality is `Nat` equality of the values. -/
theorem beq_nat {w : Nat} (x y : BitVec w) : (x == y) = (x.toNat == y.toNat) := by
  rw [Bool.eq_iff_iff]
  simp [BitVec.toNat_eq]

/-! ## Guards -/

/-- `Sk.END = (POS == LEN)`, both readings. -/
theorem end_eq (s : Stream.State) (i : Stream.Input) :
    Machine.streamEnd (cfgOf i) (abs s) = (s.pos == i.cfgLen) := by
  unfold Machine.streamEnd cfgOf abs
  exact (beq_nat s.pos i.cfgLen).symm

/-- `Sk.MARK = (POS == MARK) && (BIDX == 0)`, both readings. -/
theorem mark_eq (s : Stream.State) (i : Stream.Input) :
    Machine.streamMark (cfgOf i) (abs s) = ((s.pos == i.cfgMark) && (s.bidx == 0)) := by
  unfold Machine.streamMark cfgOf abs
  rw [beq_nat s.pos i.cfgMark, beq_nat s.bidx 0]
  rfl

/-- `Sk.BYTE = (BIDX == 0)`, both readings. -/
theorem byteAt_eq (s : Stream.State) :
    Machine.streamAtByte (abs s) = (s.bidx == 0) := by
  unfold Machine.streamAtByte abs
  exact (beq_nat s.bidx 0).symm

/-- Source `Sk.BYTE`: `CUR` in transmit, `PEND` in receive, both readings. -/
theorem byte_eq (s : Stream.State) (i : Stream.Input) :
    Machine.streamByte (cfgOf i) (abs s) = (if i.cfgMode then s.pend else s.cur).toNat := by
  unfold Machine.streamByte cfgOf abs
  by_cases h : i.cfgMode <;> simp [h]

/-! ## The RAM request -/

/-- The cut's `b = MSB ? ~BIDX : BIDX` as a `Nat`: the machine's `streamB`. -/
theorem bsel_toNat (s : Stream.State) (i : Stream.Input) :
    (Stream.bsel s i).toNat = Machine.streamB (cfgOf i) (abs s) := by
  unfold Stream.bsel Machine.streamB cfgOf abs
  by_cases hm : i.cfgMsb = true
  · simp [hm, BitVec.toNat_not]
  · simp [hm]

/-- The four modes, with every mode predicate decided. -/
theorem mode_cases (cap : Bool) (i : Stream.Input) :
    (modeOf cap i = 3 ∧ Stream.rpl cap i = true ∧ Stream.cen cap i = false ∧
      Stream.rxMode cap i = false ∧ Stream.txMode cap i = false) ∨
    (modeOf cap i = 2 ∧ Stream.cen cap i = true ∧ Stream.rpl cap i = false ∧
      Stream.rxMode cap i = false ∧ Stream.txMode cap i = false) ∨
    (modeOf cap i = 1 ∧ Stream.rxMode cap i = true ∧ Stream.cen cap i = false ∧
      Stream.rpl cap i = false ∧ Stream.txMode cap i = false) ∨
    (modeOf cap i = 0 ∧ Stream.txMode cap i = true ∧ Stream.cen cap i = false ∧
      Stream.rpl cap i = false ∧ Stream.rxMode cap i = false) := by
  unfold modeOf Stream.rpl Stream.cen Stream.rxMode Stream.txMode
  by_cases hc : cap = true <;> by_cases hr : i.replayEn = true <;>
    by_cases hq : i.capEn = true <;> by_cases hm : i.cfgMode = true <;>
    simp_all [Bool.and_eq_true, Stream.rpl, Stream.cen, Stream.rxMode, Stream.txMode]

/-- The cut's request flags as one `RamReq`: none, a word read, a byte write or a
whole-word write. -/
def cutReq (cap : Bool) (s : Stream.State) (i : Stream.Input) : Machine.RamReq :=
  if !Stream.req cap s i then .none
  else if Stream.reqWe cap s i then
    (if Stream.reqWord cap s i then
      .wrWord ((Stream.reqAddr cap s i).toNat / 4) (Stream.reqWword cap s i).toNat
     else .wrByte (Stream.reqAddr cap s i).toNat (Stream.reqWdata cap s i).toNat)
  else .rd ((Stream.reqAddr cap s i).toNat / 4) 0

/-! ## The register step's abstraction

The step bridge maps the cut's sampled inputs onto the machine's `StreamIn`
record.  The two derived inputs need care:

* `landNow` is the machine's "the RAM output holds this stream's word read in
  `t-1`".  The cut has no such input: it uses `LD` on `rdata` directly, and gates
  the replay landing by `!FRZD`.  The map is therefore `landNow := LD && !FRZD`,
  which is exactly the chip's timing (a word read in cycle `s` is at the RAM
  output in `s+1`; a freeze in `s+1` captures it at the end of `s+1` and `LD`
  updates in the first unfrozen cycle).
* `ctlMove`/`hCtl` carry the cut's `rewind`, `flush` and `clrStarved` in the
  machine's control bus: bit 0 rewind, bit 1 flush, host bit 7 clear `STARVED`. -/

/-- The control-move bus value: bit 0 rewind, bit 1 flush. -/
def ctlVal (i : Stream.Input) : Nat :=
  (if i.rewind then 1 else 0) + (if i.flush then 2 else 0)

/-- The host `CTL` bus value: bit 7 clears `STARVED`. -/
def clrVal (i : Stream.Input) : Nat := if i.clrStarved then 128 else 0

/-- The machine's per-cycle stream inputs for the cut's sampled inputs. -/
def absIn (_cap : Bool) (s : Stream.State) (i : Stream.Input) : Machine.StreamIn :=
  { adv := i.adv
    rx := if i.rxWe then some (if i.rxBit then 1 else 0) else none
    ctlMove := some (ctlVal i)
    hCtl := some (clrVal i)
    served := i.gnt
    landNow := s.ld && !i.frzd
    ramOut := i.rdata.toNat
    cev := i.capPush
    record := i.capRec.toNat
    apply := i.replayApply
    late := i.replayLate }

/-- The machine debug block with the *gated* capture/replay enables. -/
def dbgOfCap (cap : Bool) (i : Stream.Input) : Machine.DbgSt :=
  { cen := Stream.cen cap i, rpl := Stream.rpl cap i }

@[simp] theorem nbit_ctl0 (i : Stream.Input) :
    Machine.Util.nbit (ctlVal i) 0 = i.rewind := by
  unfold ctlVal Machine.Util.nbit
  by_cases hr : i.rewind = true <;> by_cases hf : i.flush = true <;>
    simp [hr, hf]
  all_goals decide

@[simp] theorem nbit_ctl1 (i : Stream.Input) :
    Machine.Util.nbit (ctlVal i) 1 = i.flush := by
  unfold ctlVal Machine.Util.nbit
  by_cases hr : i.rewind = true <;> by_cases hf : i.flush = true <;>
    simp [hr, hf]
  all_goals decide

@[simp] theorem nbit_clr7 (i : Stream.Input) :
    Machine.Util.nbit (clrVal i) 7 = i.clrStarved := by
  unfold clrVal Machine.Util.nbit
  by_cases hc : i.clrStarved = true <;> simp [hc]
  all_goals decide

@[simp] theorem nbit_clr0 (i : Stream.Input) :
    Machine.Util.nbit (clrVal i) 0 = false := by
  unfold clrVal Machine.Util.nbit
  by_cases hc : i.clrStarved = true <;> simp [hc]
  all_goals decide

/-- The machine's per-stream mode of S0 is the cut's mode selection. -/
theorem streamMode_zero (cap : Bool) (i : Stream.Input) :
    Machine.streamMode (cfgOf i) 0 (dbgOfCap cap i) = modeOf cap i := by
  unfold Machine.streamMode cfgOf dbgOfCap modeOf Stream.cen Stream.rpl
  by_cases h1 : cap = true <;> by_cases h2 : i.replayEn = true <;>
    by_cases h3 : i.capEn = true <;> by_cases h4 : i.cfgMode = true <;>
    simp_all

/-- `n &&& 1` is `n % 2`. -/
theorem and_one (y : Nat) : y &&& 1 = y % 2 := by
  have h : (1 : Nat) = 2 ^ 1 - 1 := by decide
  rw [h, Nat.and_two_pow_sub_one_eq_mod]

/-- The cut's `Stream.bitAt` is the machine's `bit` at the same index. -/
theorem stream_bitAt_eq (x : BitVec 8) (n : BitVec 3) :
    Stream.bitAt x n = Machine.Util.bit x n.toNat := by
  unfold Stream.bitAt Machine.Util.bit
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, BitVec.toNat_eq, BitVec.toNat_and,
    BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod,
    Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, decide_eq_true_eq,
    BitVec.getLsbD]
  rw [show BitVec.toNat (1 : BitVec 8) = 1 from rfl, and_one,
    show BitVec.toNat (0 : BitVec 8) = 0 from rfl]
  omega

/-- The cut's `Sk.BIT` is the machine's transmit bit. -/
theorem bit_eq (cap : Bool) (s : Stream.State) (i : Stream.Input) :
    Stream.bitOut cap s i = Machine.streamBit (cfgOf i) 0 (dbgOfCap cap i) (abs s) := by
  unfold Stream.bitOut Machine.streamBit
  rw [streamMode_zero]
  rw [show Stream.bitAt s.cur (Stream.bsel s i)
        = Machine.Util.bit s.cur (Stream.bsel s i).toNat
      from stream_bitAt_eq s.cur (Stream.bsel s i), bsel_toNat]
  unfold Machine.streamEnd Stream.endC cfgOf
  rw [beq_nat]
  by_cases hm : modeOf cap i = 0
  · have htx : Stream.txMode cap i = true := by
      rcases mode_cases cap i with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, htx, _⟩
      · omega
      · omega
      · omega
      · exact htx
    simp [hm, htx, abs]
  · have htx : Stream.txMode cap i = false := by
      rcases mode_cases cap i with ⟨_, _, _, _, htx⟩ | ⟨_, _, _, _, htx⟩ |
        ⟨_, _, _, _, htx⟩ | ⟨h, htx, _⟩
      · exact htx
      · exact htx
      · exact htx
      · omega
    simp [hm, htx, abs]

/-- **The RAM request bridge.**  The cut's request flags are exactly the
machine's `streamReq` at the selected mode, in all three forms: a word read
(transmit, replay), a byte write (receive) and a whole-word write (capture). -/
theorem cutReq_eq (cap : Bool) (s : Stream.State) (i : Stream.Input) :
    cutReq cap s i = Machine.streamReq (modeOf cap i) (abs s) := by
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · rw [hm]
    simp only [cutReq, Machine.streamReq, abs, Stream.req, Stream.reqWe, Stream.reqWord,
      Stream.reqAddr, Stream.reqWdata, Stream.reqWword, hrpl,
      Bool.not_true, Bool.false_eq_true, if_false, if_true]
    by_cases h : s.rq = true <;> simp_all [Stream.cen, Stream.rpl, Stream.rxMode, Stream.txMode, Bool.and_eq_true]
  · rw [hm]
    simp only [cutReq, Machine.streamReq, abs, Stream.req, Stream.reqWe, Stream.reqWord,
      Stream.reqAddr, Stream.reqWdata, Stream.reqWword, hcen, hrpl, htx,
      Bool.not_true, Bool.false_eq_true, if_false, if_true]
    by_cases h : s.pv = true <;> simp_all [Stream.cen, Stream.rpl, Stream.rxMode, Stream.txMode, Bool.and_eq_true]
  · rw [hm]
    simp only [cutReq, Machine.streamReq, abs, Stream.req, Stream.reqWe, Stream.reqWord,
      Stream.reqAddr, Stream.reqWdata, Stream.reqWword, hrx, hcen, hrpl, htx,
      Bool.not_true, Bool.false_eq_true, if_false, if_true]
    by_cases h : s.pv = true <;> simp_all [Stream.cen, Stream.rpl, Stream.rxMode, Stream.txMode, Bool.and_eq_true]
  · rw [hm]
    simp only [cutReq, Machine.streamReq, abs, Stream.req, Stream.reqWe, Stream.reqWord,
      Stream.reqAddr, Stream.reqWdata, Stream.reqWword, htx, hcen, hrpl,
      Bool.not_true, Bool.false_eq_true, if_false, if_true]
    by_cases h : s.rq = true <;> simp_all [Stream.cen, Stream.rpl, Stream.rxMode, Stream.txMode, Bool.and_eq_true]

end StreamB

/-! ## The register step: the frozen cycle, and the witnessed divergences -/

namespace StreamB

/-- `bv n x.toNat` of an `n`-bit value is that value. -/
theorem bv_id {n : Nat} (x : BitVec n) : Machine.Util.bv n x.toNat = x := by
  simp [Machine.Util.bv, BitVec.ofNat_toNat]

/-- `BitVec` inequality is `Nat` inequality of the values. -/
theorem bne_nat {w : Nat} (x y : BitVec w) : (x != y) = (x.toNat != y.toNat) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
  constructor
  · rintro h h0
    exact h (by rw [← bv_id x, ← bv_id y, h0])
  · rintro h hxy
    exact h (by rw [hxy])

/-- **Frozen-cycle register-step bridge.**  In a frozen cycle (§12.3), with no
rewind, no landing exception and no move input (the chip makes no moves while
frozen: `ADV`, `RX`, a stream flush, a capture push and a replay `late` are all
`false`), the cut's step and the machine's step are the *same state*: both hold
every register and both clear/hold `STARVED` identically.  The excluded cases are
the two divergences witnessed below and in the notes: the frozen landing
(divergence (b)) and the frozen `STARVED` event (divergence (a)); the third
witness is the inert `NV` of a `CAP = 0` stream at a rewind.  A frozen cycle
*may* rewind (§12.3 keeps the host stream `CTL` running), which
`abs_step_frozen_rewind` below also bridges. -/
theorem abs_step_frozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = false)
    (hland : s.ld = true → i.frzd = true)
    (hside : i.adv = false ∧ i.rxWe = false ∧ i.flush = false ∧ i.capPush = false ∧
      i.replayLate = false) :
    abs (Stream.step cap s i) =
      Machine.streamNext (cfgOf i) (modeOf cap i) (abs s) (absIn cap s i) true := by
  have hcon : ¬ (s.ld = true ∧ i.frzd = false) := by
    rintro ⟨h1, h2⟩
    rw [hland h1] at h2
    exact Bool.noConfusion h2
  obtain ⟨ha, hrx, hfl, hce, hla⟩ := hside
  unfold Stream.step Machine.streamNext
  simp only [abs, absIn, cfgOf, cond_eq_ite, hreset, hfrz, hrew, ha, hrx, hfl, hce, hla,
    Stream.posNext, Stream.bidxNext, Stream.baNext, Stream.curNext, Stream.cvNext,
    Stream.wbNext, Stream.wvNext, Stream.rqNext, Stream.ldNext, Stream.pendNext,
    Stream.pvNext, Stream.starvedNext, Stream.nbNext, Stream.nvNext,
    Stream.starveEvent, Stream.starveTx, Stream.starveRx, Stream.advT, Stream.bitin,
    Stream.fl, Stream.push, Stream.done, Stream.endC, Stream.last,
    Machine.Util.streamAuto, Machine.streamEnd, bv_id,
    Option.getD_some, Option.getD_none, nbit_ctl0, nbit_ctl1, nbit_clr7, nbit_clr0,
    Bool.not_true, Bool.false_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    ite_false, ite_true, beq_nat]
  by_cases h0 : cap = true <;> by_cases h1 : s.ld = true <;> by_cases h2 : i.frzd = true <;>
    simp_all

set_option maxHeartbeats 2000000 in
/-- **Frozen-cycle register-step bridge with a host rewind.**  §12.3 keeps the
host stream `CTL` rewind (and the `STARVED` clear) running while frozen, so a
frozen cycle may rewind even though it makes no autonomous update.  In such a
cycle, with no landing exception and no move input, the cut's step and the
machine's step are again the *same state*, field by field: both hold `PEND`,
both take `STARVED` from `STARVED && !CTL[7]`, `WB`/`NB` hold (§6.3's rewind
list does not include them), and both apply §6.3's rewind override
`POS' = 0, BIDX' = 0, BA' = START, CUR' = 0, CV' = WV' = RQ' = LD' = PV' = 0`.
The only field the two readings do not agree on is the inert `NV` of a `CAP = 0`
stream (witness (b') below, §6.3 vs AMBIG(14)); `hnv` is that side condition. -/
theorem abs_step_frozen_rewind (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = true)
    (hland : s.ld = true → i.frzd = true)
    (hside : i.adv = false ∧ i.rxWe = false ∧ i.flush = false ∧ i.capPush = false ∧
      i.replayLate = false)
    (hnv : cap = true ∨ s.nv = false) :
    abs (Stream.step cap s i) =
      Machine.streamNext (cfgOf i) (modeOf cap i) (abs s) (absIn cap s i) true := by
  have hcon : ¬ (s.ld = true ∧ i.frzd = false) := by
    rintro ⟨h1, h2⟩
    rw [hland h1] at h2
    exact Bool.noConfusion h2
  obtain ⟨ha, hrx, hfl, hce, hla⟩ := hside
  unfold Stream.step Machine.streamNext
  simp only [abs, absIn, cfgOf, cond_eq_ite, hreset, hfrz, hrew, ha, hrx, hfl, hce, hla,
    Stream.posNext, Stream.bidxNext, Stream.baNext, Stream.curNext, Stream.cvNext,
    Stream.wbNext, Stream.wvNext, Stream.rqNext, Stream.ldNext, Stream.pendNext,
    Stream.pvNext, Stream.starvedNext, Stream.nbNext, Stream.nvNext,
    Stream.starveEvent, Stream.starveTx, Stream.starveRx, Stream.advT, Stream.bitin,
    Stream.fl, Stream.push, Stream.done, Stream.endC, Stream.last,
    Machine.Util.streamAuto, Machine.streamEnd, bv_id,
    Option.getD_some, Option.getD_none, nbit_ctl0, nbit_ctl1, nbit_clr7, nbit_clr0,
    Bool.not_true, Bool.false_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    ite_false, ite_true, beq_nat]
  rcases hnv with hc | hn
  · by_cases h1 : s.ld = true <;> by_cases h2 : i.frzd = true <;> simp_all
  · by_cases h1 : s.ld = true <;> by_cases h2 : i.frzd = true <;> simp_all

/-- A state for the divergence witnesses. -/
def wS : Stream.State :=
  { pos := 0, bidx := 0, ba := 0, cur := 0, cv := false, wb := 7, wv := false, rq := false,
    ld := true, pend := 0, pv := false, starved := false, nb := 9, nv := false }

/-- Inputs for the transmit `STARVED` witness (a). -/
def wI : Stream.Input :=
  { resetN := true, frz := true, frzd := false, capEn := false, capPush := false, capRec := 0,
    replayEn := false, replayApply := false, replayLate := false, cfgMode := false,
    cfgMsb := false, cfgStart := 0, cfgLen := 5, cfgMark := 0, adv := true, rxWe := false,
    rxBit := false, rewind := false, flush := false, clrStarved := false, gnt := false,
    rdata := 0 }

/-- Inputs for the replay-buffer witness (b). -/
def wI2 : Stream.Input :=
  { wI with replayEn := true, adv := false, rdata := 0x1234 }

/-- State for the inert-`NV` witness: the second slot valid. -/
def wS3 : Stream.State := { wS with nv := true }

/-- Inputs for the inert-`NV` witness: a frozen cycle with a host rewind. -/
def wI3 : Stream.Input := { wI with rewind := true, adv := false }

/-- **Divergence (a), `STARVED` in a frozen cycle.**  §12.3 says a frozen cycle
makes no autonomous update, and the machine's frozen branch returns `ev = false`.
The cut's `starveEvent` is *not* gated by `FRZ`: a free `ADV` in a frozen cycle
raises `STARVED'` in the cut.  §12.3 "streams … make no autonomous update" and
§6.3 `ADV` is a move, so the chip never presents it while frozen. -/
theorem freeze_starved_disagrees :
    (Stream.step false wS wI).starved = true ∧
      (Machine.streamNext (cfgOf wI) (modeOf false wI) (abs wS) (absIn false wS wI) true).starved =
        false := by
  decide

/-- **Divergence (b), the frozen replay landing.**  A word landing in a frozen
cycle with `WV = 0`: the cut parks it in `NB` (`nbNext`) and holds `WB`; the
machine stores it in `WB` (`streamNext`'s frozen branch stores in `WB` unless
`MODE = 3 && WV`, AMBIG(11)).  The valid content agrees — both `WV` and `NV` are
clear — but the raw `NB`/`WB` slots differ. -/
theorem frozen_replay_buffer_disagrees :
    (Stream.step true wS wI2).nb = 0x1234#32 ∧
      (Stream.step true wS wI2).wb = 7#32 ∧
      (Machine.streamNext (cfgOf wI2) (modeOf true wI2) (abs wS) (absIn true wS wI2) true).wb =
        0x1234#32 ∧
      (Machine.streamNext (cfgOf wI2) (modeOf true wI2) (abs wS) (absIn true wS wI2) true).nb =
        9#32 := by
  decide

/-- **Divergence (b'), the inert `NV` of a `CAP = 0` stream at a rewind.**  The
cut's `nvNext` clears `NV` on a rewind only when `CAP = 1` (the field is inert
otherwise: the RTL has no second slot), while the machine's rewind also clears
`NV` (AMBIG(14)).  With `CAP = 0`, `NV` is not an observable register of the
stream. -/
theorem frozen_rewind_inert_nv_disagrees :
    (Stream.step false wS3 wI3).nv = true ∧
      (Machine.streamNext (cfgOf wI3) (modeOf false wI3) (abs wS3)
        (absIn false wS3 wI3) true).nv = false := by
  decide

end StreamB

/-! ## The unfrozen cycle: the replay-buffer relation and the field bridges

The buffer slots are the one place where the two readings need a *relation*
rather than equality: a word landing in a frozen cycle is parked in `NB` by the
cut (`nbNext`'s frozen branch) and in `WB` (or `NB` when `WV`) by the machine
(AMBIG(11)), and `NB`/`NV` are inert in the `CAP = 0` variant.  `ReplayRel` is
that relation; it also carries the two shape facts the landing word needs
(`WV = 0 → NV = 0`, and no read is in flight while a landing is pending). -/

namespace StreamB

/-- `BA[1:0]` as a `Nat`: the lane index. -/
theorem lane_val (s : Stream.State) : (Stream.lane s).toNat = s.ba.toNat % 4 := by
  unfold Stream.lane
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]

/-- `LB` is the machine's lane extraction of `WB`. -/
theorem lb_eq (s : Stream.State) (i : Stream.Input) :
    Stream.lb s i = Machine.Util.bv 8 (Machine.streamLB (abs s)) := by
  rw [← bv_id (Stream.lb s i)]
  congr 1

/-- `streamLB` only reads `WB` and `BA`. -/
theorem streamLB_congr (a b : Machine.StreamSt) (hwb : a.wb = b.wb) (hba : a.ba = b.ba) :
    Machine.streamLB a = Machine.streamLB b := by
  unfold Machine.streamLB
  rw [hwb, hba]

/-- Host `CTL` bit 1 is clear: bit 1 flushes and bit 7 clears `STARVED`. -/
@[simp] theorem nbit_clr1 (i : Stream.Input) : Machine.Util.nbit (clrVal i) 1 = false := by
  unfold clrVal Machine.Util.nbit
  by_cases hc : i.clrStarved = true <;> simp [hc]

@[simp] theorem pair_fst {α β : Type} (a : α) (b : β) : (a, b).1 = a := rfl

@[simp] theorem pair_snd {α β : Type} (a : α) (b : β) : (a, b).2 = b := rfl

@[simp] theorem fst_ite {α β : Type} (c : Prop) [Decidable c] (a b : α × β) :
    (if c then a else b).1 = if c then a.1 else b.1 := by split <;> rfl

@[simp] theorem snd_ite {α β : Type} (c : Prop) [Decidable c] (a b : α × β) :
    (if c then a else b).2 = if c then a.2 else b.2 := by split <;> rfl

@[simp] theorem pos_ite (c : Prop) [Decidable c] (a b : Machine.StreamSt) :
    (if c then a else b).pos = if c then a.pos else b.pos := by split <;> rfl

@[simp] theorem bidx_ite (c : Prop) [Decidable c] (a b : Machine.StreamSt) :
    (if c then a else b).bidx = if c then a.bidx else b.bidx := by split <;> rfl

@[simp] theorem ba_ite (c : Prop) [Decidable c] (a b : Machine.StreamSt) :
    (if c then a else b).ba = if c then a.ba else b.ba := by split <;> rfl

@[simp] theorem cur_ite (c : Prop) [Decidable c] (a b : Machine.StreamSt) :
    (if c then a else b).cur = if c then a.cur else b.cur := by split <;> rfl

@[simp] theorem cv_ite (c : Prop) [Decidable c] (a b : Machine.StreamSt) :
    (if c then a else b).cv = if c then a.cv else b.cv := by split <;> rfl

@[simp] theorem wb_ite (c : Prop) [Decidable c] (a b : Machine.StreamSt) :
    (if c then a else b).wb = if c then a.wb else b.wb := by split <;> rfl

@[simp] theorem wv_ite (c : Prop) [Decidable c] (a b : Machine.StreamSt) :
    (if c then a else b).wv = if c then a.wv else b.wv := by split <;> rfl

@[simp] theorem rq_ite (c : Prop) [Decidable c] (a b : Machine.StreamSt) :
    (if c then a else b).rq = if c then a.rq else b.rq := by split <;> rfl

@[simp] theorem ld_ite (c : Prop) [Decidable c] (a b : Machine.StreamSt) :
    (if c then a else b).ld = if c then a.ld else b.ld := by split <;> rfl

@[simp] theorem pend_ite (c : Prop) [Decidable c] (a b : Machine.StreamSt) :
    (if c then a else b).pend = if c then a.pend else b.pend := by split <;> rfl

@[simp] theorem pv_ite (c : Prop) [Decidable c] (a b : Machine.StreamSt) :
    (if c then a else b).pv = if c then a.pv else b.pv := by split <;> rfl

@[simp] theorem starved_ite (c : Prop) [Decidable c] (a b : Machine.StreamSt) :
    (if c then a else b).starved = if c then a.starved else b.starved := by split <;> rfl

@[simp] theorem nb_ite (c : Prop) [Decidable c] (a b : Machine.StreamSt) :
    (if c then a else b).nb = if c then a.nb else b.nb := by split <;> rfl

@[simp] theorem nv_ite (c : Prop) [Decidable c] (a b : Machine.StreamSt) :
    (if c then a else b).nv = if c then a.nv else b.nv := by split <;> rfl

/-- **`ReplayRel`: the replay-buffer relation.**  `WV` and `NV` agree; a valid
`WB`/`NB` agrees; the second slot is never valid while the first is empty; the
pending landing word agrees (the cut's `NB` against the machine's `WB` when `WV`
is clear, the machine's `NB` when `WV` is set); and no read is in flight while a
landing is pending.  For `CAP = 0` the second slots are inert in the cut, so the
relation only asks for `WB`/`WV`/`NB` equality. -/
def ReplayRel (cap : Bool) (s : Stream.State) (m : Machine.StreamSt) : Prop :=
  (cap = true →
    s.wv = m.wv ∧ s.nv = m.nv ∧
    (s.wv = true → s.wb = m.wb) ∧
    (s.nv = true → s.nb = m.nb) ∧
    (s.wv = false → s.nv = false) ∧
    (s.ld = true → s.nb = (if s.wv = true then m.nb else m.wb)))
  ∧ (cap = false → s.wb = m.wb ∧ s.wv = m.wv ∧ s.nb = m.nb)
  ∧ ¬ (s.rq = true ∧ s.ld = true)

/-- **`AbsRel`: the abstraction relation of the unfrozen bridge.**  The ten
non-buffer registers agree and `ReplayRel` holds for the buffer slots. -/
def AbsRel (cap : Bool) (s : Stream.State) (m : Machine.StreamSt) : Prop :=
  s.pos = m.pos ∧ s.bidx = m.bidx ∧ s.ba = m.ba ∧ s.cur = m.cur ∧ s.cv = m.cv ∧
  s.rq = m.rq ∧ s.ld = m.ld ∧ s.pend = m.pend ∧ s.pv = m.pv ∧ s.starved = m.starved ∧
  ReplayRel cap s m

/-- `END` in the two readings. -/
theorem endC_eq (s : Stream.State) (i : Stream.Input) (m : Machine.StreamSt)
    (hpos : s.pos = m.pos) :
    Stream.endC s i = Machine.streamEnd (cfgOf i) m := by
  unfold Stream.endC Machine.streamEnd cfgOf
  rw [beq_nat, hpos]

/-- `BIDX == 7` in the two readings. -/
theorem last_eq (s : Stream.State) (m : Machine.StreamSt) (hbidx : s.bidx = m.bidx) :
    Stream.last s = (m.bidx.toNat == 7) := by
  unfold Stream.last
  rw [beq_nat, hbidx]
  simp

/-- `BA[1:0] == 3` in the two readings: the last lane of the lookahead word. -/
theorem lane_three (s : Stream.State) (m : Machine.StreamSt) (hba : s.ba = m.ba) :
    (Stream.lane s == 3) = (m.ba.toNat % 4 == 3) := by
  rw [beq_nat, lane_val, hba]
  simp

/-- `LB` in the two readings, for states with the same `WB` and `BA`. -/
theorem lb_eq_m (s : Stream.State) (i : Stream.Input) (m : Machine.StreamSt)
    (hwb : s.wb = m.wb) (hba : s.ba = m.ba) :
    Stream.lb s i = Machine.Util.bv 8 (Machine.streamLB m) := by
  rw [lb_eq, streamLB_congr (abs s) m hwb hba]

/-- A valid first slot agrees. -/
theorem ReplayRel.wb_of_wv {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : ReplayRel cap s m) (hwv : s.wv = true) : s.wb = m.wb := by
  rcases h with ⟨h1, h2, _⟩
  by_cases hc : cap = true
  · exact (h1 hc).2.2.1 hwv
  · rcases h2 (by simp [hc]) with ⟨hwb, _, _⟩
    exact hwb

/-- A valid second slot agrees. -/
theorem ReplayRel.nb_of_nv {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : ReplayRel cap s m) (hc : cap = true) (hnv : s.nv = true) : s.nb = m.nb :=
  h.1 hc |>.2.2.2.1 hnv

/-- The validity flags agree. -/
theorem ReplayRel.wv_eq {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : ReplayRel cap s m) : s.wv = m.wv := by
  rcases h with ⟨h1, h2, _⟩
  by_cases hc : cap = true
  · exact (h1 hc).1
  · exact (h2 (by simp [hc])).2.1

theorem ReplayRel.nv_eq {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : ReplayRel cap s m) (hc : cap = true) : s.nv = m.nv :=
  h.1 hc |>.2.1

/-- The second slot is never valid while the first is empty. -/
theorem ReplayRel.shape {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : ReplayRel cap s m) (hc : cap = true) (hwv : s.wv = false) : s.nv = false :=
  h.1 hc |>.2.2.2.2.1 hwv

/-- **`BufRel`: the replay-buffer relation proved preserved by the unfrozen step.**
It is `ReplayRel` without the pending-landing clause (and without the buffer
occupancy shape), i.e. the part that holds in every unfrozen cycle. -/
def BufRel (cap : Bool) (s : Stream.State) (m : Machine.StreamSt) : Prop :=
  (cap = true →
    s.wv = m.wv ∧ s.nv = m.nv ∧
    (s.wv = true → s.wb = m.wb) ∧
    (s.nv = true → s.nb = m.nb))
  ∧ (cap = false → s.wb = m.wb ∧ s.wv = m.wv ∧ s.nb = m.nb)
  ∧ ¬ (s.rq = true ∧ s.ld = true)

/-- The abstraction relation of the unfrozen bridge. -/
def AbsRelB (cap : Bool) (s : Stream.State) (m : Machine.StreamSt) : Prop :=
  s.pos = m.pos ∧ s.bidx = m.bidx ∧ s.ba = m.ba ∧ s.cur = m.cur ∧ s.cv = m.cv ∧
  s.rq = m.rq ∧ s.ld = m.ld ∧ s.pend = m.pend ∧ s.pv = m.pv ∧ s.starved = m.starved ∧
  BufRel cap s m

/-- The validity flags agree. -/
theorem BufRel.wv_eq {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : BufRel cap s m) : s.wv = m.wv := by
  rcases h with ⟨h1, h2, _⟩
  by_cases hc : cap = true
  · exact (h1 hc).1
  · exact (h2 (by cases cap <;> simp_all)).2.1

/-- A valid first slot agrees. -/
theorem BufRel.wb_of_wv {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : BufRel cap s m) (hwv : s.wv = true) : s.wb = m.wb := by
  rcases h with ⟨h1, h2, _⟩
  by_cases hc : cap = true
  · exact (h1 hc).2.2.1 hwv
  · exact (h2 (by cases cap <;> simp_all)).1

/-- The validity flags agree (CAP = 1). -/
theorem BufRel.nv_eq {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : BufRel cap s m) (hc : cap = true) : s.nv = m.nv :=
  (h.1 hc).2.1

/-- A valid second slot agrees. -/
theorem BufRel.nb_of_nv {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : BufRel cap s m) (hc : cap = true) (hnv : s.nv = true) : s.nb = m.nb :=
  (h.1 hc).2.2.2 hnv

/-- `ReplayRel` implies `BufRel`. -/
theorem ReplayRel.toBufRel {cap : Bool} {s : Stream.State} {m : Machine.StreamSt}
    (h : ReplayRel cap s m) : BufRel cap s m := by
  rcases h with ⟨h1, h2, h3⟩
  refine ⟨?_, h2, h3⟩
  intro hc
  exact ⟨(h1 hc).1, (h1 hc).2.1, (h1 hc).2.2.1, (h1 hc).2.2.2.1⟩

/-- `cap = false` from `cap ≠ true`. -/
theorem cap_false {cap : Bool} (h : ¬ cap = true) : cap = false := by cases cap <;> simp_all

/-- The rewind target address in the two readings. -/
theorem cfgStart_bv (i : Stream.Input) : i.cfgStart = Machine.Util.bv 11 (cfgOf i).start := by
  unfold cfgOf
  exact (bv_id i.cfgStart).symm

/-- `rfl`, or a `simp_all` with a large step budget. -/
macro "smash" : tactic =>
  `(tactic| first | rfl | simp_all (config := { maxSteps := 8000000 }))

/-- Unfold both steps and every condition of the cycle. -/
macro "ssimp" : tactic =>
  `(tactic| simp only [Stream.step, Stream.posNext, Stream.bidxNext, Stream.baNext, Stream.curNext,
    Stream.cvNext, Stream.wbNext, Stream.wvNext, Stream.rqNext, Stream.ldNext, Stream.pendNext,
    Stream.pvNext, Stream.starvedNext, Stream.nbNext, Stream.nvNext,
    Stream.advT, Stream.starveTx, Stream.starveRx, Stream.starveEvent, Stream.push, Stream.done,
    Stream.bitin, Stream.fl, Stream.last, Stream.occupied, Stream.landing,
    Machine.streamNext, Machine.Util.streamAuto, absIn, beq_nat, bne_nat, lane_val, cfgStart_bv])

end StreamB

/-! ## The transmit cycle (mode 0) -/

namespace StreamB

/-- `adv` in the two readings. -/
theorem advT_eq (cap : Bool) (s : Stream.State) (i : Stream.Input) (m : Machine.StreamSt)
    (htx : Stream.txMode cap i = true) (hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m) :
    Stream.advT cap s i = (i.adv && !Machine.streamEnd (cfgOf i) m) := by
  unfold Stream.advT
  rw [htx, hend]
  simp

set_option maxHeartbeats 1600000 in
theorem pos_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (h : AbsRelB cap s m) :
    (Stream.step cap s i).pos =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).pos := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  clear hcur hpend hstar
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hwveq : s.wv = m.wv := BufRel.wv_eq hbuf
  have hlast : Stream.last s = (m.bidx.toNat == 7) := last_eq s m hbidx
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hpos, hbidx, hrq, hld]
    by_cases hrew : i.rewind = true <;> by_cases hrg : m.rq = true <;> by_cases hg : i.gnt = true <;>
      simp_all
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hpos, hbidx, hpv]
    by_cases hrew : i.rewind = true <;> by_cases hpush : i.capPush = true <;>
      by_cases he : Machine.streamEnd (cfgOf i) m = true <;> by_cases hpg : m.pv = true <;>
      by_cases hg : i.gnt = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hpos, hbidx]
    by_cases hrew : i.rewind = true <;> by_cases hd : Stream.done cap s i = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hpos, hbidx, advT_eq cap s i m htx hend, hlast]
    by_cases hrew : i.rewind = true <;> by_cases hcv' : m.cv = true <;>
      by_cases hb7 : m.bidx.toNat = 7 <;> smash

/-- `b` in the two readings. -/
theorem bsel_eq_m (s : Stream.State) (i : Stream.Input) (m : Machine.StreamSt)
    (hbidx : s.bidx = m.bidx) :
    (Stream.bsel s i).toNat = Machine.streamB (cfgOf i) m := by
  rw [bsel_toNat]
  unfold Machine.streamB cfgOf abs
  rw [hbidx]

/-- `bitin` in the two readings. -/
theorem bitin_eq (cap : Bool) (s : Stream.State) (i : Stream.Input) (m : Machine.StreamSt)
    (hrx : Stream.rxMode cap i = true) (hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m) :
    Stream.bitin cap s i = (i.rxWe && !Machine.streamEnd (cfgOf i) m) := by
  unfold Stream.bitin
  rw [hrx, hend]
  simp

/-- The machine's received bus `isSome` is the cut's `RX` enable. -/
@[simp] theorem absIn_rx_isSome (cap : Bool) (s : Stream.State) (i : Stream.Input) :
    (absIn cap s i).rx.isSome = i.rxWe := by
  unfold absIn
  cases i.rxWe <;> simp

/-- Bit 0 of the machine's `RX` bus value is the cut's `RX` bit. -/
@[simp] theorem absIn_bus0 (i : Stream.Input) :
    Machine.Util.nbit (if i.rxBit then 1 else 0) 0 = i.rxBit := by
  unfold Machine.Util.nbit
  cases i.rxBit <;> simp

/-- `1 <<< b` as a `Nat`. -/
theorem shift_one_nat (b : Nat) (hb : b < 8) : ((1 : BitVec 8) <<< b).toNat = 2 ^ b := by
  have h2 : 2 ^ b < 2 ^ 8 := Nat.pow_lt_pow_right (by decide) hb
  rw [BitVec.toNat_shiftLeft]
  rw [show ((1 : BitVec 8).toNat <<< b) = 2 ^ b by
    simp [Nat.one_shiftLeft]]
  exact Nat.mod_eq_of_lt h2

/-- `NSH` in the two readings. -/
theorem nsh_eq (cap : Bool) (s : Stream.State) (i : Stream.Input) (m : Machine.StreamSt)
    (hrx : Stream.rxMode cap i = true) (hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m)
    (hcur : s.cur = m.cur) (hbidx : s.bidx = m.bidx) :
    Stream.nsh cap s i =
      Machine.Util.bv 8 (m.cur.toNat |||
        (if ((absIn cap s i).rx.isSome && !Machine.streamEnd (cfgOf i) m) &&
            Machine.Util.nbit (if i.rxBit then 1 else 0) 0 then
          2 ^ Machine.streamB (cfgOf i) m else 0)) := by
  have hb : (Stream.bsel s i).toNat = Machine.streamB (cfgOf i) m := bsel_eq_m s i m hbidx
  have hb8 : Machine.streamB (cfgOf i) m < 8 := by
    rw [← hb]
    exact (Stream.bsel s i).isLt
  have hisSome : (absIn cap s i).rx.isSome = i.rxWe := by
    unfold absIn
    cases i.rxWe <;> simp
  have hbus : Machine.Util.nbit (if i.rxBit then 1 else 0) 0 = i.rxBit := by
    unfold Machine.Util.nbit
    cases i.rxBit <;> simp
  unfold Stream.nsh
  rw [bitin_eq cap s i m hrx hend, hb, hcur, hisSome, hbus]
  rw [← bv_id (m.cur ||| (if (i.rxWe && !Machine.streamEnd (cfgOf i) m) && i.rxBit then
    (1 : BitVec 8) <<< Machine.streamB (cfgOf i) m else 0))]
  congr 1
  by_cases hc : ((i.rxWe && !Machine.streamEnd (cfgOf i) m) && i.rxBit) = true
  · rw [BitVec.toNat_or, if_pos hc, if_pos hc, shift_one_nat _ hb8]
  · rw [if_neg hc, if_neg hc]
    simp

set_option maxHeartbeats 1600000 in
theorem bidx_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (h : AbsRelB cap s m) :
    (Stream.step cap s i).bidx =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).bidx := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  clear hcur hpend hpv hstar
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hwveq : s.wv = m.wv := BufRel.wv_eq hbuf
  have hlast : Stream.last s = (m.bidx.toNat == 7) := last_eq s m hbidx
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hpos, hbidx]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hpos, hbidx]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hpos, hbidx]
    by_cases hrew : i.rewind = true <;> by_cases hxw : i.rxWe = true <;>
      by_cases hfl : i.flush = true <;> by_cases he : Machine.streamEnd (cfgOf i) m = true <;>
      by_cases hb7 : m.bidx.toNat = 7 <;> by_cases hb0 : m.bidx.toNat = 0 <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hpos, hbidx, advT_eq cap s i m htx hend, hlast]
    by_cases hrew : i.rewind = true <;> by_cases hcv' : m.cv = true <;>
      by_cases hb7 : m.bidx.toNat = 7 <;> by_cases hwv : m.wv = true <;> smash

set_option maxHeartbeats 1600000 in
theorem rq_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (h : AbsRelB cap s m) :
    (Stream.step cap s i).rq =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).rq := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  clear hcur hpend hpv hstar
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hwveq : s.wv = m.wv := BufRel.wv_eq hbuf
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · ssimp
    have hcap : cap = true := (Stream.rpl_facts cap i hrpl).1
    simp only [hwveq, BufRel.nv_eq hbuf hcap, BufRel.nb_of_nv hbuf hcap, hreset, hfrz, hm, hend, hrq, hld]
    by_cases hrew : i.rewind = true <;> by_cases hg : i.gnt = true <;>
      by_cases he : Machine.streamEnd (cfgOf i) m = true <;>
      by_cases hwv : m.wv = true <;> by_cases hnv : m.nv = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hrq, hld]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hrq, hld]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hrq, hld]
    by_cases hrew : i.rewind = true <;> by_cases hg : i.gnt = true <;> by_cases hwv : m.wv = true <;>
      simp_all

set_option maxHeartbeats 1600000 in
theorem ld_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (h : AbsRelB cap s m) :
    (Stream.step cap s i).ld =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).ld := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  clear hcur hpend hpv hstar
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hwveq : s.wv = m.wv := BufRel.wv_eq hbuf
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hrq, hld]
    by_cases hrew : i.rewind = true <;> by_cases hg : i.gnt = true <;>
      by_cases hrq' : m.rq = true <;> by_cases hld' : m.ld = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hrq, hld]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hrq, hld]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hrq, hld]
    by_cases hrew : i.rewind = true <;> by_cases hg : i.gnt = true <;>
      by_cases hrq' : m.rq = true <;> by_cases hld' : m.ld = true <;> smash

set_option maxHeartbeats 1600000 in
theorem ba_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (h : AbsRelB cap s m) :
    (Stream.step cap s i).ba =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).ba := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  clear hcur hpend hstar
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hwveq : s.wv = m.wv := BufRel.wv_eq hbuf
  have hlast : Stream.last s = (m.bidx.toNat == 7) := last_eq s m hbidx
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hba, hbidx, hrq, hld, hpv]
    by_cases hrew : i.rewind = true <;> by_cases hg : i.gnt = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hba, hbidx, hrq, hld, hpv]
    by_cases hrew : i.rewind = true <;> by_cases hg : i.gnt = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hba, hbidx, hrq, hld, hpv]
    by_cases hrew : i.rewind = true <;> by_cases hg : i.gnt = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hba, hbidx, hrq, hld,
      advT_eq cap s i m htx hend, hlast]
    by_cases hrew : i.rewind = true <;> by_cases hcv' : m.cv = true <;>
      by_cases hwv : m.wv = true <;> by_cases hb7 : m.bidx.toNat = 7 <;>
      smash

set_option maxHeartbeats 1600000 in
theorem cv_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (h : AbsRelB cap s m) :
    (Stream.step cap s i).cv =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).cv := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  clear hcur hpend hstar
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hwveq : s.wv = m.wv := BufRel.wv_eq hbuf
  have hlast : Stream.last s = (m.bidx.toNat == 7) := last_eq s m hbidx
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hcv, hbidx]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hcv, hbidx]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hcv, hbidx]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hcv, hbidx,
      advT_eq cap s i m htx hend, hlast]
    by_cases hrew : i.rewind = true <;> by_cases hcv' : m.cv = true <;>
      by_cases hwv : m.wv = true <;> by_cases hb7 : m.bidx.toNat = 7 <;>
      smash

set_option maxHeartbeats 1600000 in
theorem cur_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (h : AbsRelB cap s m) :
    (Stream.step cap s i).cur =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).cur := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  clear hpend hstar
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hwveq : s.wv = m.wv := BufRel.wv_eq hbuf
  have hlast : Stream.last s = (m.bidx.toNat == 7) := last_eq s m hbidx
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hcur]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hcur]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    have hns := nsh_eq cap s i m hrx hend hcur hbidx
    simp only [hwveq, hreset, hfrz, hm, hend, hcur, hbidx, hns]
    by_cases hrew : i.rewind = true <;> by_cases hxw : i.rxWe = true <;>
      by_cases hfl : i.flush = true <;> by_cases he : Machine.streamEnd (cfgOf i) m = true <;>
      by_cases hb7 : m.bidx.toNat = 7 <;> by_cases hb0 : m.bidx.toNat = 0 <;>
      smash
  · ssimp
    by_cases hrew : i.rewind = true
    · simp only [hwveq, hreset, hfrz, hm, hend, hcur, hbidx, hba, hcv,
        advT_eq cap s i m htx hend, hlast]
      smash
    · by_cases hwv : s.wv = true
      · have hwb : s.wb = m.wb := hbuf.wb_of_wv hwv
        simp only [hwveq, hreset, hfrz, hm, hend, hcur, hbidx, hba, hcv,
          advT_eq cap s i m htx hend, hlast, lb_eq_m s i m hwb hba]
        by_cases hcv' : m.cv = true <;> by_cases hb7 : m.bidx.toNat = 7 <;>
          smash
      · simp only [hwveq, hreset, hfrz, hm, hend, hcur, hbidx, hba, hcv,
          advT_eq cap s i m htx hend, hlast]
        by_cases hcv' : m.cv = true <;> by_cases hb7 : m.bidx.toNat = 7 <;>
          smash

set_option maxHeartbeats 1600000 in
theorem pend_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (h : AbsRelB cap s m) :
    (Stream.step cap s i).pend =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).pend := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  clear hstar
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hwveq : s.wv = m.wv := BufRel.wv_eq hbuf
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hpend]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hpend]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    have hns := nsh_eq cap s i m hrx hend hcur hbidx
    simp only [hwveq, hreset, hfrz, hm, hend, hcur, hbidx, hpend, hpv, hns]
    by_cases hxw : i.rxWe = true <;> by_cases hfl : i.flush = true <;>
      by_cases he : Machine.streamEnd (cfgOf i) m = true <;> by_cases hb7 : m.bidx.toNat = 7 <;>
      by_cases hb0 : m.bidx.toNat = 0 <;> by_cases hpv' : m.pv = true <;>
      by_cases hg : i.gnt = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hpend]
    by_cases hrew : i.rewind = true <;> smash

set_option maxHeartbeats 1600000 in
theorem pv_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (h : AbsRelB cap s m) :
    (Stream.step cap s i).pv =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).pv := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  clear hstar
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hwveq : s.wv = m.wv := BufRel.wv_eq hbuf
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hpv]
    by_cases hrew : i.rewind = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hpv]
    by_cases hrew : i.rewind = true <;> by_cases hcp : i.capPush = true <;>
      by_cases he : Machine.streamEnd (cfgOf i) m = true <;> by_cases hg : i.gnt = true <;>
      smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hpv]
    by_cases hrew : i.rewind = true <;> by_cases hxw : i.rxWe = true <;>
      by_cases hfl : i.flush = true <;> by_cases he : Machine.streamEnd (cfgOf i) m = true <;>
      by_cases hb7 : m.bidx.toNat = 7 <;> by_cases hb0 : m.bidx.toNat = 0 <;>
      by_cases hg : i.gnt = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hpv]
    by_cases hrew : i.rewind = true <;> smash

set_option maxHeartbeats 4000000 in
theorem starved_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (h : AbsRelB cap s m) :
    (Stream.step cap s i).starved =
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).starved := by
  obtain ⟨hpos, hbidx, hba, hcur, hcv, hrq, hld, hpend, hpv, hstar, hbuf⟩ := h
  clear hba hcur hpend
  have hend : Stream.endC s i = Machine.streamEnd (cfgOf i) m := endC_eq s i m hpos
  have hwveq : s.wv = m.wv := BufRel.wv_eq hbuf
  have hlast : Stream.last s = (m.bidx.toNat == 7) := last_eq s m hbidx
  rcases mode_cases cap i with ⟨hm, hrpl, hcen, hrx, htx⟩ | ⟨hm, hcen, hrpl, hrx, htx⟩ |
    ⟨hm, hrx, hcen, hrpl, htx⟩ | ⟨hm, htx, hcen, hrpl, hrx⟩
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hstar, hbidx]
    by_cases hc : i.clrStarved = true <;> by_cases hs : m.starved = true <;>
      by_cases hl : i.replayLate = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hstar, hbidx, hpv]
    by_cases hcp : i.capPush = true <;> by_cases he : Machine.streamEnd (cfgOf i) m = true <;>
      by_cases hpv' : m.pv = true <;> by_cases hg : i.gnt = true <;>
      by_cases hc : i.clrStarved = true <;> by_cases hs : m.starved = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hstar, hbidx, hpv]
    by_cases hxw : i.rxWe = true <;> by_cases hfl : i.flush = true <;>
      by_cases he : Machine.streamEnd (cfgOf i) m = true <;> by_cases hb7 : m.bidx.toNat = 7 <;>
      by_cases hb0 : m.bidx.toNat = 0 <;> by_cases hpv' : m.pv = true <;>
      by_cases hg : i.gnt = true <;> by_cases hc : i.clrStarved = true <;>
      by_cases hs : m.starved = true <;> smash
  · ssimp
    simp only [hwveq, hreset, hfrz, hm, hend, hstar, hbidx, hcv,
      advT_eq cap s i m htx hend, hlast]
    by_cases hadv : i.adv = true <;> by_cases hcv' : m.cv = true <;>
      by_cases hwv : m.wv = true <;> by_cases hb7 : m.bidx.toNat = 7 <;>
      by_cases he : Machine.streamEnd (cfgOf i) m = true <;>
      by_cases hc : i.clrStarved = true <;> by_cases hs : m.starved = true <;> smash
/-! ## The assembled unfrozen step

The ten scalar registers are bridged for every unfrozen cycle.  The replay
buffer slots need `BufRel`; its preservation is *not* proved here: the
`WB`/`NB` representation differs in the replay landing and `apply` corners
(see `BRIDGE_UNITS_STREAM_NOTES.md`). -/

/-- **The unfrozen register step, scalar fragment.**  With `FRZ = 0`, the cut's
ten scalar registers step to the machine's registers under `AbsRelB`. -/
theorem abs_step_unfrozen (cap : Bool) (s : Stream.State) (i : Stream.Input)
    (m : Machine.StreamSt) (hreset : i.resetN = true) (hfrz : i.frz = false)
    (h : AbsRelB cap s m) :
    (Stream.step cap s i).pos = (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).pos ∧
    (Stream.step cap s i).bidx = (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).bidx ∧
    (Stream.step cap s i).ba = (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).ba ∧
    (Stream.step cap s i).cur = (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).cur ∧
    (Stream.step cap s i).cv = (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).cv ∧
    (Stream.step cap s i).rq = (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).rq ∧
    (Stream.step cap s i).ld = (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).ld ∧
    (Stream.step cap s i).pend = (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).pend ∧
    (Stream.step cap s i).pv = (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).pv ∧
    (Stream.step cap s i).starved = (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false).starved :=
  ⟨pos_step_unfrozen cap s i m hreset hfrz h,
   bidx_step_unfrozen cap s i m hreset hfrz h,
   ba_step_unfrozen cap s i m hreset hfrz h,
   cur_step_unfrozen cap s i m hreset hfrz h,
   cv_step_unfrozen cap s i m hreset hfrz h,
   rq_step_unfrozen cap s i m hreset hfrz h,
   ld_step_unfrozen cap s i m hreset hfrz h,
   pend_step_unfrozen cap s i m hreset hfrz h,
   pv_step_unfrozen cap s i m hreset hfrz h,
   starved_step_unfrozen cap s i m hreset hfrz h⟩

end StreamB

end Metronome.Bridge
