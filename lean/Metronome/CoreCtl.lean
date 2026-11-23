import Metronome.Transition
import Std.Tactic.BVDecide

/-!
# Core control: the write-group pick, the freeze register and the `CTRL.STICKY` clear

This module is the independent specification of the three control cones that the
core-queue cut (`Metronome.CoreQueue`) takes as free per-cycle inputs:

* `cw`, the picked 15-bit `CW` write group (`w_cw` in [project.v](../../src/project.v)),
  so that the queue's `CW.D` / `CW.AL` / `CW.AH` decode becomes a statement
  about issued moves;
* `frz`, the freeze flag that gates the queue's drain and the cores;
* the `CTRL.STICKY` clear leaf `c_wr_stk & h_wd[2]`.

Everything here is written from SPEC_V2 §6 (write groups), §9 (`CTRL.STICKY`)
and §12.3 (freeze and single-cycle step), not from the RTL.  The RTL side lives
in `CoreCtlEquivalence.lean.in`, which `corectl_check.py` fills from the
elaborated netlist: it extracts each cone as a Lean function of named free
inputs, proves the extracted fields equal to the specification below, and then
instantiates the queue theorems with the specification's values.

## Cycle boundary

`stateAt inputs n` is the register state during chip cycle `n`, after `n`
sampled edges, exactly as in `Metronome.CoreQueue`.
-/

set_option autoImplicit false

namespace Metronome.CoreCtl

/-! ## Bits and slices -/

/-- One net bit as a `Bool`, the shape of a scalar RTL operand. -/
def bitAt {w : Nat} (x : BitVec w) (i : Nat) : Bool :=
  ((BitVec.truncate 1 (BitVec.ushiftRight x i)) != 0)

/-- Bits `off … off+w-1` of `x`, the shape the RTL adapter emits for a bus slice. -/
def slice {n : Nat} (x : BitVec n) (off w : Nat) : BitVec w :=
  BitVec.truncate w (BitVec.ushiftRight x off)

/-! ## The write-group pick (SPEC_V2 §6)

SPEC_V2 §6 partitions the destination ports into write groups and states that
when two or more enabled moves target one group in a cycle, sticky `CONFLICT`
becomes set and only the write with the lowest `(core, move index)` takes
effect.  The move bus is six moves wide (two cores, three moves each) in that
priority order, so "lowest `(core, move index)`" is "lowest index".

The RTL builds the pick as `pick(hits(mv_en, grp, G), c_dst, c_dat)`: `hits`
marks the first enabled move whose destination is in group `G`, and `pick`
OR-selects that move's `{1, dst, data}` word.
-/

/-- One move at the write-group arbiter, as the core pipeline presents it. -/
structure Move where
  /-- `mv_en`: the move's guard held this cycle. -/
  enabled : Bool
  /-- `grp`: the move's write group, from the destination map. -/
  group : BitVec 5
  /-- `c_dst`: the move's destination code. -/
  dst : BitVec 6
  /-- `c_dat`: the move's write data. -/
  data : BitVec 8

/-- The six moves of a cycle, in priority order: core 0 moves 0..2, then core 1.
Written as a structure rather than a `Fin 6 → Move` function so the priority
chain's six selectors are ordinary projections. -/
structure Bundle where
  m0 : Move
  m1 : Move
  m2 : Move
  m3 : Move
  m4 : Move
  m5 : Move

/-- The bundle carried by the elaborated nets `mv_en`, `grp_v`, `c_dst`, `c_dat`:
one move per six-bit destination slice and eight-bit data slice. -/
def bundle (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) (dat : BitVec 48) : Bundle :=
  { m0 := ⟨bitAt en 0, slice grp 0 5, slice dst 0 6, slice dat 0 8⟩
    m1 := ⟨bitAt en 1, slice grp 5 5, slice dst 6 6, slice dat 8 8⟩
    m2 := ⟨bitAt en 2, slice grp 10 5, slice dst 12 6, slice dat 16 8⟩
    m3 := ⟨bitAt en 3, slice grp 15 5, slice dst 18 6, slice dat 24 8⟩
    m4 := ⟨bitAt en 4, slice grp 20 5, slice dst 24 6, slice dat 32 8⟩
    m5 := ⟨bitAt en 5, slice grp 25 5, slice dst 30 6, slice dat 40 8⟩ }

/-- One move competes for group `want`: it is enabled and its destination is in
that group.  This is one bit of the RTL's `hits` vector before the priority
mask. -/
def contenderAt (m : Move) (want : BitVec 5) : Bool :=
  m.enabled && (m.group == want)

/-- The 15-bit group word `{we, dst[5:0], data[7:0]}`: the RTL's `w_cw`. -/
def makeWord (we : Bool) (dst : BitVec 6) (data : BitVec 8) : BitVec 15 :=
  (if we then (1 : BitVec 15) <<< 14 else 0) ||| (dst.setWidth 15 <<< 8) |||
    data.setWidth 15

/-- The `we` bit of a group word. -/
def wordWE (w : BitVec 15) : Bool := bitAt w 14

/-- The destination code `w[13:8]` of a group word. -/
def wordDst (w : BitVec 15) : BitVec 6 := slice w 8 6

/-- The data byte `w[7:0]` of a group word. -/
def wordData (w : BitVec 15) : BitVec 8 := slice w 0 8

theorem makeWord_we (we : Bool) (dst : BitVec 6) (data : BitVec 8) :
    wordWE (makeWord we dst data) = we := by
  unfold makeWord wordWE bitAt
  bv_decide

theorem makeWord_dst (we : Bool) (dst : BitVec 6) (data : BitVec 8) :
    wordDst (makeWord we dst data) = dst := by
  unfold makeWord wordDst slice
  bv_decide

theorem makeWord_data (we : Bool) (dst : BitVec 6) (data : BitVec 8) :
    wordData (makeWord we dst data) = data := by
  unfold makeWord wordData slice
  bv_decide

/-- The three fields determine the word: the RTL packs exactly `{we, dst, data}`. -/
theorem makeWord_fields (w : BitVec 15) :
    makeWord (wordWE w) (wordDst w) (wordData w) = w := by
  unfold makeWord wordWE wordDst wordData bitAt slice
  bv_decide

/-! ### The priority chain

`chain` is the specification of one write group: the first selector that is
true chooses its value, and no selector gives zero.  Every write group uses this
same chain. -/

/-- The priority chain of one write group: the first true selector wins. -/
def chain {w : Nat} (c0 c1 c2 c3 c4 c5 : Bool) (w0 w1 w2 w3 w4 w5 : BitVec w) : BitVec w :=
  if c0 then w0 else if c1 then w1 else if c2 then w2
  else if c3 then w3 else if c4 then w4 else if c5 then w5 else 0

theorem chain_none {w : Nat} (c0 c1 c2 c3 c4 c5 : Bool) (w0 w1 w2 w3 w4 w5 : BitVec w)
    (h0 : c0 = false) (h1 : c1 = false) (h2 : c2 = false)
    (h3 : c3 = false) (h4 : c4 = false) (h5 : c5 = false) :
    chain c0 c1 c2 c3 c4 c5 w0 w1 w2 w3 w4 w5 = 0 := by
  simp [chain, h0, h1, h2, h3, h4, h5]

theorem chain_at_0 {w : Nat} (c0 c1 c2 c3 c4 c5 : Bool) (w0 w1 w2 w3 w4 w5 : BitVec w)
    (h0 : c0 = true) :
    chain c0 c1 c2 c3 c4 c5 w0 w1 w2 w3 w4 w5 = w0 := by
  simp [chain, h0]

theorem chain_at_1 {w : Nat} (c0 c1 c2 c3 c4 c5 : Bool) (w0 w1 w2 w3 w4 w5 : BitVec w)
    (h0 : c0 = false) (h1 : c1 = true) :
    chain c0 c1 c2 c3 c4 c5 w0 w1 w2 w3 w4 w5 = w1 := by
  simp [chain, h0, h1]

theorem chain_at_2 {w : Nat} (c0 c1 c2 c3 c4 c5 : Bool) (w0 w1 w2 w3 w4 w5 : BitVec w)
    (h0 : c0 = false) (h1 : c1 = false) (h2 : c2 = true) :
    chain c0 c1 c2 c3 c4 c5 w0 w1 w2 w3 w4 w5 = w2 := by
  simp [chain, h0, h1, h2]

theorem chain_at_3 {w : Nat} (c0 c1 c2 c3 c4 c5 : Bool) (w0 w1 w2 w3 w4 w5 : BitVec w)
    (h0 : c0 = false) (h1 : c1 = false) (h2 : c2 = false) (h3 : c3 = true) :
    chain c0 c1 c2 c3 c4 c5 w0 w1 w2 w3 w4 w5 = w3 := by
  simp [chain, h0, h1, h2, h3]

theorem chain_at_4 {w : Nat} (c0 c1 c2 c3 c4 c5 : Bool) (w0 w1 w2 w3 w4 w5 : BitVec w)
    (h0 : c0 = false) (h1 : c1 = false) (h2 : c2 = false) (h3 : c3 = false) (h4 : c4 = true) :
    chain c0 c1 c2 c3 c4 c5 w0 w1 w2 w3 w4 w5 = w4 := by
  simp [chain, h0, h1, h2, h3, h4]

theorem chain_at_5 {w : Nat} (c0 c1 c2 c3 c4 c5 : Bool) (w0 w1 w2 w3 w4 w5 : BitVec w)
    (h0 : c0 = false) (h1 : c1 = false) (h2 : c2 = false) (h3 : c3 = false)
    (h4 : c4 = false) (h5 : c5 = true) :
    chain c0 c1 c2 c3 c4 c5 w0 w1 w2 w3 w4 w5 = w5 := by
  simp [chain, h0, h1, h2, h3, h4, h5]

/-! ### The write a group presents -/

/-- The 15-bit group word as its three fields.  A group with no contender writes
`⟨false, 0, 0⟩`, which the RTL presents as `we = 0`. -/
structure GroupWord where
  /-- `w_cw[14]`: a move won the group. -/
  we : Bool
  /-- `w_cw[13:8]`: the winning destination code. -/
  dst : BitVec 6
  /-- `w_cw[7:0]`: the winning data byte. -/
  data : BitVec 8
  deriving DecidableEq, Repr

@[ext] theorem GroupWord.ext {a b : GroupWord} (we : a.we = b.we) (dst : a.dst = b.dst)
    (data : a.data = b.data) : a = b := by
  obtain ⟨⟩ := a
  obtain ⟨⟩ := b
  simp_all

/-- The RTL's packed form of a group word. -/
def GroupWord.pack (w : GroupWord) : BitVec 15 :=
  makeWord w.we w.dst w.data

/-- At least one move contends for the group: the RTL's `|hits`, the `we` bit. -/
def anyContender (b : Bundle) (want : BitVec 5) : Bool :=
  contenderAt b.m0 want || contenderAt b.m1 want || contenderAt b.m2 want ||
  contenderAt b.m3 want || contenderAt b.m4 want || contenderAt b.m5 want

/-- SPEC_V2 §6: the write one group presents.  The first contender in priority
order supplies `dst` and `data`; `we` says whether any move contended. -/
def word (b : Bundle) (want : BitVec 5) : GroupWord where
  we := anyContender b want
  dst := chain (contenderAt b.m0 want) (contenderAt b.m1 want) (contenderAt b.m2 want)
    (contenderAt b.m3 want) (contenderAt b.m4 want) (contenderAt b.m5 want)
    b.m0.dst b.m1.dst b.m2.dst b.m3.dst b.m4.dst b.m5.dst
  data := chain (contenderAt b.m0 want) (contenderAt b.m1 want) (contenderAt b.m2 want)
    (contenderAt b.m3 want) (contenderAt b.m4 want) (contenderAt b.m5 want)
    b.m0.data b.m1.data b.m2.data b.m3.data b.m4.data b.m5.data

theorem word_we (b : Bundle) (want : BitVec 5) : (word b want).we = anyContender b want :=
  rfl

theorem word_we_of_hit (b : Bundle) (want : BitVec 5) (hit : anyContender b want = true) :
    (word b want).we = true :=
  hit

/-- No move contends for the group: the group is written zero. -/
theorem word_none (b : Bundle) (want : BitVec 5)
    (h0 : contenderAt b.m0 want = false) (h1 : contenderAt b.m1 want = false)
    (h2 : contenderAt b.m2 want = false) (h3 : contenderAt b.m3 want = false)
    (h4 : contenderAt b.m4 want = false) (h5 : contenderAt b.m5 want = false) :
    word b want = ⟨false, 0, 0⟩ := by
  apply GroupWord.ext <;> simp [word, anyContender, chain, h0, h1, h2, h3, h4, h5]

/-- A unique contender, at move 0: the group word is that move's. -/
theorem word_unique_0 (b : Bundle) (want : BitVec 5)
    (hit : contenderAt b.m0 want = true) :
    word b want = ⟨true, b.m0.dst, b.m0.data⟩ := by
  apply GroupWord.ext <;> simp [word, anyContender, chain, hit]

theorem word_unique_1 (b : Bundle) (want : BitVec 5)
    (no0 : contenderAt b.m0 want = false) (hit : contenderAt b.m1 want = true) :
    word b want = ⟨true, b.m1.dst, b.m1.data⟩ := by
  apply GroupWord.ext <;> simp [word, anyContender, chain, no0, hit]

theorem word_unique_2 (b : Bundle) (want : BitVec 5)
    (no0 : contenderAt b.m0 want = false) (no1 : contenderAt b.m1 want = false)
    (hit : contenderAt b.m2 want = true) :
    word b want = ⟨true, b.m2.dst, b.m2.data⟩ := by
  apply GroupWord.ext <;> simp [word, anyContender, chain, no0, no1, hit]

theorem word_unique_3 (b : Bundle) (want : BitVec 5)
    (no0 : contenderAt b.m0 want = false) (no1 : contenderAt b.m1 want = false)
    (no2 : contenderAt b.m2 want = false) (hit : contenderAt b.m3 want = true) :
    word b want = ⟨true, b.m3.dst, b.m3.data⟩ := by
  apply GroupWord.ext <;> simp [word, anyContender, chain, no0, no1, no2, hit]

theorem word_unique_4 (b : Bundle) (want : BitVec 5)
    (no0 : contenderAt b.m0 want = false) (no1 : contenderAt b.m1 want = false)
    (no2 : contenderAt b.m2 want = false) (no3 : contenderAt b.m3 want = false)
    (hit : contenderAt b.m4 want = true) :
    word b want = ⟨true, b.m4.dst, b.m4.data⟩ := by
  apply GroupWord.ext <;> simp [word, anyContender, chain, no0, no1, no2, no3, hit]

theorem word_unique_5 (b : Bundle) (want : BitVec 5)
    (no0 : contenderAt b.m0 want = false) (no1 : contenderAt b.m1 want = false)
    (no2 : contenderAt b.m2 want = false) (no3 : contenderAt b.m3 want = false)
    (no4 : contenderAt b.m4 want = false) (hit : contenderAt b.m5 want = true) :
    word b want = ⟨true, b.m5.dst, b.m5.data⟩ := by
  apply GroupWord.ext <;> simp [word, anyContender, chain, no0, no1, no2, no3, no4, hit]

/-! ## The freeze register (SPEC_V2 §12.3)

SPEC_V2 §12.3: state `FREEZE` (the host bit), `FRZ` (this cycle is frozen) and
`FRZD` (`FRZ` of the previous cycle).  A host write of `DBG` with byte `d` sets
`FREEZE' = d[0]` and `FRZ' = d[0] && !d[1]`; without a `DBG` write,
`FRZ' = FREEZE`; always `FRZD' = FRZ`.  Reset clears all three.

So `DBG <- 0x01` freezes from the next cycle, `DBG <- 0x03` (STEP) runs exactly
one cycle and freezes again, and `DBG <- 0x00` (or `0x02`) releases the freeze.
-/

/-- `FREEZE`, `FRZ` and `FRZD` from SPEC_V2 §12.3. -/
structure FreezeState where
  /-- `FREEZE`: the host freeze bit. -/
  freeze : Bool
  /-- `FRZ`: this cycle is frozen. -/
  frz : Bool
  /-- `FRZD`: `FRZ` of the previous cycle. -/
  frzd : Bool
  deriving DecidableEq, Repr

@[ext] theorem FreezeState.ext {a b : FreezeState} (freeze : a.freeze = b.freeze)
    (frz : a.frz = b.frz) (frzd : a.frzd = b.frzd) : a = b := by
  obtain ⟨⟩ := a
  obtain ⟨⟩ := b
  simp_all

/-- The sampled inputs of the freeze cone: reset, the `DBG` write strobe and the
host data byte. -/
structure FreezeInput where
  resetN : Bool
  /-- `d_wr_dbg`: a host write to `DBG.DBG`. -/
  dbgWrite : Bool
  /-- `h_wd`: the host data byte. -/
  data : BitVec 8
  deriving DecidableEq, Repr

/-- Reset value: not frozen, and no frozen cycle. -/
def freezeReset : FreezeState := ⟨false, false, false⟩

/-- The `DBG` write byte's freeze bit, `d[0]`. -/
def freezeBit (i : FreezeInput) : Bool := bitAt i.data 0

/-- The `DBG` write byte's step bit, `d[1]`. -/
def stepBit (i : FreezeInput) : Bool := bitAt i.data 1

/-- SPEC_V2 §12.3's transition. -/
def freezeStep (s : FreezeState) (i : FreezeInput) : FreezeState where
  freeze := if i.resetN then (if i.dbgWrite then freezeBit i else s.freeze) else false
  frz := if i.resetN then (if i.dbgWrite then (freezeBit i && !stepBit i) else s.freeze) else false
  frzd := if i.resetN then s.frz else false

theorem freeze_next (s : FreezeState) (i : FreezeInput) :
    (freezeStep s i).freeze =
      if i.resetN then (if i.dbgWrite then freezeBit i else s.freeze) else false := rfl

theorem frz_next (s : FreezeState) (i : FreezeInput) :
    (freezeStep s i).frz =
      if i.resetN then (if i.dbgWrite then (freezeBit i && !stepBit i) else s.freeze)
      else false := rfl

theorem frzd_next (s : FreezeState) (i : FreezeInput) :
    (freezeStep s i).frzd = if i.resetN then s.frz else false := rfl

/-- Reset clears the freeze registers. -/
theorem freezeStep_reset (s : FreezeState) (i : FreezeInput) (h : i.resetN = false) :
    freezeStep s i = freezeReset := by
  apply FreezeState.ext <;> simp [freezeStep, freezeReset, h]

/-- A `DBG` write of `0x01` freezes from the next cycle. -/
theorem frz_of_freeze_write (s : FreezeState) (i : FreezeInput)
    (reset : i.resetN = true) (wr : i.dbgWrite = true) (bit : freezeBit i = true)
    (notStep : stepBit i = false) :
    (freezeStep s i).frz = true ∧ (freezeStep s i).freeze = true := by
  simp [freezeStep, reset, wr, bit, notStep]

/-- A `DBG` write of `0x03` (STEP) runs exactly this cycle: `FRZ` is clear and
`FREEZE` stays set, so the cycle after it is frozen again. -/
theorem frz_of_step_write (s : FreezeState) (i : FreezeInput)
    (reset : i.resetN = true) (wr : i.dbgWrite = true) (bit : freezeBit i = true)
    (step : stepBit i = true) :
    (freezeStep s i).frz = false ∧ (freezeStep s i).freeze = true := by
  simp [freezeStep, reset, wr, bit, step]

/-- A `DBG` write with bit 0 clear releases the freeze, and clears `FREEZE`. -/
theorem frz_of_release_write (s : FreezeState) (i : FreezeInput)
    (reset : i.resetN = true) (wr : i.dbgWrite = true) (bit : freezeBit i = false) :
    (freezeStep s i).frz = false ∧ (freezeStep s i).freeze = false := by
  simp [freezeStep, reset, wr, bit]

/-- Without a `DBG` write, `FRZ` follows `FREEZE`: a frozen machine stays frozen
and an unfrozen one stays running. -/
theorem frz_holds (s : FreezeState) (i : FreezeInput)
    (reset : i.resetN = true) (wr : i.dbgWrite = false) :
    (freezeStep s i).frz = s.freeze ∧ (freezeStep s i).freeze = s.freeze := by
  simp [freezeStep, reset, wr]

/-- One cycle of the freeze cone in isolation: a reset or a `DBG` write whose
freeze bit is clear keeps (or makes) the machine unfrozen. -/
theorem freeze_low_step (s : FreezeState) (i : FreezeInput)
    (reset : i.resetN = true) (low : s.freeze = false)
    (noTrigger : ¬ ((i.dbgWrite = true) ∧ (freezeBit i = true))) :
    (freezeStep s i).freeze = false ∧ (freezeStep s i).frz = false := by
  by_cases wr : i.dbgWrite = true
  · have bit : freezeBit i = false := by
      by_cases b : freezeBit i = true
      · exact absurd ⟨wr, b⟩ noTrigger
      · simpa using b
    simp [freezeStep, reset, wr, bit]
  · simp [freezeStep, reset, wr, low]

/-! ### Trace lift -/

def stateAt (inputs : Nat → FreezeInput) (n : Nat) : FreezeState :=
  run (fun s i => freezeStep s i) inputs freezeReset n

theorem stateAt_succ (inputs : Nat → FreezeInput) (n : Nat) :
    stateAt inputs (n + 1) = freezeStep (stateAt inputs n) (inputs n) := rfl

theorem stateAt_zero (inputs : Nat → FreezeInput) : stateAt inputs 0 = freezeReset := rfl

/-- Starting from reset, `FRZ` is low until the first `DBG` write that sets its
freeze bit: neither a running machine nor a `STEP` can raise it. -/
theorem trace_freeze_low (inputs : Nat → FreezeInput) :
    ∀ n, (∀ k, k < n → (inputs k).resetN = true) →
      (∀ k, k < n → ¬ ((inputs k).dbgWrite = true ∧ freezeBit (inputs k) = true)) →
      (stateAt inputs n).freeze = false ∧ (stateAt inputs n).frz = false := by
  intro n
  induction n with
  | zero => intro _ _; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro noReset noTrigger
    have low := ih (fun k lt => noReset k (by omega))
      (fun k lt => noTrigger k (by omega))
    rw [stateAt_succ]
    exact freeze_low_step _ _ (noReset n (by omega)) low.1 (noTrigger n (by omega))

/-- After a `DBG` write with bit 0 set, the next cycle is frozen, whatever the
state was before. -/
theorem trace_frz_of_trigger (inputs : Nat → FreezeInput) (m : Nat)
    (reset : (inputs m).resetN = true) (wr : (inputs m).dbgWrite = true)
    (bit : freezeBit (inputs m) = true) (notStep : stepBit (inputs m) = false) :
    (stateAt inputs (m + 1)).frz = true := by
  rw [stateAt_succ]
  exact (frz_of_freeze_write _ _ reset wr bit notStep).1

/-- A `STEP` write runs exactly one cycle: the next cycle is unfrozen and the
one after it is frozen again, provided the step cycle has no `DBG` write. -/
theorem trace_frz_one_cycle (inputs : Nat → FreezeInput) (m : Nat)
    (reset : (inputs m).resetN = true) (wr : (inputs m).dbgWrite = true)
    (bit : freezeBit (inputs m) = true) (step : stepBit (inputs m) = true)
    (nextReset : (inputs (m + 1)).resetN = true)
    (nextNoWrite : (inputs (m + 1)).dbgWrite = false) :
    (stateAt inputs (m + 1)).frz = false ∧ (stateAt inputs (m + 2)).frz = true := by
  have stepped := frz_of_step_write (stateAt inputs m) (inputs m) reset wr bit step
  refine ⟨?_, ?_⟩
  · rw [stateAt_succ]
    exact stepped.1
  · rw [show m + 2 = (m + 1) + 1 by omega, stateAt_succ]
    exact (frz_holds _ _ nextReset nextNoWrite).1.trans stepped.2

/-! ## The `CTRL.STICKY` clear (SPEC_V2 §9, §13.1)

`CTRL.STICKY` is a write-one-to-clear byte: bit 0 `CONFLICT`, bit 1 `MEMHAZ`,
bit 2 `CWOVR` (`project.v`'s readback `{5'd0, cw_overrun, memhaz, conflict}` and
SPEC_V2 §13.1's `CTRL.STICKY` bit 2).  The RTL forms the clear leaf as
`c_wr_stk & h_wd[2]`, where `c_wr_stk = w_ctl & (o_ctl == HO_CTRL_STICKY)` and
`w_ctl = h_wr & in_ctl`: a host write of byte `d` to the `STICKY` offset with
`d[2]` set.
-/

/-- The `CWOVR` clear: a host write of byte `d` to `stickyAddr` with bit 2 set.
The address decode is what makes `wr && addr == stickyAddr` the `CTRL.STICKY`
write. -/
def stickyLeaf (wr : Bool) (addr : BitVec 16) (stickyAddr : BitVec 16) (d : BitVec 8) : Bool :=
  wr && (addr == stickyAddr) && bitAt d 2

theorem stickyLeaf_spec (wr : Bool) (addr : BitVec 16) (stickyAddr : BitVec 16)
    (d : BitVec 8) :
    stickyLeaf wr addr stickyAddr d = true ↔
      (wr = true ∧ addr = stickyAddr ∧ bitAt d 2 = true) := by
  unfold stickyLeaf
  simp [Bool.and_eq_true, and_assoc]

/-- Clearing needs the byte's bit 2: a `STICKY` write of `0x01` or `0x02`
leaves `CWOVR` alone. -/
theorem stickyLeaf_no_clear (wr : Bool) (addr : BitVec 16) (stickyAddr : BitVec 16)
    (d : BitVec 8) (bit : bitAt d 2 = false) :
    stickyLeaf wr addr stickyAddr d = false := by
  simp [stickyLeaf, bit]

/-- A write to any other address does not clear `CWOVR`. -/
theorem stickyLeaf_other_addr (wr : Bool) (addr : BitVec 16) (stickyAddr : BitVec 16)
    (d : BitVec 8) (other : addr ≠ stickyAddr) :
    stickyLeaf wr addr stickyAddr d = false := by
  simp [stickyLeaf, other]

/-! ## Concrete witnesses

These pin down the two cases the pick turns on: with two contenders the lower
move index wins (SPEC_V2 §6's conflict resolution), and with none the group word
is zero. -/

/-- Two contenders for one group: the lower move index wins and the later move's
data is not written. -/
theorem two_contenders_first_wins :
    let b : Bundle :=
      { m0 := ⟨true, 25, 60, 0x11⟩
        m1 := ⟨true, 25, 60, 0x22⟩
        m2 := ⟨false, 31, 0, 0⟩
        m3 := ⟨false, 31, 0, 0⟩
        m4 := ⟨false, 31, 0, 0⟩
        m5 := ⟨false, 31, 0, 0⟩ }
    word b 25 = ⟨true, 60, 0x11⟩ := by
  decide

/-- No contender: the group is written zero. -/
theorem no_contender_zero :
    let b : Bundle :=
      { m0 := ⟨false, 31, 0, 0⟩
        m1 := ⟨false, 31, 0, 0⟩
        m2 := ⟨false, 31, 0, 0⟩
        m3 := ⟨false, 31, 0, 0⟩
        m4 := ⟨false, 31, 0, 0⟩
        m5 := ⟨false, 31, 0, 0⟩ }
    word b 25 = ⟨false, 0, 0⟩ := by
  decide

end Metronome.CoreCtl
