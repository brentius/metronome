/-!
# Latch-bank specification and write step

An independent specification of the Metronome v4 configuration latch bank
(`md2_cfg_cells` in `src/md2_cfg_bank.v`), its masked read value and its write
step. Nothing here is extracted from the netlist.

The state is the raw latch content, one byte per window offset, plus the
elaborated `MASK` parameter. `read` is what a reader observes: the latch outputs
masked with `MASK`, and zero in the bits without a latch (the RTL ties those
bits to zero).

Timing abstraction (stated assumption). `md2_cfg_bank.v` samples `we`/`waddr`/
`wdata` at rising edge E1, and the selected byte's gated clock opens after
E2 = E1 + 1 cycle, so the new value is visible from W+2. This module models the
result as one atomic transparency `phase`: an open gate passes `data1`, a closed
gate holds. Out of scope, and therefore not proved here: the clock gate's own
latency, latch hold/setup behaviour, clock skew, the E1/E2 separation, and the
spacing rule that `we` is never high on consecutive edges. Those are RTL and
physical-timing obligations.

The link from this model to the netlist is `bank_check.py` (structure: which
gate and latches exist per mask byte, and which data/output/reset nets they use)
plus the generated `Metronome.BankEquivalence` module (Boolean: every extracted
gate enable is exactly `gateOpen` on the live bytes and `false` on the mask-zero
bytes). `phase_read_of_live_gates` composes the two, and `write_exact` is the
resulting write contract. `step_of_gates` states the same bridge for an ideal
family whose gates exist at every offset.
-/

namespace Metronome.Bank

/-- Bytes in the shared configuration window (`CFG_BYTES` in `md2_map.vh`). -/
abbrev BYTES : Nat := 480

/-- Latch-bank state: the elaborated mask and the raw latch content. -/
structure State where
  /-- The `MASK` parameter, one byte per window offset. -/
  mask : Fin BYTES → BitVec 8
  /-- Raw latch content. Only the bits selected by `mask` are real latches. -/
  latch : Fin BYTES → BitVec 8

/-- The nine-bit bank offset of byte `k`. -/
def addrOf (k : Fin BYTES) : BitVec 9 := BitVec.ofNat 9 k.val

/-- The bank value a reader observes: masked latch outputs, zero elsewhere. -/
def read (s : State) : Fin BYTES → BitVec 8 := fun k => s.latch k &&& s.mask k

/-- The gate condition of byte `k` for the staged write word `(we1, addr1)`.
This is the arithmetic rule the elaborated per-byte comparator must implement.
Bytes with a zero mask byte have no clock gate at all; their latch content is
unobservable (`read_zero`) and their bookkeeping gate is irrelevant. -/
def gateOpen (we1 : Bool) (addr1 : BitVec 9) (k : Fin BYTES) : Bool :=
  we1 && (addr1 == addrOf k)

/-- One latch transparency phase: each open gate passes `data1`, closed gates
hold. See the module comment for the timing abstraction this stands for. -/
def phase (s : State) (en : Fin BYTES → Bool) (data1 : BitVec 8) : State where
  mask := s.mask
  latch := fun k => if en k then data1 else s.latch k

/-- The specified write step, with the arithmetic per-byte gate condition. -/
def step (s : State) (we1 : Bool) (addr1 : BitVec 9) (data1 : BitVec 8) : State :=
  phase s (fun k => gateOpen we1 addr1 k) data1

/-! ## Arithmetic facts about the byte offset -/

theorem addrOf_injective : Function.Injective addrOf := by
  intro a b h
  apply Fin.ext
  have hnat : a.val % 2 ^ 9 = b.val % 2 ^ 9 := by
    simpa [addrOf] using congrArg BitVec.toNat h
  rw [show 2 ^ 9 = 512 by decide] at hnat
  have ha : a.val < 512 := Nat.lt_trans a.isLt (by decide)
  have hb : b.val < 512 := Nat.lt_trans b.isLt (by decide)
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hnat

theorem addrOf_ne {j k : Fin BYTES} (h : j ≠ k) : addrOf j ≠ addrOf k :=
  fun heq => h (addrOf_injective heq)

theorem gateOpen_eq_true {we1 : Bool} {addr1 : BitVec 9} {k : Fin BYTES} :
    gateOpen we1 addr1 k = true ↔ we1 = true ∧ addr1 = addrOf k := by
  rw [gateOpen, Bool.and_eq_true_iff, beq_iff_eq]

/-- At most one gate can be open at a time: two open gates would force the same
`addr1` for two different byte offsets. -/
theorem gateOpen_not_both (k j : Fin BYTES) (h : k ≠ j) (we1 : Bool)
    (addr1 : BitVec 9) :
    ¬ (gateOpen we1 addr1 k = true ∧ gateOpen we1 addr1 j = true) := by
  rintro ⟨hk, hj⟩
  rw [gateOpen_eq_true] at hk hj
  exact h (addrOf_injective (hk.2.symm.trans hj.2))

/-- The `Bool` form of `gateOpen_not_both`: two distinct gates never enable
together, so at most one byte of the bank can change in a write phase. -/
theorem gateOpen_exclusive (k j : Fin BYTES) (h : k ≠ j) (we1 : Bool)
    (addr1 : BitVec 9) :
    (gateOpen we1 addr1 k && gateOpen we1 addr1 j) = false := by
  cases hall : (gateOpen we1 addr1 k && gateOpen we1 addr1 j)
  · rfl
  · exact absurd (Bool.and_eq_true_iff.mp hall) (gateOpen_not_both k j h we1 addr1)

/-- A gate other than the addressed one stays closed. -/
theorem gateOpen_other {k j : Fin BYTES} (h : j ≠ k) (we1 : Bool) :
    gateOpen we1 (addrOf k) j = false := by
  cases hw : we1
  · simp [gateOpen]
  · cases hb : (addrOf k == addrOf j)
    · simp [gateOpen, hb]
    · exact absurd (beq_iff_eq.mp hb) (addrOf_ne (Ne.symm h))

/-! ## The write step -/

/-- A zero mask byte reads zero, so its latch content is unobservable. -/
theorem read_zero (s : State) (k : Fin BYTES) (h : s.mask k = 0) :
    read s k = 0 := by
  simp [read, h]

/-- Bits outside the mask byte read zero, before and after any write. -/
theorem read_unmasked (s : State) (k : Fin BYTES) (b : Nat)
    (h : (s.mask k).getLsbD b = false) : (read s k).getLsbD b = false := by
  simp [read, h]

/-- The observable value of byte `k` after a phase. -/
theorem phase_read (s : State) (en : Fin BYTES → Bool) (data1 : BitVec 8)
    (k : Fin BYTES) :
    read (phase s en data1) k =
      if en k then data1 &&& s.mask k else read s k := by
  by_cases h : en k <;> simp [read, phase, h]

/-- The observable value of byte `k` after the specified write step. -/
theorem step_read (s : State) (we1 : Bool) (addr1 : BitVec 9) (data1 : BitVec 8)
    (k : Fin BYTES) :
    read (step s we1 addr1 data1) k =
      if gateOpen we1 addr1 k then data1 &&& s.mask k else read s k :=
  phase_read s _ data1 k

/-- An issued write to byte `k` sets exactly the masked bits of byte `k` to
`data1 & MASK` and leaves every other byte unchanged. Bits outside the mask
read zero before and after, so they are untouched as well. -/
theorem write_exact (s : State) (k : Fin BYTES) (data1 : BitVec 8) :
    read (step s true (addrOf k) data1) k = data1 &&& s.mask k ∧
      (∀ j : Fin BYTES, j ≠ k →
        read (step s true (addrOf k) data1) j = read s j) := by
  have hopen : gateOpen true (addrOf k) k = true := by
    rw [gateOpen_eq_true]
    exact ⟨rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [step_read]
    simp [hopen]
  · intro j hjk
    rw [step_read]
    simp [gateOpen_other hjk]

/-- Each bit selected by the mask byte of the written offset takes the staged
data bit after an issued write. -/
theorem write_bit (s : State) (k : Fin BYTES) (data1 : BitVec 8) (b : Nat)
    (h : (s.mask k).getLsbD b = true) :
    (read (step s true (addrOf k) data1) k).getLsbD b = data1.getLsbD b := by
  rw [(write_exact s k data1).1]
  simp [h]

/-- A write to an offset whose mask byte is zero changes nothing, for any
strobe and data. -/
theorem write_mask_zero (s : State) (k : Fin BYTES) (hzero : s.mask k = 0)
    (we1 : Bool) (data1 : BitVec 8) :
    read (step s we1 (addrOf k) data1) = read s := by
  funext j
  by_cases hjk : j = k
  · have hzero' : s.mask j = 0 := by rw [hjk]; exact hzero
    have hread : read s j = 0 := read_zero s j hzero'
    rw [step_read]
    by_cases h : gateOpen we1 (addrOf k) j <;> simp [h, hzero', hread]
  · rw [step_read, gateOpen_other hjk we1]
    simp

/-! ## Bridge from the extracted gate family -/

/-- If every gate of the elaborated bank implements `gateOpen` (checked per
byte by `Metronome.BankEquivalence`), a transparency phase equals the
specified write step. -/
theorem step_of_gates (s : State) (rtlEn : Fin BYTES → Bool → BitVec 9 → Bool)
    (hmatch : ∀ k we1 addr1, rtlEn k we1 addr1 = gateOpen we1 addr1 k)
    (we1 : Bool) (addr1 : BitVec 9) (data1 : BitVec 8) :
    phase s (fun k => rtlEn k we1 addr1) data1 = step s we1 addr1 data1 := by
  rw [show (fun k => rtlEn k we1 addr1) = (fun k => gateOpen we1 addr1 k) from
    funext (fun k => hmatch k we1 addr1)]
  rfl

/-- `write_exact` for a gate family extracted from the netlist. -/
theorem write_exact_of_gates (s : State)
    (rtlEn : Fin BYTES → Bool → BitVec 9 → Bool)
    (hmatch : ∀ k we1 addr1, rtlEn k we1 addr1 = gateOpen we1 addr1 k)
    (k : Fin BYTES) (data1 : BitVec 8) :
    read (phase s (fun j => rtlEn j true (addrOf k)) data1) k = data1 &&& s.mask k := by
  rw [step_of_gates s rtlEn hmatch]
  exact (write_exact s k data1).1

/-- `write_exact` for the extracted gates: every other byte is unchanged. -/
theorem write_others_of_gates (s : State)
    (rtlEn : Fin BYTES → Bool → BitVec 9 → Bool)
    (hmatch : ∀ k we1 addr1, rtlEn k we1 addr1 = gateOpen we1 addr1 k)
    (k j : Fin BYTES) (h : j ≠ k) (data1 : BitVec 8) :
    read (phase s (fun i => rtlEn i true (addrOf k)) data1) j = read s j := by
  rw [step_of_gates s rtlEn hmatch]
  exact (write_exact s k data1).2 j h

/-- `write_mask_zero` for a gate family extracted from the netlist. -/
theorem write_mask_zero_of_gates (s : State)
    (rtlEn : Fin BYTES → Bool → BitVec 9 → Bool)
    (hmatch : ∀ k we1 addr1, rtlEn k we1 addr1 = gateOpen we1 addr1 k)
    (k : Fin BYTES) (hzero : s.mask k = 0) (we1 : Bool) (data1 : BitVec 8) :
    read (phase s (fun j => rtlEn j we1 (addrOf k)) data1) = read s := by
  rw [step_of_gates s rtlEn hmatch]
  exact write_mask_zero s k hzero we1 data1

/-- The form of the gate family that the netlist actually realises: a mask-zero
byte has no clock gate at all, so its extracted enable is `false`, while
`gateOpen` is still true at that offset. Both agree on every live byte. A
phase of such a family has the specified *read* value, because a mask-zero byte
reads zero before and after (`read_zero`).

This is the hypothesis-free link used by `Metronome.BankEquivalence`: the
elaborated family is closed at the 196 mask-zero offsets and equals `gateOpen`
at the 284 live ones. -/
theorem phase_read_of_live_gates (s : State)
    (rtlEn : Fin BYTES → Bool → BitVec 9 → Bool)
    (hlive : ∀ k we1 addr1, s.mask k ≠ 0 → rtlEn k we1 addr1 = gateOpen we1 addr1 k)
    (hclosed : ∀ k we1 addr1, s.mask k = 0 → rtlEn k we1 addr1 = false)
    (we1 : Bool) (addr1 : BitVec 9) (data1 : BitVec 8) :
    read (phase s (fun k => rtlEn k we1 addr1) data1) = read (step s we1 addr1 data1) := by
  funext k
  rw [phase_read, step_read]
  by_cases hzero : s.mask k = 0
  · rw [hclosed k we1 addr1 hzero, read_zero s k hzero]
    by_cases hg : gateOpen we1 addr1 k <;> simp [hg, hzero]
  · rw [hlive k we1 addr1 hzero]

/-- `write_exact` for a live/hole gate family: an issued write to byte `k` sets
exactly its mask bits to `data1 & MASK`. -/
theorem write_exact_of_live_gates (s : State)
    (rtlEn : Fin BYTES → Bool → BitVec 9 → Bool)
    (hlive : ∀ k we1 addr1, s.mask k ≠ 0 → rtlEn k we1 addr1 = gateOpen we1 addr1 k)
    (hclosed : ∀ k we1 addr1, s.mask k = 0 → rtlEn k we1 addr1 = false)
    (k : Fin BYTES) (data1 : BitVec 8) :
    read (phase s (fun j => rtlEn j true (addrOf k)) data1) k = data1 &&& s.mask k := by
  rw [phase_read_of_live_gates s rtlEn hlive hclosed]
  exact (write_exact s k data1).1

/-- `write_exact` for a live/hole gate family: every other byte is unchanged. -/
theorem write_others_of_live_gates (s : State)
    (rtlEn : Fin BYTES → Bool → BitVec 9 → Bool)
    (hlive : ∀ k we1 addr1, s.mask k ≠ 0 → rtlEn k we1 addr1 = gateOpen we1 addr1 k)
    (hclosed : ∀ k we1 addr1, s.mask k = 0 → rtlEn k we1 addr1 = false)
    (k j : Fin BYTES) (h : j ≠ k) (data1 : BitVec 8) :
    read (phase s (fun i => rtlEn i true (addrOf k)) data1) j = read s j := by
  rw [phase_read_of_live_gates s rtlEn hlive hclosed]
  exact (write_exact s k data1).2 j h

/-- `write_mask_zero` for a live/hole gate family. -/
theorem write_mask_zero_of_live_gates (s : State)
    (rtlEn : Fin BYTES → Bool → BitVec 9 → Bool)
    (hlive : ∀ k we1 addr1, s.mask k ≠ 0 → rtlEn k we1 addr1 = gateOpen we1 addr1 k)
    (hclosed : ∀ k we1 addr1, s.mask k = 0 → rtlEn k we1 addr1 = false)
    (k : Fin BYTES) (hzero : s.mask k = 0) (we1 : Bool) (data1 : BitVec 8) :
    read (phase s (fun j => rtlEn j we1 (addrOf k)) data1) = read s := by
  rw [phase_read_of_live_gates s rtlEn hlive hclosed]
  exact write_mask_zero s k hzero we1 data1

end Metronome.Bank
