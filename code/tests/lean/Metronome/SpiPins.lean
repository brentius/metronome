import Metronome.HostCmd

/-!
# SPI pin layer: pin waveforms to the host command machine

`Metronome.HostCmd` proves the byte-level command machine of `src/md2_host.v`
from per-cycle sampled inputs `sck`, `sckPrev`, `csN` and `mosi`.  This module
closes the layer below it: the chip-top pin synchronisers (`s1`, `s2`, `sp` in
`src/project.v`, SPEC_V2 §2) and a mode-0 SPI pin waveform.

## What is modelled

* `Sync` is the three 16-bit synchroniser registers.  `step` is the SPEC_V2 §2
  equation: with `rst_q` (the sampled `resetN`) high, `s1' = raw`, `s2' = s1`,
  `sp' = s2`; with `rst_q` low all three clear.  `raw = {ui_in, uio_in}`, so
  bit 8 is SCK, bit 9 CS_N and bit 10 MOSI (SPEC_V2 §2, "the host link uses
  `ui_in[0..2]`").
* `hostInput` is the host-link input word derived from the synchronised state.
  The generated `SpiPinsEquivalence.lean.in` cut proves that the elaborated
  `u_host` port wiring is exactly this word.
* A mode-0 SPI clock is a rise every `period` cycles (`srAt`).  The host sees
  a pin level two cycles after the cycle that held it, and `sckPrev` three
  cycles after, so a pin rise held in cycle `n+1` is one `SR` in cycle `n+3`.

## Timing premises

The discrete trace model samples one pin level per clock cycle, so a phase has
to last at least one cycle to be representable: `period ≥ 2` (a high phase of
at least one cycle and a low phase of at least one cycle).  That is the minimum
the proofs need.  SPEC_V2 §9's "keep SCK at or below clk/16" gives `period ≥ 16`
(an 8-cycle half period); the extra margin is a physical setup/hold and
metastability requirement on the asynchronous pins, which the discrete model
does not represent.  The only data premise is that MOSI holds the clocked bit
across the two cycles the edge detector and the sampler read: the cycle of the
rise and the cycle before it (`mosi_stable`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Metronome.SpiPins

/-! ## The pin synchroniser (SPEC_V2 §2) -/

/-- The three 16-bit synchroniser registers `s1`, `s2`, `sp` of
`src/project.v`. -/
structure Sync where
  /-- First synchroniser stage. -/
  s1 : BitVec 16
  /-- Second stage: the synchronised level. -/
  s2 : BitVec 16
  /-- Previous synchronised level, one cycle behind `s2`. -/
  sp : BitVec 16
  deriving DecidableEq, Repr

/-- Two synchroniser states with equal registers are equal. -/
@[ext] theorem Sync.ext {a b : Sync} (h1 : a.s1 = b.s1) (h2 : a.s2 = b.s2)
    (h3 : a.sp = b.sp) : a = b := by
  obtain ⟨x1, x2, x3⟩ := a
  obtain ⟨y1, y2, y3⟩ := b
  simp_all

/-- The sampled synchroniser input: `resetN` is `rst_q`, `hi` is `ui_in` and
`lo` is `uio_in`. -/
structure Input where
  resetN : Bool
  hi : BitVec 8
  lo : BitVec 8
  deriving DecidableEq, Repr

/-- The raw pin word `{ui_in, uio_in}`. -/
def raw (i : Input) : BitVec 16 := i.hi ++ i.lo

/-- The synchroniser input word of a raw pin vector. -/
def pinInput (rst : Bool) (w : BitVec 16) : Input :=
  ⟨rst, (w >>> 8).truncate 8, w.truncate 8⟩

theorem raw_pinInput (rst : Bool) (w : BitVec 16) : raw (pinInput rst w) = w := by
  unfold raw pinInput
  simp
  bv_decide

/-- The state left by a sampled reset edge. -/
def resetState : Sync := ⟨0, 0, 0⟩

/-- SPEC_V2 §2: `s1' = raw`, `s2' = s1`, `sp' = s2`, all cleared while `rst_q`
is low. -/
def step (s : Sync) (i : Input) : Sync :=
  ⟨if i.resetN then raw i else (0 : BitVec 16),
   if i.resetN then s.s1 else (0 : BitVec 16),
   if i.resetN then s.s2 else (0 : BitVec 16)⟩

/-- Bit `k` of a pin vector. -/
def bit (w : BitVec 16) (k : Nat) : Bool := ((w >>> k) &&& 1) != 0

/-- Bit `k` of a byte, the same test on an 8-bit value. -/
def bit8 (w : BitVec 8) (k : Nat) : Bool := ((w >>> k) &&& 1) != 0

/-- Synchronised SCK. -/
def sck (s : Sync) : Bool := bit s.s2 8

/-- Synchronised previous SCK (`sp`). -/
def sckPrev (s : Sync) : Bool := bit s.sp 8

/-- Synchronised CS_N. -/
def csN (s : Sync) : Bool := bit s.s2 9

/-- Synchronised MOSI. -/
def mosi (s : Sync) : Bool := bit s.s2 10

/-- The host-link input word: the four synchronised pin levels plus the two
free data-RAM inputs. -/
def hostInput (rst : Bool) (s : Sync) (rdData hland : Bool) : HostCmd.Input :=
  ⟨rst, sck s, sckPrev s, csN s, mosi s, rdData, hland⟩

/-- The synchroniser state during cycle `n`, after `n` sampled edges. -/
def syncAt (inputs : Nat → Input) (initial : Sync) (n : Nat) : Sync :=
  run (fun s i => step s i) inputs initial n

theorem syncAt_succ (inputs : Nat → Input) (initial : Sync) (n : Nat) :
    syncAt inputs initial (n + 1) = step (syncAt inputs initial n) (inputs n) := rfl

/-! ## The pin values arrive two (three) cycles later -/

theorem s1_at (inputs : Nat → Input) (initial : Sync) (n : Nat)
    (h : (inputs n).resetN = true) :
    (syncAt inputs initial (n + 1)).s1 = raw (inputs n) := by
  rw [syncAt_succ]
  simp [step, h]

theorem s2_at (inputs : Nat → Input) (initial : Sync) (n : Nat)
    (h0 : (inputs n).resetN = true) (h1 : (inputs (n + 1)).resetN = true) :
    (syncAt inputs initial (n + 2)).s2 = raw (inputs n) := by
  rw [show n + 2 = (n + 1) + 1 from rfl, syncAt_succ]
  simp only [step, h1, ite_true]
  exact s1_at inputs initial n h0

theorem sp_at (inputs : Nat → Input) (initial : Sync) (n : Nat)
    (h0 : (inputs n).resetN = true) (h1 : (inputs (n + 1)).resetN = true)
    (h2 : (inputs (n + 2)).resetN = true) :
    (syncAt inputs initial (n + 3)).sp = raw (inputs n) := by
  rw [show n + 3 = (n + 2) + 1 from rfl, syncAt_succ]
  simp only [step, h2, ite_true]
  exact s2_at inputs initial n h0 h1

/-- The host sees the pin level of cycle `n` two cycles later. -/
theorem sck_at (inputs : Nat → Input) (initial : Sync) (n : Nat)
    (h0 : (inputs n).resetN = true) (h1 : (inputs (n + 1)).resetN = true) :
    sck (syncAt inputs initial (n + 2)) = bit (raw (inputs n)) 8 := by
  unfold sck
  rw [s2_at inputs initial n h0 h1]

theorem csN_at (inputs : Nat → Input) (initial : Sync) (n : Nat)
    (h0 : (inputs n).resetN = true) (h1 : (inputs (n + 1)).resetN = true) :
    csN (syncAt inputs initial (n + 2)) = bit (raw (inputs n)) 9 := by
  unfold csN
  rw [s2_at inputs initial n h0 h1]

theorem mosi_at (inputs : Nat → Input) (initial : Sync) (n : Nat)
    (h0 : (inputs n).resetN = true) (h1 : (inputs (n + 1)).resetN = true) :
    mosi (syncAt inputs initial (n + 2)) = bit (raw (inputs n)) 10 := by
  unfold mosi
  rw [s2_at inputs initial n h0 h1]

/-- The host sees the previous pin level three cycles later: `sck_p` is `sp`. -/
theorem sckPrev_at (inputs : Nat → Input) (initial : Sync) (n : Nat)
    (h0 : (inputs n).resetN = true) (h1 : (inputs (n + 1)).resetN = true)
    (h2 : (inputs (n + 2)).resetN = true) :
    sckPrev (syncAt inputs initial (n + 3)) = bit (raw (inputs n)) 8 := by
  unfold sckPrev
  rw [sp_at inputs initial n h0 h1 h2]

/-- The host link's `SR` is exactly a rising SCK pin edge two cycles earlier,
while the pin `CS_N` is low.  This is both directions: every pin rise is one
`SR`, and no `SR` happens without one. -/
theorem sr_at (inputs : Nat → Input) (initial : Sync) (rst : Bool) (rdData hland : Bool) (n : Nat)
    (h0 : (inputs n).resetN = true) (h1 : (inputs (n + 1)).resetN = true)
    (h2 : (inputs (n + 2)).resetN = true) :
    HostCmd.sr (hostInput rst (syncAt inputs initial (n + 3)) rdData hland)
      = (!bit (raw (inputs (n + 1))) 9 && bit (raw (inputs (n + 1))) 8 &&
          !bit (raw (inputs n)) 8) := by
  unfold HostCmd.sr hostInput
  simp only
  rw [sck_at inputs initial (n + 1) h1 h2, csN_at inputs initial (n + 1) h1 h2,
      sckPrev_at inputs initial n h0 h1 h2]

/-! ## The pin trace as the host's inputs -/

/-- The synchroniser input trace of a raw pin trace. -/
def pinInputs (raws : Nat → BitVec 16) (rst : Nat → Bool) : Nat → Input :=
  fun n => pinInput (rst n) (raws n)

theorem raw_pinInputs (raws : Nat → BitVec 16) (rst : Nat → Bool) (n : Nat) :
    raw (pinInputs raws rst n) = raws n := raw_pinInput (rst n) (raws n)

/-- The host-link input trace of a raw pin trace, with the free data-RAM
inputs `rdData` and `hland`. -/
def hostInputs (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : Sync)
    (rdData hland : Nat → Bool) : Nat → HostCmd.Input :=
  fun n => hostInput (rst n) (syncAt (pinInputs raws rst) initial n) (rdData n) (hland n)

/-- The host's `SR` in cycle `m` is the pin rise held in cycle `m-2`, while the
pin `CS_N` is low in that cycle. -/
theorem sr_pins (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : Sync)
    (rdData hland : Nat → Bool) (n : Nat)
    (h0 : rst n = true) (h1 : rst (n + 1) = true) (h2 : rst (n + 2) = true) :
    HostCmd.sr (hostInputs raws rst initial rdData hland (n + 3))
      = (!bit (raws (n + 1)) 9 && bit (raws (n + 1)) 8 && !bit (raws n) 8) := by
  unfold hostInputs
  have h := sr_at (pinInputs raws rst) initial (rst (n + 3)) (rdData (n + 3)) (hland (n + 3)) n
    h0 h1 h2
  simpa only [raw_pinInputs] using h

/-- The MOSI bit an `SR` samples in cycle `m` is the pin MOSI of cycle `m-2`. -/
theorem mosi_pins (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : Sync)
    (rdData hland : Nat → Bool) (n : Nat)
    (h0 : rst n = true) (h1 : rst (n + 1) = true) :
    (hostInputs raws rst initial rdData hland (n + 2)).mosi = bit (raws n) 10 := by
  unfold hostInputs hostInput
  simp only
  unfold mosi
  rw [s2_at (pinInputs raws rst) initial n h0 h1, raw_pinInputs]

/-! ## The host machine between rising edges

`HostCmd` states its burst theorems with a rising edge in every cycle.  A real
mode-0 clock leaves idle cycles between the edges, so this section restates the
byte progression with explicit gaps: the machine's byte state, bit count, shift
register and address only move on an `SR`, on a write strobe or on an
acknowledgement. -/

/-- A byte in progress in phase `p`: `c` bits counted, no registered strobe,
address `a`, shift register `r`. -/
def Prog (t : HostCmd.State) (p : BitVec 3) (ir : Bool) (c : BitVec 3) (a : BitVec 16)
    (r : BitVec 7) : Prop :=
  t.phase = p ∧ t.isRd = ir ∧ t.bitc = c ∧ t.wr = false ∧ t.addr = a ∧ t.rx = r

/-- The cycle after a data-byte completion: the write strobe is asserted at
address `a` and the next rising edge starts the next byte. -/
def Strobe (t : HostCmd.State) (a : BitVec 16) (r : BitVec 7) : Prop :=
  t.phase = HostCmd.ST_DATA ∧ t.isRd = false ∧ t.bitc = 0 ∧ t.wr = true ∧
    t.addr = a ∧ t.rx = r

/-- One `SR` while the machine counts bit `c` of a byte, `c ≠ 7`. -/
theorem prog_edge (t : HostCmd.State) (i : HostCmd.Input) (p : BitVec 3) (ir : Bool)
    (a : BitVec 16) (r : BitVec 7) (c : BitVec 3) (hc : c ≠ 7)
    (h : Prog t p ir c a r) (hreset : i.resetN = true) (hcs : i.csN = false)
    (hsr : HostCmd.sr i = true) (hack : HostCmd.ackBit t i = false) :
    Prog (HostCmd.step t i) p ir (c + 1) a
      ((r <<< 1) ||| (if i.mosi then 1 else 0)) := by
  obtain ⟨hp, hir, hc', hw, ha, hr⟩ := h
  simp only [Prog, HostCmd.step, HostCmd.phaseNext, HostCmd.bitcNext, HostCmd.rxNext,
    HostCmd.isRdNext, HostCmd.addrNext, HostCmd.wrNext, HostCmd.wdataNext, HostCmd.rdNext,
    HostCmd.rackNext, HostCmd.cmdNext, HostCmd.completing, HostCmd.sr, HostCmd.byteIn,
    HostCmd.ackBit, HostCmd.addrInc] at hp hir hc' hw ha hr hc hreset hcs hsr hack ⊢
  bv_decide

/-- A cycle with no rising edge and no acknowledgement leaves the byte
progression untouched. -/
theorem prog_idle (t : HostCmd.State) (i : HostCmd.Input) (p : BitVec 3) (ir : Bool)
    (a : BitVec 16) (r : BitVec 7) (c : BitVec 3)
    (h : Prog t p ir c a r) (hreset : i.resetN = true) (hcs : i.csN = false)
    (hsr : HostCmd.sr i = false) (hack : HostCmd.ackBit t i = false) :
    Prog (HostCmd.step t i) p ir c a r := by
  obtain ⟨hp, hir, hc', hw, ha, hr⟩ := h
  simp only [Prog, HostCmd.step, HostCmd.phaseNext, HostCmd.bitcNext, HostCmd.rxNext,
    HostCmd.isRdNext, HostCmd.addrNext, HostCmd.wrNext, HostCmd.wdataNext, HostCmd.rdNext,
    HostCmd.rackNext, HostCmd.cmdNext, HostCmd.completing, HostCmd.sr, HostCmd.byteIn,
    HostCmd.ackBit, HostCmd.addrInc] at hp hir hc' hw ha hr hreset hcs hsr hack ⊢
  bv_decide

/-- `d` edge-free cycles leave the byte progression untouched. -/
theorem prog_idle_n (inputs : Nat → HostCmd.Input) (t : HostCmd.State) (p : BitVec 3)
    (ir : Bool) (c : BitVec 3) (a : BitVec 16) (r : BitVec 7) (d : Nat)
    (h : Prog t p ir c a r)
    (hidle : ∀ j, j < d → (inputs j).resetN = true ∧ (inputs j).csN = false ∧
      HostCmd.sr (inputs j) = false ∧
      HostCmd.ackBit (HostCmd.stateAt inputs t j) (inputs j) = false) :
    Prog (HostCmd.stateAt inputs t d) p ir c a r := by
  induction d with
  | zero => exact h
  | succ d ih =>
    rw [HostCmd.stateAt_succ]
    have hd := hidle d (by omega)
    exact prog_idle _ _ _ _ _ _ _ (ih (fun j hj => hidle j (by omega)))
      hd.1 hd.2.1 hd.2.2.1 hd.2.2.2

/-- The command byte completes: `0x02`/`0x03` enter the address bytes, anything
else ignores the rest of the transaction, and `is_rd` latches `0x03`. -/
theorem prog_complete_cmd (t : HostCmd.State) (i : HostCmd.Input) (ir : Bool)
    (a : BitVec 16) (r : BitVec 7) (h : Prog t HostCmd.ST_CMD ir 7 a r)
    (hreset : i.resetN = true) (hcs : i.csN = false) (hsr : HostCmd.sr i = true)
    (hack : HostCmd.ackBit t i = false) :
    Prog (HostCmd.step t i)
      (if HostCmd.byteIn t i == HostCmd.CMD_WRITE || HostCmd.byteIn t i == HostCmd.CMD_READ
        then HostCmd.ST_AH else HostCmd.ST_IGN)
      (HostCmd.byteIn t i == HostCmd.CMD_READ) 0 a
      ((r <<< 1) ||| (if i.mosi then 1 else 0)) := by
  obtain ⟨hp, hir, hc', hw, ha, hr⟩ := h
  simp only [Prog, HostCmd.step, HostCmd.phaseNext, HostCmd.bitcNext, HostCmd.rxNext,
    HostCmd.isRdNext, HostCmd.addrNext, HostCmd.wrNext, HostCmd.wdataNext, HostCmd.rdNext,
    HostCmd.rackNext, HostCmd.cmdNext, HostCmd.completing, HostCmd.sr, HostCmd.byteIn,
    HostCmd.ackBit, HostCmd.addrInc] at hp hir hc' hw ha hr hreset hcs hsr hack ⊢
  bv_decide

/-- The address-high byte completes: the low byte comes from the register. -/
theorem prog_complete_ah (t : HostCmd.State) (i : HostCmd.Input) (ir : Bool)
    (a : BitVec 16) (r : BitVec 7) (h : Prog t HostCmd.ST_AH ir 7 a r)
    (hreset : i.resetN = true) (hcs : i.csN = false) (hsr : HostCmd.sr i = true)
    (hack : HostCmd.ackBit t i = false) :
    Prog (HostCmd.step t i) HostCmd.ST_AL ir 0 (HostCmd.byteIn t i ++ a.truncate 8)
      ((r <<< 1) ||| (if i.mosi then 1 else 0)) := by
  obtain ⟨hp, hir, hc', hw, ha, hr⟩ := h
  simp only [Prog, HostCmd.step, HostCmd.phaseNext, HostCmd.bitcNext, HostCmd.rxNext,
    HostCmd.isRdNext, HostCmd.addrNext, HostCmd.wrNext, HostCmd.wdataNext, HostCmd.rdNext,
    HostCmd.rackNext, HostCmd.cmdNext, HostCmd.completing, HostCmd.sr, HostCmd.byteIn,
    HostCmd.ackBit, HostCmd.addrInc] at hp hir hc' hw ha hr hreset hcs hsr hack ⊢
  bv_decide

/-- The address-low byte completes: the transaction enters the data bytes at
`{AH, AL}`. -/
theorem prog_complete_al (t : HostCmd.State) (i : HostCmd.Input) (ir : Bool)
    (a : BitVec 16) (r : BitVec 7) (h : Prog t HostCmd.ST_AL ir 7 a r)
    (hreset : i.resetN = true) (hcs : i.csN = false) (hsr : HostCmd.sr i = true)
    (hack : HostCmd.ackBit t i = false) :
    Prog (HostCmd.step t i) HostCmd.ST_DATA ir 0 ((a >>> 8).truncate 8 ++ HostCmd.byteIn t i)
      ((r <<< 1) ||| (if i.mosi then 1 else 0)) := by
  obtain ⟨hp, hir, hc', hw, ha, hr⟩ := h
  simp only [Prog, HostCmd.step, HostCmd.phaseNext, HostCmd.bitcNext, HostCmd.rxNext,
    HostCmd.isRdNext, HostCmd.addrNext, HostCmd.wrNext, HostCmd.wdataNext, HostCmd.rdNext,
    HostCmd.rackNext, HostCmd.cmdNext, HostCmd.completing, HostCmd.sr, HostCmd.byteIn,
    HostCmd.ackBit, HostCmd.addrInc] at hp hir hc' hw ha hr hreset hcs hsr hack ⊢
  bv_decide

/-- A write data byte completes: the strobe and the received byte appear in the
next cycle. -/
theorem prog_complete_data (t : HostCmd.State) (i : HostCmd.Input)
    (a : BitVec 16) (r : BitVec 7) (h : Prog t HostCmd.ST_DATA false 7 a r)
    (hreset : i.resetN = true) (hcs : i.csN = false) (hsr : HostCmd.sr i = true)
    (hack : HostCmd.ackBit t i = false) :
    Strobe (HostCmd.step t i) a ((r <<< 1) ||| (if i.mosi then 1 else 0)) ∧
      (HostCmd.step t i).wdata = HostCmd.byteIn t i := by
  obtain ⟨hp, hir, hc', hw, ha, hr⟩ := h
  simp only [Strobe, HostCmd.step, HostCmd.phaseNext, HostCmd.bitcNext, HostCmd.rxNext,
    HostCmd.isRdNext, HostCmd.addrNext, HostCmd.wrNext, HostCmd.wdataNext, HostCmd.rdNext,
    HostCmd.rackNext, HostCmd.cmdNext, HostCmd.completing, HostCmd.sr, HostCmd.byteIn,
    HostCmd.ackBit, HostCmd.addrInc] at hp hir hc' hw ha hr hreset hcs hsr hack ⊢
  bv_decide

/-- The cycle after the strobe: the address has stepped and the next byte can
start. -/
theorem strobe_step (t : HostCmd.State) (i : HostCmd.Input) (a : BitVec 16) (r : BitVec 7)
    (h : Strobe t a r) (hreset : i.resetN = true) (hcs : i.csN = false)
    (hsr : HostCmd.sr i = false) (hack : HostCmd.ackBit t i = false) :
    Prog (HostCmd.step t i) HostCmd.ST_DATA false 0 (a + 1) r := by
  obtain ⟨hp, hir, hc', hw, ha, hr⟩ := h
  simp only [Prog, HostCmd.step, HostCmd.phaseNext, HostCmd.bitcNext, HostCmd.rxNext,
    HostCmd.isRdNext, HostCmd.addrNext, HostCmd.wrNext, HostCmd.wdataNext, HostCmd.rdNext,
    HostCmd.rackNext, HostCmd.cmdNext, HostCmd.completing, HostCmd.sr, HostCmd.byteIn,
    HostCmd.ackBit, HostCmd.addrInc] at hp hir hc' hw ha hr hreset hcs hsr hack ⊢
  bv_decide

/-- From the strobe state, `d ≥ 1` edge-free cycles reach the start of the next
data byte, one address higher. -/
theorem strobe_settle (inputs : Nat → HostCmd.Input) (t : HostCmd.State) (a : BitVec 16)
    (r : BitVec 7) (d : Nat) (hd : 1 ≤ d) (h : Strobe t a r)
    (hidle : ∀ j, j < d → (inputs j).resetN = true ∧ (inputs j).csN = false ∧
      HostCmd.sr (inputs j) = false ∧
      HostCmd.ackBit (HostCmd.stateAt inputs t j) (inputs j) = false) :
    Prog (HostCmd.stateAt inputs t d) HostCmd.ST_DATA false 0 (a + 1) r := by
  have hd1 : 1 + (d - 1) = d := by omega
  rw [← hd1, HostCmd.stateAt_add]
  refine prog_idle_n (fun j => inputs (1 + j)) (HostCmd.stateAt inputs t 1)
    HostCmd.ST_DATA false 0 (a + 1) r (d - 1) ?_ ?_
  · have h0 := hidle 0 (by omega)
    exact strobe_step t (inputs 0) a r h h0.1 h0.2.1 h0.2.2.1 h0.2.2.2
  · intro j hj
    have h1 := hidle (1 + j) (by omega)
    refine ⟨h1.1, h1.2.1, h1.2.2.1, ?_⟩
    rw [← HostCmd.stateAt_add]
    exact h1.2.2.2

/-! ## The pin clock

A mode-0 clock on the pins: `SCK` rises every `period` cycles and `CS_N` stays
low.  In the sampled trace each phase covers at least one cycle, so
`period ≥ 2`. -/

/-- Cycle of the `k`-th `SR` the host sees. -/
def srAt (first period : Nat) : Nat → Nat
  | 0 => first
  | k + 1 => srAt first period k + period

theorem srAt_succ (first period k : Nat) :
    srAt first period (k + 1) = srAt first period k + period := rfl

theorem srAt_succ_lt (first period : Nat) (hp : 1 ≤ period) (k : Nat) :
    srAt first period k < srAt first period (k + 1) := by
  rw [srAt_succ]
  omega

theorem srAt_le_add (first period : Nat) (hp : 1 ≤ period) (k d : Nat) :
    srAt first period k ≤ srAt first period (k + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ]
    exact Nat.le_trans ih (Nat.le_of_lt (srAt_succ_lt first period hp (k + d)))

/-- The host's `SR` cycles only move forward. -/
theorem srAt_le (first period : Nat) (hp : 1 ≤ period) {a b : Nat} (h : a ≤ b) :
    srAt first period a ≤ srAt first period b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact srAt_le_add first period hp a d

/-- The host's `SR` cycles are strictly increasing. -/
theorem srAt_lt (first period : Nat) (hp : 1 ≤ period) {a b : Nat} (h : a < b) :
    srAt first period a < srAt first period b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt h)
  cases d with
  | zero => omega
  | succ d =>
    rw [Nat.add_succ]
    exact Nat.lt_of_le_of_lt (srAt_le_add first period hp a d)
      (srAt_succ_lt first period hp (a + d))

/-- Shift one bit into the 7-bit receive register. -/
def shift1 (r : BitVec 7) (b : Bool) : BitVec 7 := (r <<< 1) ||| (if b then 1 else 0)

/-- Seven shifted bits. -/
def pack7 (r : BitVec 7) (b0 b1 b2 b3 b4 b5 b6 : Bool) : BitVec 7 :=
  shift1 (shift1 (shift1 (shift1 (shift1 (shift1 (shift1 r b0) b1) b2) b3) b4) b5) b6

/-- The byte eight rising edges deliver, most significant bit first. -/
def byte8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : BitVec 8 :=
  pack7 0 b0 b1 b2 b3 b4 b5 b6 ++ (if b7 then (1 : BitVec 1) else 0)

/-- Seven shifts push the previous register content out. -/
theorem pack7_shifted_out (r : BitVec 7) (b0 b1 b2 b3 b4 b5 b6 : Bool) :
    pack7 r b0 b1 b2 b3 b4 b5 b6 = pack7 0 b0 b1 b2 b3 b4 b5 b6 := by
  unfold pack7 shift1
  bv_decide

/-- The delivered byte is `{b0, b1, …, b7}` with `b0` most significant, i.e.
SPEC_V2 §9's MSB-first byte. -/
theorem byte8_eq (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    byte8 b0 b1 b2 b3 b4 b5 b6 b7 =
      ((if b0 then (0x80 : BitVec 8) else 0) ||| (if b1 then 0x40 else 0) |||
       (if b2 then 0x20 else 0) ||| (if b3 then 0x10 else 0) |||
       (if b4 then 0x08 else 0) ||| (if b5 then 0x04 else 0) |||
       (if b6 then 0x02 else 0) ||| (if b7 then 0x01 else 0)) := by
  unfold byte8 pack7 shift1
  bv_decide

/-- The eight clocked bits of a byte reassemble it, most significant first. -/
theorem byte8_bits (B : BitVec 8) :
    byte8 (bit8 B 7) (bit8 B 6) (bit8 B 5) (bit8 B 4) (bit8 B 3) (bit8 B 2) (bit8 B 1)
      (bit8 B 0) = B := by
  unfold byte8 pack7 shift1 bit8
  bv_decide

/-! ## One byte at an arbitrary position in the trace -/

/-- The trace facts a byte needs: reset released, `CS_N` low, a rising edge at
each of the seven non-completing edges of the byte, no other rising edge inside
the byte's window, and no read acknowledgement.  The window starts at the
byte's first `SR` cycle `srAt first period base` and ends at the eighth edge
`srAt first period (base + 7)`. -/
structure Clean (inputs : Nat → HostCmd.Input) (t : HostCmd.State) (first period base : Nat) :
    Prop where
  /-- Reset stays released through the byte. -/
  reset : ∀ j, j < srAt first period (base + 7) → (inputs j).resetN = true
  /-- `CS_N` stays low through the byte. -/
  cs : ∀ j, j < srAt first period (base + 7) → (inputs j).csN = false
  /-- The seven non-completing rising edges. -/
  sr : ∀ k, k < 7 → HostCmd.sr (inputs (srAt first period (base + k))) = true
  /-- No other rising edge inside the byte's window. -/
  nosr : ∀ j, srAt first period base ≤ j → j < srAt first period (base + 7) →
    (∀ k, k < 7 → j ≠ srAt first period (base + k)) → HostCmd.sr (inputs j) = false
  /-- No read acknowledgement in the byte. -/
  ack : ∀ j, j < srAt first period (base + 7) →
    HostCmd.ackBit (HostCmd.stateAt inputs t j) (inputs j) = false

/-- `d` edge-free cycles then one rising edge count one more bit of the byte,
with the gap arbitrary. -/
theorem prog_advance (inputs : Nat → HostCmd.Input) (t : HostCmd.State) (p : BitVec 3)
    (ir : Bool) (a : BitVec 16) (r : BitVec 7) (c : BitVec 3) (first period base k : Nat)
    (hp : 1 ≤ period) (hc : c ≠ 7)
    (h : Prog (HostCmd.stateAt inputs t (srAt first period (base + k))) p ir c a r)
    (hreset : ∀ j, srAt first period (base + k) ≤ j → j < srAt first period (base + k + 1) →
      (inputs j).resetN = true)
    (hcs : ∀ j, srAt first period (base + k) ≤ j → j < srAt first period (base + k + 1) →
      (inputs j).csN = false)
    (hsr : HostCmd.sr (inputs (srAt first period (base + k))) = true)
    (hnosr : ∀ j, srAt first period (base + k) < j → j < srAt first period (base + k + 1) →
      HostCmd.sr (inputs j) = false)
    (hack : ∀ j, srAt first period (base + k) ≤ j → j < srAt first period (base + k + 1) →
      HostCmd.ackBit (HostCmd.stateAt inputs t j) (inputs j) = false) :
    Prog (HostCmd.stateAt inputs t (srAt first period (base + k + 1))) p ir (c + 1) a
      (shift1 r (inputs (srAt first period (base + k))).mosi) := by
  have hk : srAt first period (base + k) < srAt first period (base + k + 1) := by
    rw [srAt_succ]
    omega
  have h1 : Prog (HostCmd.stateAt inputs t (srAt first period (base + k) + 1)) p ir (c + 1) a
      (shift1 r (inputs (srAt first period (base + k))).mosi) := by
    rw [HostCmd.stateAt_succ]
    have := prog_edge (HostCmd.stateAt inputs t (srAt first period (base + k)))
      (inputs (srAt first period (base + k))) p ir a r c hc h (hreset _ (Nat.le_refl _) hk)
      (hcs _ (Nat.le_refl _) hk) hsr (hack _ (Nat.le_refl _) hk)
    simpa [shift1] using this
  have hidx : srAt first period (base + k + 1) = srAt first period (base + k) + 1 + (period - 1) := by
    rw [srAt_succ]
    omega
  rw [hidx, HostCmd.stateAt_add]
  refine prog_idle_n (fun j => inputs (srAt first period (base + k) + 1 + j))
    (HostCmd.stateAt inputs t (srAt first period (base + k) + 1)) p ir (c + 1) a _ (period - 1)
    h1 ?_
  intro j hj
  have hjlt : srAt first period (base + k) + 1 + j < srAt first period (base + k + 1) := by omega
  refine ⟨hreset _ (by omega) hjlt, hcs _ (by omega) hjlt, hnosr _ (by omega) hjlt, ?_⟩
  rw [← HostCmd.stateAt_add]
  exact hack _ (by omega) hjlt

/-- Seven rising edges count the seven most significant bits of a byte, at an
arbitrary position `base` in the trace. -/
theorem byte_chain (inputs : Nat → HostCmd.Input) (t : HostCmd.State) (p : BitVec 3)
    (ir : Bool) (a : BitVec 16) (r : BitVec 7) (first period base : Nat) (hp : 1 ≤ period)
    (B : BitVec 8)
    (h : Prog (HostCmd.stateAt inputs t (srAt first period base)) p ir 0 a r)
    (hc : Clean inputs t first period base)
    (hm : ∀ k, k < 8 → (inputs (srAt first period (base + k))).mosi = bit8 B (7 - k)) :
    Prog (HostCmd.stateAt inputs t (srAt first period (base + 7))) p ir 7 a
      (pack7 r (bit8 B 7) (bit8 B 6) (bit8 B 5) (bit8 B 4) (bit8 B 3) (bit8 B 2) (bit8 B 1)) := by
  have mono : ∀ {x y : Nat}, x ≤ y → srAt first period x ≤ srAt first period y :=
    fun hxy => srAt_le first period hp hxy
  have hrst : ∀ k, k < 7 → ∀ j, srAt first period (base + k) ≤ j →
      j < srAt first period (base + k + 1) → (inputs j).resetN = true :=
    fun k hk j _ hj => hc.reset j (Nat.lt_of_lt_of_le hj (mono (by omega)))
  have hcst : ∀ k, k < 7 → ∀ j, srAt first period (base + k) ≤ j →
      j < srAt first period (base + k + 1) → (inputs j).csN = false :=
    fun k hk j _ hj => hc.cs j (Nat.lt_of_lt_of_le hj (mono (by omega)))
  have hn : ∀ k, k < 7 → ∀ j, srAt first period (base + k) < j →
      j < srAt first period (base + k + 1) → HostCmd.sr (inputs j) = false :=
    fun k hk j h1 h2 =>
      hc.nosr j (Nat.le_trans (mono (by omega)) (Nat.le_of_lt h1))
        (Nat.lt_of_lt_of_le h2 (mono (by omega)))
        (fun k' hk' heq => by
          rcases Nat.lt_or_ge k' k with hlt | hge
          · have hle : srAt first period (base + k') ≤ srAt first period (base + k) :=
              mono (by omega)
            omega
          · rcases Nat.lt_or_ge k' (k + 1) with hlt2 | hge2
            · have hk'e : k' = k := by omega
              subst hk'e
              omega
            · have hle : srAt first period (base + k + 1) ≤ srAt first period (base + k') :=
                mono (by omega)
              omega)
  have hakt : ∀ k, k < 7 → ∀ j, srAt first period (base + k) ≤ j →
      j < srAt first period (base + k + 1) →
      HostCmd.ackBit (HostCmd.stateAt inputs t j) (inputs j) = false :=
    fun k hk j _ hj => hc.ack j (Nat.lt_of_lt_of_le hj (mono (by omega)))
  have step : ∀ (k : Nat) (hk : k < 7) (c : BitVec 3) (hc7 : c ≠ 7) (r : BitVec 7)
      (b : Bool),
      Prog (HostCmd.stateAt inputs t (srAt first period (base + k))) p ir c a r →
      (inputs (srAt first period (base + k))).mosi = b →
      Prog (HostCmd.stateAt inputs t (srAt first period (base + k + 1))) p ir (c + 1) a
        (shift1 r b) := by
    intro k hk c hc7 r b hprog hbit
    have := prog_advance inputs t p ir a r c first period base k hp hc7 hprog
      (hrst k hk) (hcst k hk) (hc.sr k hk) (hn k hk) (hakt k hk)
    simpa [hbit] using this
  have h0 : Prog (HostCmd.stateAt inputs t (srAt first period (base + 0))) p ir 0 a r := h
  have h1 := step 0 (by decide) 0 (by decide) r (bit8 B 7) h0 (hm 0 (by decide))
  have h2 := step 1 (by decide) 1 (by decide) (shift1 r (bit8 B 7)) (bit8 B 6) h1 (hm 1 (by decide))
  have h3 := step 2 (by decide) 2 (by decide) (shift1 (shift1 r (bit8 B 7)) (bit8 B 6))
    (bit8 B 5) h2 (hm 2 (by decide))
  have h4 := step 3 (by decide) 3 (by decide)
    (shift1 (shift1 (shift1 r (bit8 B 7)) (bit8 B 6)) (bit8 B 5)) (bit8 B 4) h3 (hm 3 (by decide))
  have h5 := step 4 (by decide) 4 (by decide)
    (shift1 (shift1 (shift1 (shift1 r (bit8 B 7)) (bit8 B 6)) (bit8 B 5)) (bit8 B 4))
    (bit8 B 3) h4 (hm 4 (by decide))
  have h6 := step 5 (by decide) 5 (by decide)
    (shift1 (shift1 (shift1 (shift1 (shift1 r (bit8 B 7)) (bit8 B 6)) (bit8 B 5)) (bit8 B 4))
      (bit8 B 3)) (bit8 B 2) h5 (hm 5 (by decide))
  have h7 := step 6 (by decide) 6 (by decide)
    (shift1 (shift1 (shift1 (shift1 (shift1 (shift1 r (bit8 B 7)) (bit8 B 6)) (bit8 B 5))
      (bit8 B 4)) (bit8 B 3)) (bit8 B 2)) (bit8 B 1) h6 (hm 6 (by decide))
  exact h7

/-- A whole byte: seven counted edges and the completing edge deliver `B` to
`HostCmd`'s byte completion. -/
theorem byte_at (inputs : Nat → HostCmd.Input) (t : HostCmd.State) (p : BitVec 3)
    (ir : Bool) (a : BitVec 16) (r : BitVec 7) (first period base : Nat) (hp : 1 ≤ period)
    (B : BitVec 8)
    (h : Prog (HostCmd.stateAt inputs t (srAt first period base)) p ir 0 a r)
    (hc : Clean inputs t first period base)
    (hm : ∀ k, k < 8 → (inputs (srAt first period (base + k))).mosi = bit8 B (7 - k)) :
    Prog (HostCmd.stateAt inputs t (srAt first period (base + 7))) p ir 7 a
        (pack7 r (bit8 B 7) (bit8 B 6) (bit8 B 5) (bit8 B 4) (bit8 B 3) (bit8 B 2) (bit8 B 1)) ∧
      HostCmd.byteIn (HostCmd.stateAt inputs t (srAt first period (base + 7)))
        (inputs (srAt first period (base + 7))) = B := by
  have hchain := byte_chain inputs t p ir a r first period base hp B h hc hm
  refine ⟨hchain, ?_⟩
  have hmosi : (inputs (srAt first period (base + 7))).mosi = bit8 B 0 := by
    have := hm 7 (by decide)
    simpa using this
  have hrx := hchain.2.2.2.2.2
  have hp7 := pack7_shifted_out r (bit8 B 7) (bit8 B 6) (bit8 B 5) (bit8 B 4) (bit8 B 3)
    (bit8 B 2) (bit8 B 1)
  simp only [HostCmd.byteIn, hmosi, hrx, hp7]
  exact byte8_bits B

/-! ## The pin level of a rising edge -/

/-- The pin rise the host's `SR` in cycle `m` observes: `SCK` high two cycles
earlier and low three cycles earlier, so the host's `s2`/`sp` pair sees a rise.
The first three cycles read the reset state's zero synchroniser, so only `SCK`
high in cycle 0 could fire then, and the idle start of a transaction excludes
that. -/
def pinRise (raws : Nat → BitVec 16) : Nat → Bool
  | 0 => false
  | 1 => false
  | 2 => bit (raws 0) 8
  | m + 3 => bit (raws (m + 1)) 8 && !bit (raws m) 8

/-- The host's `SR` is exactly the pin rise it observes. -/
theorem sr_eq_pinRise (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : Sync)
    (rdData hland : Nat → Bool) (hinit : initial = resetState)
    (hreset : ∀ j, rst j = true) (hcs : ∀ j, bit (raws j) 9 = false) (m : Nat) :
    HostCmd.sr (hostInputs raws rst initial rdData hland m) = pinRise raws m := by
  match m with
  | 0 =>
    have h0 : syncAt (pinInputs raws rst) resetState 0 = resetState := rfl
    subst hinit
    simp only [hostInputs, hostInput, HostCmd.sr, pinRise, sck, sckPrev, bit]
    rw [h0]
    simp [resetState]
  | 1 =>
    have h1 : syncAt (pinInputs raws rst) resetState 1 =
        step resetState (pinInputs raws rst 0) := rfl
    subst hinit
    simp only [hostInputs, hostInput, HostCmd.sr, pinRise, sck, sckPrev, bit]
    rw [h1]
    simp [resetState, step]
  | 2 =>
    subst hinit
    have hs2 : (syncAt (pinInputs raws rst) resetState 2).s2 = raws 0 := by
      rw [s2_at (pinInputs raws rst) resetState 0 (hreset 0) (hreset 1), raw_pinInputs]
    have hsp : (syncAt (pinInputs raws rst) resetState 2).sp = (0 : BitVec 16) := by
      rw [show (2 : Nat) = 1 + 1 from rfl, syncAt_succ]
      rw [show (1 : Nat) = 0 + 1 from rfl, syncAt_succ]
      simp [step, hreset 0, hreset 1, resetState, pinInputs, pinInput, syncAt, run]
    have hcs0 : (raws 0 >>> 9) &&& 1 = (0 : BitVec 16) := by
      have h := hcs 0
      simp only [bit] at h
      simpa using h
    simp only [hostInputs, hostInput, HostCmd.sr, pinRise, sck, csN, sckPrev]
    rw [hs2, hsp]
    simp only [bit]
    bv_decide
  | m + 3 =>
    rw [sr_pins raws rst initial rdData hland m (hreset m) (hreset (m + 1))
      (hreset (m + 2))]
    have hb : ((raws (m + 1) >>> 9) &&& 1 != (0 : BitVec 16)) = false := by
      have h := hcs (m + 1)
      simpa only [bit] using h
    simp only [pinRise, bit]
    bv_decide

/-- A pin rise is one `SR`. -/
theorem sr_of_pinRise (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : Sync)
    (rdData hland : Nat → Bool) (hinit : initial = resetState)
    (hreset : ∀ j, rst j = true) (hcs : ∀ j, bit (raws j) 9 = false) (m : Nat)
    (h : pinRise raws m = true) :
    HostCmd.sr (hostInputs raws rst initial rdData hland m) = true := by
  rw [sr_eq_pinRise raws rst initial rdData hland hinit hreset hcs m, h]

/-- Without a pin rise there is no `SR`. -/
theorem sr_of_not_pinRise (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : Sync)
    (rdData hland : Nat → Bool) (hinit : initial = resetState)
    (hreset : ∀ j, rst j = true) (hcs : ∀ j, bit (raws j) 9 = false) (m : Nat)
    (h : pinRise raws m = false) :
    HostCmd.sr (hostInputs raws rst initial rdData hland m) = false := by
  rw [sr_eq_pinRise raws rst initial rdData hland hinit hreset hcs m, h]

/-- The MOSI bit the host samples in cycle `m` is the pin MOSI of cycle `m-2`. -/
theorem mosi_pins_at (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : Sync)
    (rdData hland : Nat → Bool) (m : Nat) (hm : 2 ≤ m)
    (h0 : rst (m - 2) = true) (h1 : rst (m - 1) = true) :
    (hostInputs raws rst initial rdData hland m).mosi = bit (raws (m - 2)) 10 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  exact mosi_pins raws rst initial rdData hland n (by simpa using h0) (by simpa using h1)

/-- The synchronised `CS_N` is low in every cycle of a transaction: it is the
pin `CS_N` of two cycles earlier, and the reset state holds it zero at the
start. -/
theorem cs_low (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : Sync)
    (rdData hland : Nat → Bool) (hinit : initial = resetState)
    (hreset : ∀ j, rst j = true) (hcs : ∀ j, bit (raws j) 9 = false) (m : Nat) :
    (hostInputs raws rst initial rdData hland m).csN = false := by
  match m with
  | 0 =>
    have h0 : syncAt (pinInputs raws rst) initial 0 = initial := rfl
    subst hinit
    change csN (syncAt (pinInputs raws rst) resetState 0) = false
    rw [h0]
    simp [csN, resetState, bit]
  | 1 =>
    have h1 : syncAt (pinInputs raws rst) initial 1 =
        step initial (pinInputs raws rst 0) := rfl
    subst hinit
    change csN (syncAt (pinInputs raws rst) resetState 1) = false
    rw [h1]
    simp [csN, step, resetState, bit]
  | k + 2 =>
    change csN (syncAt (pinInputs raws rst) initial (k + 2)) = false
    rw [csN_at (pinInputs raws rst) initial k (hreset k) (hreset (k + 1)), raw_pinInputs]
    exact hcs k

/-- The trace facts of one byte, from the pin trace. -/
theorem clean_of_pins (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : Sync)
    (rdData hland : Nat → Bool) (first period base : Nat)
    (hp : 1 ≤ period) (hinit : initial = resetState)
    (hreset : ∀ j, rst j = true) (hcs : ∀ j, bit (raws j) 9 = false)
    (hrise : ∀ k, k < 7 → pinRise raws (srAt first period (base + k)) = true)
    (honly : ∀ m, pinRise raws m = true → ∃ k, m = srAt first period k)
    (hack : ∀ j, HostCmd.ackBit (HostCmd.stateAt (hostInputs raws rst initial rdData hland)
      HostCmd.resetState j) (hostInputs raws rst initial rdData hland j) = false) :
    Clean (hostInputs raws rst initial rdData hland) HostCmd.resetState first period base := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j _
    exact hreset j
  · intro j _
    exact cs_low raws rst initial rdData hland hinit hreset hcs j
  · intro k hk
    exact sr_of_pinRise raws rst initial rdData hland hinit hreset hcs _ (hrise k hk)
  · intro j hb hlt hne
    by_cases hrise : pinRise raws j = true
    · exfalso
      obtain ⟨k, hk⟩ := honly j hrise
      have hmono : ∀ {x y : Nat}, x ≤ y → srAt first period x ≤ srAt first period y :=
        fun hxy => srAt_le first period hp hxy
      have hkb : base ≤ k := by
        rcases Nat.lt_or_ge k base with h' | h'
        · exfalso
          have h1 : srAt first period k < srAt first period base := srAt_lt first period hp h'
          omega
        · exact h'
      have hkt : k < base + 7 := by
        rcases Nat.lt_or_ge k (base + 7) with h' | h'
        · exact h'
        · exfalso
          have h1 : srAt first period (base + 7) ≤ srAt first period k := hmono h'
          omega
      exact hne (k - base) (by omega) (by
        rw [show base + (k - base) = k from by omega]
        exact hk)
    · have hpf : pinRise raws j = false := by
        simpa using hrise
      exact sr_of_not_pinRise raws rst initial rdData hland hinit hreset hcs j hpf
  · intro j _
    exact hack j

/-! ## Transaction index arithmetic -/

theorem highByte (b1 b2 : BitVec 8) : (((b1 ++ b2) >>> 8).truncate 8) = b1 := by
  bv_decide

/-- A byte address plus one is the next byte's address. -/
theorem addrSucc (A : BitVec 16) (j : Nat) :
    A + (j : BitVec 16) + 1 = A + ((j + 1 : Nat) : BitVec 16) := by
  rw [BitVec.natCast_eq_ofNat, BitVec.natCast_eq_ofNat]
  change A + BitVec.ofNat 16 j + BitVec.ofNat 16 1 = A + BitVec.ofNat 16 (j + 1)
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- The first edge of data byte `j+1` is eight edges after the first edge of
byte `j`. -/
theorem baseSucc (j : Nat) : 8 * (3 + (j + 1)) = 8 * (3 + j) + 8 := by
  rw [show 3 + (j + 1) = (3 + j) + 1 from by omega, Nat.mul_succ]

/-! ## Settling from a byte's last edge to the next byte's first edge -/

/-- From a byte in progress at `srAt base`, the edge-free cycles up to the next
byte's first edge leave the machine at the start of that byte. -/
theorem settle_prog (inputs : Nat → HostCmd.Input) (t : HostCmd.State)
    (p : BitVec 3) (ir : Bool) (a : BitVec 16) (r : BitVec 7) (first period base : Nat)
    (hp : 2 ≤ period)
    (h : Prog (HostCmd.stateAt inputs t (srAt first period (base + 7) + 1)) p ir 0 a r)
    (hreset : ∀ j, j < srAt first period (base + 8) → (inputs j).resetN = true)
    (hcs : ∀ j, j < srAt first period (base + 8) → (inputs j).csN = false)
    (hnosr : ∀ j, srAt first period (base + 7) + 1 ≤ j → j < srAt first period (base + 8) →
      HostCmd.sr (inputs j) = false)
    (hack : ∀ j, j < srAt first period (base + 8) →
      HostCmd.ackBit (HostCmd.stateAt inputs t j) (inputs j) = false) :
    Prog (HostCmd.stateAt inputs t (srAt first period (base + 8))) p ir 0 a r := by
  have hidx : srAt first period (base + 7) + 1 + (period - 1) = srAt first period (base + 8) := by
    rw [show srAt first period (base + 8) = srAt first period (base + 7) + period from rfl]
    omega
  rw [← hidx, HostCmd.stateAt_add]
  refine prog_idle_n (fun k => inputs (srAt first period (base + 7) + 1 + k))
    (HostCmd.stateAt inputs t (srAt first period (base + 7) + 1)) p ir 0 a r (period - 1) h ?_
  intro k hk
  have hlt : srAt first period (base + 7) + 1 + k < srAt first period (base + 8) := by omega
  refine ⟨hreset _ (by omega), hcs _ (by omega), hnosr _ (by omega) hlt, ?_⟩
  rw [← HostCmd.stateAt_add]
  exact hack _ hlt

/-! ## The headline theorem

The steps below are separate lemmas about a symbolic state and a symbolic cycle
index, so each proof is small and is checked once; the headline theorem only
chains them.  A byte's receive shift register content is never named: `AtPhase`
existentially quantifies it, and every construction below writes its witness
explicitly. -/

/-- The machine is in phase `p` at cycle `n`, at bit count 0, with no pending
write strobe and address `a`, for some receive shift register content. -/
def AtPhase (inputs : Nat → HostCmd.Input) (t : HostCmd.State) (n : Nat) (p : BitVec 3)
    (ir : Bool) (a : BitVec 16) : Prop :=
  ∃ r, Prog (HostCmd.stateAt inputs t n) p ir 0 a r

/-- The machine is at the start of a data byte at address `a`. -/
def AtByte (inputs : Nat → HostCmd.Input) (t : HostCmd.State) (n : Nat) (a : BitVec 16) : Prop :=
  AtPhase inputs t n HostCmd.ST_DATA false a

/-- Between a byte's eighth edge and the next byte's first edge there is no
other edge of the clock trace: `srAt` is strictly increasing in the edge index,
and the next byte's first edge is exactly `period` cycles after the eighth. -/
theorem edge_gap (first period : Nat) (hp : 1 ≤ period) (base m k : Nat)
    (hm : 0 < m) (hmp : m < period)
    (hk : srAt first period (base + 7) + m = srAt first period k) : False := by
  rcases Nat.lt_or_ge k (base + 8) with hlt | hge
  · have h1 : srAt first period k ≤ srAt first period (base + 7) :=
      srAt_le first period hp (by omega)
    omega
  · have h1 : srAt first period (base + 8) ≤ srAt first period k :=
      srAt_le first period hp hge
    have h2 : srAt first period (base + 8) = srAt first period (base + 7) + period := rfl
    omega

/-- The eight rising edges of a byte reach its eighth edge, where `byteIn` is
the byte.  This is `byte_at` with its result written out. -/
theorem byte_end (inputs : Nat → HostCmd.Input) (t : HostCmd.State) (p : BitVec 3)
    (ir : Bool) (a : BitVec 16) (r : BitVec 7) (first period base : Nat) (hp : 1 ≤ period)
    (B : BitVec 8)
    (h : Prog (HostCmd.stateAt inputs t (srAt first period base)) p ir 0 a r)
    (hc : Clean inputs t first period base)
    (hm : ∀ k, k < 8 → (inputs (srAt first period (base + k))).mosi = bit8 B (7 - k)) :
    Prog (HostCmd.stateAt inputs t (srAt first period (base + 7))) p ir 7 a
        (pack7 r (bit8 B 7) (bit8 B 6) (bit8 B 5) (bit8 B 4) (bit8 B 3) (bit8 B 2) (bit8 B 1)) ∧
      HostCmd.byteIn (HostCmd.stateAt inputs t (srAt first period (base + 7)))
        (inputs (srAt first period (base + 7))) = B :=
  byte_at inputs t p ir a r first period base hp B h hc hm

/-- The command byte completes: `0x02`/`0x03` enter the address-high byte,
anything else ignores the transaction, and `is_rd` latches `0x03`. -/
theorem complete_cmd (inputs : Nat → HostCmd.Input) (t : HostCmd.State) (first period base : Nat)
    (hp : 1 ≤ period) (ir : Bool) (a : BitVec 16) (r : BitVec 7) (B : BitVec 8)
    (h : Prog (HostCmd.stateAt inputs t (srAt first period base)) HostCmd.ST_CMD ir 0 a r)
    (hc : Clean inputs t first period base)
    (hm : ∀ k, k < 8 → (inputs (srAt first period (base + k))).mosi = bit8 B (7 - k))
    (hsr : HostCmd.sr (inputs (srAt first period (base + 7))) = true)
    (hreset : (inputs (srAt first period (base + 7))).resetN = true)
    (hcs : (inputs (srAt first period (base + 7))).csN = false)
    (hack : HostCmd.ackBit (HostCmd.stateAt inputs t (srAt first period (base + 7)))
      (inputs (srAt first period (base + 7))) = false) :
    AtPhase inputs t (srAt first period (base + 7) + 1)
      (if B == HostCmd.CMD_WRITE || B == HostCmd.CMD_READ then HostCmd.ST_AH else HostCmd.ST_IGN)
      (B == HostCmd.CMD_READ) a := by
  have hb := byte_end inputs t HostCmd.ST_CMD ir a r first period base hp B h hc hm
  have hstep := prog_complete_cmd (HostCmd.stateAt inputs t (srAt first period (base + 7)))
    (inputs (srAt first period (base + 7))) ir a
    (pack7 r (bit8 B 7) (bit8 B 6) (bit8 B 5) (bit8 B 4) (bit8 B 3) (bit8 B 2) (bit8 B 1))
    hb.1 hreset hcs hsr hack
  rw [hb.2] at hstep
  rw [← HostCmd.stateAt_succ] at hstep
  exact ⟨_, hstep⟩

/-- The address-high byte completes: the low half comes from the register. -/
theorem complete_ah (inputs : Nat → HostCmd.Input) (t : HostCmd.State) (first period base : Nat)
    (hp : 1 ≤ period) (ir : Bool) (a : BitVec 16) (r : BitVec 7) (B : BitVec 8)
    (h : Prog (HostCmd.stateAt inputs t (srAt first period base)) HostCmd.ST_AH ir 0 a r)
    (hc : Clean inputs t first period base)
    (hm : ∀ k, k < 8 → (inputs (srAt first period (base + k))).mosi = bit8 B (7 - k))
    (hsr : HostCmd.sr (inputs (srAt first period (base + 7))) = true)
    (hreset : (inputs (srAt first period (base + 7))).resetN = true)
    (hcs : (inputs (srAt first period (base + 7))).csN = false)
    (hack : HostCmd.ackBit (HostCmd.stateAt inputs t (srAt first period (base + 7)))
      (inputs (srAt first period (base + 7))) = false) :
    AtPhase inputs t (srAt first period (base + 7) + 1) HostCmd.ST_AL ir (B ++ a.truncate 8) := by
  have hb := byte_end inputs t HostCmd.ST_AH ir a r first period base hp B h hc hm
  have hstep := prog_complete_ah (HostCmd.stateAt inputs t (srAt first period (base + 7)))
    (inputs (srAt first period (base + 7))) ir a
    (pack7 r (bit8 B 7) (bit8 B 6) (bit8 B 5) (bit8 B 4) (bit8 B 3) (bit8 B 2) (bit8 B 1))
    hb.1 hreset hcs hsr hack
  rw [hb.2] at hstep
  rw [← HostCmd.stateAt_succ] at hstep
  exact ⟨_, hstep⟩

/-- The address-low byte completes: the transaction enters the data bytes at
`{AH, AL}`. -/
theorem complete_al (inputs : Nat → HostCmd.Input) (t : HostCmd.State) (first period base : Nat)
    (hp : 1 ≤ period) (ir : Bool) (a : BitVec 16) (r : BitVec 7) (B : BitVec 8)
    (h : Prog (HostCmd.stateAt inputs t (srAt first period base)) HostCmd.ST_AL ir 0 a r)
    (hc : Clean inputs t first period base)
    (hm : ∀ k, k < 8 → (inputs (srAt first period (base + k))).mosi = bit8 B (7 - k))
    (hsr : HostCmd.sr (inputs (srAt first period (base + 7))) = true)
    (hreset : (inputs (srAt first period (base + 7))).resetN = true)
    (hcs : (inputs (srAt first period (base + 7))).csN = false)
    (hack : HostCmd.ackBit (HostCmd.stateAt inputs t (srAt first period (base + 7)))
      (inputs (srAt first period (base + 7))) = false) :
    AtPhase inputs t (srAt first period (base + 7) + 1) HostCmd.ST_DATA ir
      ((a >>> 8).truncate 8 ++ B) := by
  have hb := byte_end inputs t HostCmd.ST_AL ir a r first period base hp B h hc hm
  have hstep := prog_complete_al (HostCmd.stateAt inputs t (srAt first period (base + 7)))
    (inputs (srAt first period (base + 7))) ir a
    (pack7 r (bit8 B 7) (bit8 B 6) (bit8 B 5) (bit8 B 4) (bit8 B 3) (bit8 B 2) (bit8 B 1))
    hb.1 hreset hcs hsr hack
  rw [hb.2] at hstep
  rw [← HostCmd.stateAt_succ] at hstep
  exact ⟨_, hstep⟩

/-- The idle cycles after a byte's eighth edge leave the machine at the start
of the next byte. -/
theorem settle_phase (inputs : Nat → HostCmd.Input) (t : HostCmd.State) (p : BitVec 3)
    (ir : Bool) (a : BitVec 16) (first period base : Nat) (hp : 2 ≤ period)
    (h : AtPhase inputs t (srAt first period (base + 7) + 1) p ir a)
    (hreset : ∀ j, j < srAt first period (base + 8) → (inputs j).resetN = true)
    (hcs : ∀ j, j < srAt first period (base + 8) → (inputs j).csN = false)
    (hnosr : ∀ j, srAt first period (base + 7) + 1 ≤ j → j < srAt first period (base + 8) →
      HostCmd.sr (inputs j) = false)
    (hack : ∀ j, j < srAt first period (base + 8) →
      HostCmd.ackBit (HostCmd.stateAt inputs t j) (inputs j) = false) :
    AtPhase inputs t (srAt first period (base + 8)) p ir a := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, settle_prog inputs t p ir a r first period base hp hr hreset hcs hnosr hack⟩

/-- A write data byte completes: its strobe and data appear in the next cycle. -/
theorem byte_strobe (inputs : Nat → HostCmd.Input) (t : HostCmd.State) (first period base : Nat)
    (hp : 1 ≤ period) (a : BitVec 16) (r : BitVec 7) (B : BitVec 8)
    (h : Prog (HostCmd.stateAt inputs t (srAt first period base)) HostCmd.ST_DATA false 0 a r)
    (hc : Clean inputs t first period base)
    (hm : ∀ k, k < 8 → (inputs (srAt first period (base + k))).mosi = bit8 B (7 - k))
    (hsr : HostCmd.sr (inputs (srAt first period (base + 7))) = true)
    (hreset : (inputs (srAt first period (base + 7))).resetN = true)
    (hcs : (inputs (srAt first period (base + 7))).csN = false)
    (hack : HostCmd.ackBit (HostCmd.stateAt inputs t (srAt first period (base + 7)))
      (inputs (srAt first period (base + 7))) = false) :
    Strobe (HostCmd.stateAt inputs t (srAt first period (base + 7) + 1)) a
        (shift1 (pack7 r (bit8 B 7) (bit8 B 6) (bit8 B 5) (bit8 B 4) (bit8 B 3) (bit8 B 2)
          (bit8 B 1)) (inputs (srAt first period (base + 7))).mosi) ∧
      (HostCmd.stateAt inputs t (srAt first period (base + 7) + 1)).wdata = B := by
  have hb := byte_end inputs t HostCmd.ST_DATA false a r first period base hp B h hc hm
  have hstep := prog_complete_data (HostCmd.stateAt inputs t (srAt first period (base + 7)))
    (inputs (srAt first period (base + 7))) a
    (pack7 r (bit8 B 7) (bit8 B 6) (bit8 B 5) (bit8 B 4) (bit8 B 3) (bit8 B 2) (bit8 B 1))
    hb.1 hreset hcs hsr hack
  rw [← HostCmd.stateAt_succ] at hstep
  rw [hb.2] at hstep
  exact ⟨hstep.1, hstep.2⟩

/-- One write data byte at edge index `8 * (3 + j)`: its strobe is at the byte's
address in the cycle after its eighth edge, and the next byte starts `period`
cycles after that edge, one address higher. -/
theorem data_step (inputs : Nat → HostCmd.Input) (t : HostCmd.State) (first period : Nat)
    (hp : 2 ≤ period) (A : BitVec 16) (j : Nat) (r : BitVec 7) (B : BitVec 8)
    (h : Prog (HostCmd.stateAt inputs t (srAt first period (8 * (3 + j)))) HostCmd.ST_DATA false 0
      (A + (j : BitVec 16)) r)
    (hc : Clean inputs t first period (8 * (3 + j)))
    (hreset : ∀ m, (inputs m).resetN = true)
    (hcs : ∀ m, (inputs m).csN = false)
    (hsr : ∀ k, HostCmd.sr (inputs (srAt first period k)) = true)
    (hnosr : ∀ m, (∀ k, m ≠ srAt first period k) → HostCmd.sr (inputs m) = false)
    (hack : ∀ m, HostCmd.ackBit (HostCmd.stateAt inputs t m) (inputs m) = false)
    (hm : ∀ k, k < 8 → (inputs (srAt first period (8 * (3 + j) + k))).mosi = bit8 B (7 - k)) :
    (HostCmd.stateAt inputs t (srAt first period (8 * (3 + j) + 7) + 1)).wr = true ∧
      (HostCmd.stateAt inputs t (srAt first period (8 * (3 + j) + 7) + 1)).addr =
        A + (j : BitVec 16) ∧
      (HostCmd.stateAt inputs t (srAt first period (8 * (3 + j) + 7) + 1)).wdata = B ∧
      AtByte inputs t (srAt first period (8 * (3 + (j + 1))))
        (A + ((j + 1 : Nat) : BitVec 16)) := by
  have hp1 : 1 ≤ period := by omega
  have hmosi : (inputs (srAt first period (8 * (3 + j) + 7))).mosi = bit8 B 0 := by
    have h7 := hm 7 (by decide)
    simpa using h7
  have hstr := byte_strobe inputs t first period (8 * (3 + j)) hp1
    (A + (j : BitVec 16)) r B h hc hm (hsr _) (hreset _) (hcs _) (hack _)
  rw [hmosi] at hstr
  obtain ⟨hstrobe, hwdata⟩ := hstr
  refine ⟨hstrobe.2.2.2.1, hstrobe.2.2.2.2.1, hwdata, ?_⟩
  have hidx : srAt first period (8 * (3 + j) + 7) + 1 + (period - 1) =
      srAt first period (8 * (3 + (j + 1))) := by
    rw [baseSucc]
    show srAt first period (8 * (3 + j) + 7) + 1 + (period - 1) =
      srAt first period (8 * (3 + j) + 8)
    rw [show srAt first period (8 * (3 + j) + 8) =
      srAt first period (8 * (3 + j) + 7) + period from rfl]
    omega
  have hidle : ∀ m, m < period - 1 →
      (inputs (srAt first period (8 * (3 + j) + 7) + 1 + m)).resetN = true ∧
      (inputs (srAt first period (8 * (3 + j) + 7) + 1 + m)).csN = false ∧
      HostCmd.sr (inputs (srAt first period (8 * (3 + j) + 7) + 1 + m)) = false ∧
      HostCmd.ackBit (HostCmd.stateAt
        (fun x => inputs (srAt first period (8 * (3 + j) + 7) + 1 + x))
        (HostCmd.stateAt inputs t (srAt first period (8 * (3 + j) + 7) + 1)) m)
        (inputs (srAt first period (8 * (3 + j) + 7) + 1 + m)) = false := by
    intro m hm'
    refine ⟨hreset _, hcs _, ?_, ?_⟩
    · apply hnosr
      intro k hk
      exact edge_gap first period hp1 (8 * (3 + j)) (1 + m) k (by omega) (by omega) (by omega)
    · rw [← HostCmd.stateAt_add]
      exact hack _
  have hsettle := strobe_settle
    (fun x => inputs (srAt first period (8 * (3 + j) + 7) + 1 + x))
    (HostCmd.stateAt inputs t (srAt first period (8 * (3 + j) + 7) + 1))
    (A + (j : BitVec 16))
    (shift1 (pack7 r (bit8 B 7) (bit8 B 6) (bit8 B 5) (bit8 B 4) (bit8 B 3) (bit8 B 2)
      (bit8 B 1)) (bit8 B 0))
    (period - 1) (by omega) hstrobe hidle
  rw [← HostCmd.stateAt_add, hidx, addrSucc] at hsettle
  exact ⟨_, hsettle⟩

/-- **The headline theorem.**  A mode-0 SPI write transaction on the pins - the
command byte `0x02`, the two address bytes and the data bytes, each clocked MSB
first on eight rising edges `period` cycles apart - drives one host write strobe
per data byte, with the write data equal to the clocked byte and the address
`{AH, AL} + j`, in the cycle after the byte's eighth rising edge. -/
theorem transaction_strobes (raws : Nat → BitVec 16) (rst : Nat → Bool) (initial : Sync)
    (rdData hland : Nat → Bool) (first period nbytes : Nat) (bytes : Nat → BitVec 8)
    (hp : 2 ≤ period) (hf : 3 ≤ first) (hnb : 3 ≤ nbytes)
    (hinit : initial = resetState)
    (hreset : ∀ j, rst j = true)
    (hcs : ∀ j, bit (raws j) 9 = false)
    (hrise : ∀ k, pinRise raws (srAt first period k) = true)
    (honly : ∀ m, pinRise raws m = true → ∃ k, m = srAt first period k)
    (hbit : ∀ m k, m < nbytes → k < 8 →
      bit (raws (srAt first period (8 * m + k) - 2)) 10 = bit8 (bytes m) (7 - k))
    (hcmd : bytes 0 = HostCmd.CMD_WRITE)
    (hack : ∀ j, HostCmd.ackBit
      (HostCmd.stateAt (hostInputs raws rst initial rdData hland) HostCmd.resetState j)
      (hostInputs raws rst initial rdData hland j) = false) :
    ∀ j, j + 3 < nbytes →
      (HostCmd.stateAt (hostInputs raws rst initial rdData hland) HostCmd.resetState
        (srAt first period (8 * (3 + j) + 7) + 1)).wr = true ∧
      (HostCmd.stateAt (hostInputs raws rst initial rdData hland) HostCmd.resetState
        (srAt first period (8 * (3 + j) + 7) + 1)).addr =
        (bytes 1 ++ bytes 2) + (j : BitVec 16) ∧
      (HostCmd.stateAt (hostInputs raws rst initial rdData hland) HostCmd.resetState
        (srAt first period (8 * (3 + j) + 7) + 1)).wdata = bytes (3 + j) := by
  intro j hj
  let ins := hostInputs raws rst initial rdData hland
  have hp1 : 1 ≤ period := by omega
  have hsrAll : ∀ k, HostCmd.sr (ins (srAt first period k)) = true := by
    intro k
    exact sr_of_pinRise raws rst initial rdData hland hinit hreset hcs _ (hrise k)
  have hnosrAll : ∀ m, (∀ k, m ≠ srAt first period k) → HostCmd.sr (ins m) = false := by
    intro m hm
    have hne : pinRise raws m ≠ true := by
      intro h
      obtain ⟨k, hk⟩ := honly m h
      exact hm k hk
    have hpf : pinRise raws m = false := by simpa using hne
    exact sr_of_not_pinRise raws rst initial rdData hland hinit hreset hcs m hpf
  have hclean : ∀ base, Clean ins HostCmd.resetState first period base := by
    intro base
    exact clean_of_pins raws rst initial rdData hland first period base hp1 hinit hreset hcs
      (fun k _ => hrise (base + k)) honly hack
  have hmosi8 : ∀ m k, m < nbytes → k < 8 →
      (ins (srAt first period (8 * m + k))).mosi = bit8 (bytes m) (7 - k) := by
    intro m k hm hk
    have hge : 2 ≤ srAt first period (8 * m + k) := by
      have h1 : 2 ≤ srAt first period 0 := by
        rw [show srAt first period 0 = first from rfl]
        omega
      exact Nat.le_trans h1 (srAt_le first period hp1 (Nat.zero_le (8 * m + k)))
    have h := mosi_pins_at raws rst initial rdData hland (srAt first period (8 * m + k))
      hge (hreset _) (hreset _)
    rw [h]
    exact hbit m k hm hk
  -- the idle cycles from a byte's last edge to the next byte's first edge
  have settle : ∀ base (p : BitVec 3) (ir : Bool) (a : BitVec 16),
      AtPhase ins HostCmd.resetState (srAt first period (base + 7) + 1) p ir a →
      AtPhase ins HostCmd.resetState (srAt first period (base + 8)) p ir a := by
    intro base p ir a h
    exact settle_phase ins HostCmd.resetState p ir a first period base hp h
      (fun j _ => hreset j) (fun j _ => cs_low raws rst initial rdData hland hinit hreset hcs j)
      (fun j hj1 hj2 => by
        apply hnosrAll
        intro k hk
        rcases Nat.lt_or_ge k (base + 8) with hlt | hge
        · have h1 : srAt first period k ≤ srAt first period (base + 7) :=
            srAt_le first period hp1 (by omega)
          omega
        · have h1 : srAt first period (base + 8) ≤ srAt first period k :=
            srAt_le first period hp1 hge
          omega)
      (fun j _ => hack j)
  -- the machine starts at the first edge in the reset state
  have hstart : Prog (HostCmd.stateAt ins HostCmd.resetState (srAt first period 0))
      HostCmd.ST_CMD false 0 (0 : BitVec 16) (0 : BitVec 7) := by
    have h0 : Prog HostCmd.resetState HostCmd.ST_CMD false 0 (0 : BitVec 16) (0 : BitVec 7) :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hidle : ∀ m, m < first → (ins m).resetN = true ∧ (ins m).csN = false ∧
        HostCmd.sr (ins m) = false ∧
        HostCmd.ackBit (HostCmd.stateAt ins HostCmd.resetState m) (ins m) = false := by
      intro m hm
      refine ⟨hreset m, cs_low raws rst initial rdData hland hinit hreset hcs m, ?_, hack m⟩
      apply hnosrAll
      intro k hk
      have h0' : srAt first period 0 ≤ srAt first period k :=
        srAt_le first period hp1 (Nat.zero_le k)
      have h1 : first ≤ srAt first period k := by
        rwa [show srAt first period 0 = first from rfl] at h0'
      omega
    exact prog_idle_n ins HostCmd.resetState HostCmd.ST_CMD false 0 (0 : BitVec 16)
      (0 : BitVec 7) first h0 hidle
  -- byte 0: the command byte
  have hbyte0 : AtPhase ins HostCmd.resetState (srAt first period (0 + 7) + 1)
      HostCmd.ST_AH false 0 := by
    have hb := complete_cmd ins HostCmd.resetState first period 0 hp1 false 0 0 (bytes 0)
      hstart
      (hclean 0) (fun k hk => by simpa using hmosi8 0 k (by omega) hk)
      (hsrAll _) (hreset _) (cs_low raws rst initial rdData hland hinit hreset hcs _) (hack _)
    have hcond : (HostCmd.CMD_WRITE == HostCmd.CMD_WRITE ||
        HostCmd.CMD_WRITE == HostCmd.CMD_READ) = true := by decide
    have hread : (HostCmd.CMD_WRITE == HostCmd.CMD_READ) = false := by decide
    rw [hcmd] at hb
    simpa [hcond, hread] using hb
  -- byte 1: address high
  have hbyte1 : AtPhase ins HostCmd.resetState (srAt first period (8 + 7) + 1)
      HostCmd.ST_AL false (bytes 1 ++ (0 : BitVec 8)) := by
    have hs': AtPhase ins HostCmd.resetState (srAt first period (0 + 8)) HostCmd.ST_AH false 0 :=
      settle 0 HostCmd.ST_AH false 0 hbyte0
    have hs : AtPhase ins HostCmd.resetState (srAt first period (8 + 0)) HostCmd.ST_AH false 0 := hs'
    obtain ⟨r, hr⟩ := hs
    have hb := complete_ah ins HostCmd.resetState first period 8 hp1 false 0 r (bytes 1) hr
      (hclean 8) (fun k hk => hmosi8 1 k (by omega) hk) (hsrAll _) (hreset _)
      (cs_low raws rst initial rdData hland hinit hreset hcs _) (hack _)
    simpa using hb
  -- byte 2: address low, entering the data bytes
  have hbyte2 : AtByte ins HostCmd.resetState (srAt first period (16 + 8)) (bytes 1 ++ bytes 2) := by
    have hs2 : AtPhase ins HostCmd.resetState (srAt first period (8 + 8)) HostCmd.ST_AL false
        (bytes 1 ++ (0 : BitVec 8)) :=
      settle 8 HostCmd.ST_AL false (bytes 1 ++ (0 : BitVec 8)) hbyte1
    have hs : AtPhase ins HostCmd.resetState (srAt first period (16 + 0)) HostCmd.ST_AL false
        (bytes 1 ++ (0 : BitVec 8)) := hs2
    obtain ⟨r, hr⟩ := hs
    have hb := complete_al ins HostCmd.resetState first period 16 hp1 false
      (bytes 1 ++ (0 : BitVec 8)) r (bytes 2) hr (hclean 16)
      (fun k hk => hmosi8 2 k (by omega) hk) (hsrAll _) (hreset _)
      (cs_low raws rst initial rdData hland hinit hreset hcs _) (hack _)
    simp only [highByte] at hb
    exact settle 16 HostCmd.ST_DATA false (bytes 1 ++ bytes 2) hb
  -- the data bytes
  have hdata : ∀ j, j + 3 < nbytes →
      AtByte ins HostCmd.resetState (srAt first period (8 * (3 + j)))
          ((bytes 1 ++ bytes 2) + (j : BitVec 16)) ∧
      (HostCmd.stateAt ins HostCmd.resetState (srAt first period (8 * (3 + j) + 7) + 1)).wr = true ∧
      (HostCmd.stateAt ins HostCmd.resetState
          (srAt first period (8 * (3 + j) + 7) + 1)).addr =
            (bytes 1 ++ bytes 2) + (j : BitVec 16) ∧
      (HostCmd.stateAt ins HostCmd.resetState
          (srAt first period (8 * (3 + j) + 7) + 1)).wdata = bytes (3 + j) ∧
      AtByte ins HostCmd.resetState (srAt first period (8 * (3 + (j + 1))))
          ((bytes 1 ++ bytes 2) + ((j + 1 : Nat) : BitVec 16)) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h0 : AtByte ins HostCmd.resetState (srAt first period (8 * (3 + 0)))
          ((bytes 1 ++ bytes 2) + (0 : BitVec 16)) := by
        simpa using hbyte2
      obtain ⟨r, hr⟩ := h0
      have h0' : AtByte ins HostCmd.resetState (srAt first period (8 * (3 + 0)))
          ((bytes 1 ++ bytes 2) + (0 : BitVec 16)) := ⟨r, hr⟩
      have hstep := data_step ins HostCmd.resetState first period hp (bytes 1 ++ bytes 2) 0 r
        (bytes 3) hr (hclean _) (fun m => hreset m)
        (fun m => cs_low raws rst initial rdData hland hinit hreset hcs m) hsrAll hnosrAll
        (fun m => hack m) (fun k hk => hmosi8 3 k (by omega) hk)
      exact ⟨h0', hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2⟩
    | succ j ih =>
      intro hj
      obtain ⟨_, _, _, _, hnext⟩ := ih (by omega)
      obtain ⟨r, hr⟩ := hnext
      have hnext' : AtByte ins HostCmd.resetState (srAt first period (8 * (3 + (j + 1))))
          ((bytes 1 ++ bytes 2) + ((j + 1 : Nat) : BitVec 16)) := ⟨r, hr⟩
      have hstep := data_step ins HostCmd.resetState first period hp (bytes 1 ++ bytes 2) (j + 1) r
        (bytes (3 + (j + 1))) hr (hclean _) (fun m => hreset m)
        (fun m => cs_low raws rst initial rdData hland hinit hreset hcs m) hsrAll hnosrAll
        (fun m => hack m) (fun k hk => hmosi8 (3 + (j + 1)) k (by omega) hk)
      exact ⟨hnext', hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2⟩
  exact ⟨(hdata j hj).2.1, (hdata j hj).2.2.1, (hdata j hj).2.2.2.1⟩

end Metronome.SpiPins
