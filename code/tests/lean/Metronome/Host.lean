import Metronome.Transition

/-!
# Host write strobe and byte counter

This module specifies the two registers that gate a host write from the SPI
target in `src/md2_host.v`: the registered write strobe `wr` and the 3-bit bit
counter `bitc`.  It is the first cut needed to discharge
`Metronome.Config.SpacedHost` from the actual chip top.

The reduced state keeps only `wr` and `bitc`.  The byte state `st` and the
command latch `is_rd` influence `wr` but are not otherwise modelled here, so
they are per-cycle inputs.  Treating them as free inputs is an
over-approximation of the real circuit and is therefore sound for the safety
properties below; their own next-state equations, the SPI pin timing and the
command decode are separate obligations.

The name `bitc` and the constants follow `md2_host.v`: `ST_DATA = 3'd3` and a
byte completes on the eighth rising edge (`bitc == 7`).

## Cycle boundary

`stateAt inputs initial n` is the register state during chip cycle `n`, after
`n` sampled edges.  The one-step facts constrain the *next* strobe from the
current state.  Consequently, two adjacent strobes in cycles `n+1` and `n+2`
are impossible for every `n`, but the pair in cycles `0` and `1` involves the
arbitrary power-up value of `wr` and is not covered.  A sampled reset edge
ends cycle 0 and leaves `resetState` (`wr = false`, `bitc = 0`) for cycle 1,
so a trace started in `resetState` covers cycle 0 explicitly.  The
`powerup_boundary_witness` below shows that this reset-state premise is
necessary.
-/

namespace Metronome.Host

structure State where
  wr : Bool
  bitc : BitVec 3
  deriving DecidableEq, Repr

/-- The state left by a sampled reset edge (`rst_n` low at the clock). -/
def resetState : State := ⟨false, 0⟩

/-- Sampled host-link inputs. `st` and `isRd` are the values of the host
state registers in this cycle, kept symbolic. -/
structure Input where
  resetN : Bool
  sck : Bool
  sckPrev : Bool
  csN : Bool
  st : BitVec 3
  isRd : Bool
  deriving DecidableEq, Repr

/-- SPEC_V2 §9: a write issues on the cycle after the eighth bit of a data
byte while the command byte was `0x02`.  `ST_DATA = 3`. -/
def wrNext (state : State) (input : Input) : Bool :=
  input.resetN && !input.csN && input.sck && !input.sckPrev &&
    (state.bitc == 7) && (input.st == 3) && !input.isRd

/-- SPEC_V2 §9: reset or deasserted CS_N clears the bit count; an accepted bit
increments it, wrapping from 7 to 0 on the completing edge. -/
def bitcNext (state : State) (input : Input) : BitVec 3 :=
  if !input.resetN then 0
  else if input.csN then 0
  else if input.sck && !input.sckPrev then
    if state.bitc == 7 then 0 else state.bitc + 1
  else state.bitc

def step (state : State) (input : Input) : State :=
  ⟨wrNext state input, bitcNext state input⟩

theorem wr_next_bitc_zero (state : State) (input : Input)
    (write : wrNext state input = true) : bitcNext state input = 0 := by
  unfold wrNext at write
  simp only [Bool.and_eq_true] at write
  obtain ⟨⟨⟨⟨⟨⟨reset, cs⟩, sck⟩, sckPrev⟩, count⟩, _state⟩, _read⟩ := write
  have csFalse : input.csN = false := by simpa using cs
  have sckPrevFalse : input.sckPrev = false := by simpa using sckPrev
  unfold bitcNext
  rw [reset, csFalse, count]
  simp [sck, sckPrevFalse]

theorem bitc_ne_seven_excludes_wr (state : State) (input : Input)
    (count : state.bitc ≠ 7) : wrNext state input = false := by
  unfold wrNext
  rw [show (state.bitc == 7) = false from beq_eq_false_iff_ne.mpr count]
  simp

theorem wr_next_bitc_seven (state : State) (input : Input)
    (write : wrNext state input = true) : state.bitc = 7 := by
  by_cases count : state.bitc = 7
  · exact count
  · have excluded := bitc_ne_seven_excludes_wr state input count
    rw [excluded] at write
    cases write

theorem reset_clears (state : State) (input : Input) (reset : input.resetN = false) :
    (step state input).wr = false ∧ (step state input).bitc = 0 := by
  simp [step, wrNext, bitcNext, reset]

def stateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun state input => step state input) inputs initial n

theorem stateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    stateAt inputs initial (n + 1) = step (stateAt inputs initial n) (inputs n) := rfl

/-- A sampled reset edge leaves the reset state, whatever the prior values. -/
theorem reset_state_after_edge (inputs : Nat → Input) (initial : State)
    (reset : (inputs 0).resetN = false) :
    stateAt inputs initial 1 = resetState := by
  obtain ⟨write, count⟩ := reset_clears initial (inputs 0) reset
  show step initial (inputs 0) = resetState
  rw [show step initial (inputs 0) =
        ⟨(step initial (inputs 0)).wr, (step initial (inputs 0)).bitc⟩ from rfl, write, count]
  rfl

/-- No two adjacent host write strobes in cycles `n+1` and `n+2`, for any
sampled input trace.  The state that produced cycle `n+1` is `stateAt n`; the
state that produced cycle `n+2` is `stateAt (n+1)`.  Cycle 0 is not in this
statement: see the module note. -/
theorem trace_spacing (inputs : Nat → Input) (initial : State) (n : Nat) :
    (stateAt inputs initial (n + 1)).wr = true →
      (stateAt inputs initial (n + 2)).wr = false := by
  intro write
  cases following : (stateAt inputs initial (n + 2)).wr with
  | false => rfl
  | true =>
    exfalso
    have write' : wrNext (stateAt inputs initial n) (inputs n) = true := by
      change (stateAt inputs initial (n + 1)).wr = true
      exact write
    have following' : wrNext (stateAt inputs initial (n + 1)) (inputs (n + 1)) = true := by
      change (stateAt inputs initial (n + 2)).wr = true
      exact following
    have zero : (stateAt inputs initial (n + 1)).bitc = 0 := by
      change bitcNext (stateAt inputs initial n) (inputs n) = 0
      exact wr_next_bitc_zero _ _ write'
    have seven : (stateAt inputs initial (n + 1)).bitc = 7 :=
      wr_next_bitc_seven _ _ following'
    rw [zero] at seven
    exact absurd seven (by decide)

/-- The same spacing result with an explicit sampled reset at cycle 0.  The
reset establishes `stateAt 1 = resetState`; the theorem itself only uses the
local next-state facts, so it needs no further reset assumption. -/
theorem trace_spacing_after_reset (inputs : Nat → Input) (initial : State)
    (_reset : (inputs 0).resetN = false) (n : Nat) :
    (stateAt inputs initial (n + 1)).wr = true →
      (stateAt inputs initial (n + 2)).wr = false := by
  intro write
  exact trace_spacing inputs initial n write

/-- Without a reset-state start, an arbitrary power-up `wr = 1` (with
`bitc = 7`) can be followed by another strobe in cycle 1.  This is why the
composition below starts from `resetState`. -/
theorem powerup_boundary_witness :
    let initial : State := ⟨true, 7⟩
    let inputs : Nat → Input :=
      fun _ => ⟨true, true, false, false, 3, false⟩
    (stateAt inputs initial 0).wr = true ∧ (stateAt inputs initial 1).wr = true := by
  simp [stateAt, Metronome.run, step, wrNext]

end Metronome.Host
