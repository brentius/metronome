import Metronome.Compose

set_option autoImplicit false

namespace Metronome.Host

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 3acc7dc6dc96e5a98b4a8c0ed0fbb4b3637f139052a13e6ad43c0ea033afd127
-- The guest state `st` and the command latch `is_rd` are free per-cycle
-- inputs here. Their own next-state equations are outside this cut.
def rtlStep (state : State) (input : Input) : State :=
  let host0 := !input.csN
  let host1 := host0 && input.sck
  let host2 := !input.sckPrev
  let host3 := host1 && host2
  let host4 := (state.bitc != (7 : BitVec 3))
  let host5 := (state.bitc + (1 : BitVec 3))
  let host6 := if host4 then host5 else (0 : BitVec 3)
  let host7 := if host3 then host6 else state.bitc
  let host8 := if input.csN then (0 : BitVec 3) else host7
  let host9 := if input.resetN then host8 else (0 : BitVec 3)
  let host10 := (input.st == (3 : BitVec 3))
  let host11 := if input.isRd then false else true
  let host12 := if host10 then host11 else false
  let host13 := if host4 then false else host12
  let host14 := if host3 then host13 else false
  let host15 := if input.csN then false else host14
  let host16 := if input.resetN then host15 else false
  ⟨host16, host9⟩

end Metronome.Host

namespace Metronome.Compose

/-- The Python adapter checked that the elaborated `cfg_host_now` net is
exactly `((u_host.wr & in_cfg) & live)` with this definition's leaf order. -/
theorem chipHostValid_witness : chipHostValid true true true = true := rfl

end Metronome.Compose

namespace Metronome.Host

/-- The extracted transition matches the specification for every state and
input. `st` and `is_rd` are symbolic, so their own RTL equations are not part
of this cut. -/
theorem rtlStep_eq_step (state : State) (input : Input) :
    rtlStep state input = step state input := by
  obtain ⟨wr, bitc⟩ := state
  obtain ⟨resetN, sck, sckPrev, csN, st, isRd⟩ := input
  by_cases count : bitc = 7 <;> by_cases data : st = 3 <;>
    cases resetN <;> cases sck <;> cases sckPrev <;> cases csN <;> cases isRd <;>
    simp [rtlStep, step, wrNext, bitcNext, count, data] <;> rfl

def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun state input => rtlStep state input) inputs initial n

theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt inputs initial n :=
  run_congr (fun state input => rtlStep_eq_step state input) inputs initial n

theorem rtl_trace_result (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStep (rtlStateAt inputs initial n) (inputs n) =
      step (stateAt inputs initial n) (inputs n) := by
  rw [rtlStateAt_eq, rtlStep_eq_step]

theorem rtl_trace_spacing (inputs : Nat → Input) (initial : State) (n : Nat) :
    (rtlStateAt inputs initial (n + 1)).wr = true →
      (rtlStateAt inputs initial (n + 2)).wr = false := by
  rw [rtlStateAt_eq, rtlStateAt_eq]
  exact trace_spacing inputs initial n

theorem rtl_wr_next_bitc_zero (state : State) (input : Input)
    (write : (rtlStep state input).wr = true) : (rtlStep state input).bitc = 0 := by
  rw [rtlStep_eq_step] at write ⊢
  exact wr_next_bitc_zero state input write

theorem rtl_bitc_ne_seven_excludes_wr (state : State) (input : Input)
    (count : state.bitc ≠ 7) : (rtlStep state input).wr = false := by
  rw [rtlStep_eq_step]
  exact bitc_ne_seven_excludes_wr state input count

/-- info: 'Metronome.Host.rtlStep_eq_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtlStep_eq_step

/-- info: 'Metronome.Host.rtl_trace_spacing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtl_trace_spacing

/-- info: 'Metronome.Host.rtl_wr_next_bitc_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtl_wr_next_bitc_zero

/-- info: 'Metronome.Host.rtl_bitc_ne_seven_excludes_wr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtl_bitc_ne_seven_excludes_wr

end Metronome.Host
