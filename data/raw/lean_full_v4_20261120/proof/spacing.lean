import Metronome.Config

set_option autoImplicit false

namespace Metronome.Config

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 8430f424f6d5458dfd6a75e99c841ed68b8e7935320a3bd906287206ad498bc9
def rtlStep (state : State) (input : Input) : Result :=
  let previousWrite := input.resetN && state.previousWrite
  let arb0 := !previousWrite
  let arb1 := input.hostValid && arb0
  let arb2 := state.heldValid || arb1
  let arb3 := !arb2
  let arb4 := input.coreValid && arb3
  let arb5 := arb2 || arb4
  let arb6 := if arb2 then input.host.addr else input.core.addr
  let arb7 := if state.heldValid then state.held.addr else arb6
  let arb8 := if arb2 then input.host.data else input.core.data
  let arb9 := if state.heldValid then state.held.data else arb8
  let arb10 := input.hostValid && previousWrite
  let arb11 := if input.resetN then arb10 else false
  let arb12 := if arb10 then input.host.addr else state.held.addr
  let arb13 := if arb10 then input.host.data else state.held.data
  let stage0 := if arb5 then arb9 else state.staged.data
  { coreIssue := arb4
    bankWrite := arb5
    bank := ⟨arb7, arb9⟩
    next := { previousWrite := (input.resetN && arb5)
              heldValid := arb11
              held := ⟨arb12, arb13⟩
              staged := ⟨arb7, stage0⟩ } }

end Metronome.Config

namespace Metronome.Config

/-- All payloads and current register values are symbolic in this check. -/
theorem rtlStep_eq_step (state : State) (input : Input) :
    rtlStep state input = step state input := by
  obtain ⟨previous, held, _, _⟩ := state
  obtain ⟨resetN, hostValid, _, coreValid, _⟩ := input
  cases resetN <;> cases previous <;> cases held <;>
    cases hostValid <;> cases coreValid <;> rfl

def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => (rtlStep s i).next) inputs initial n

theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt inputs initial n :=
  run_congr (fun s i => congrArg Result.next (rtlStep_eq_step s i)) inputs initial n

theorem rtl_trace_result (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStep (rtlStateAt inputs initial n) (inputs n) =
      step (stateAt inputs initial n) (inputs n) := by
  rw [rtlStateAt_eq, rtlStep_eq_step]

theorem rtl_trace_spacing (inputs : Nat → Input) (initial : State)
    (reset : (inputs 0).resetN = false) (n : Nat)
    (active : (inputs (n + 1)).resetN = true)
    (followingActive : (inputs (n + 2)).resetN = true)
    (write : (rtlStep (rtlStateAt inputs initial (n + 1)) (inputs (n + 1))).bankWrite = true) :
    (rtlStep (rtlStateAt inputs initial (n + 2)) (inputs (n + 2))).bankWrite = false := by
  rw [rtl_trace_result] at write ⊢
  exact trace_spacing inputs initial reset n active followingActive write

theorem rtl_trace_host_service (inputs : Nat → Input) (initial : State)
    (reset : (inputs 0).resetN = false) (spaced : SpacedHost inputs) (n : Nat)
    (active : (inputs (n + 1)).resetN = true) (host : (inputs (n + 1)).hostValid = true) :
    let state := rtlStateAt inputs initial (n + 1)
    let input := inputs (n + 1)
    if state.previousWrite then
      (rtlStep state input).bankWrite = false ∧
        ((inputs (n + 2)).resetN = true →
          HostIssued (rtlStep (rtlStateAt inputs initial (n + 2)) (inputs (n + 2))) input.host)
    else HostIssued (rtlStep state input) input.host := by
  simpa only [rtlStateAt_eq, rtlStep_eq_step] using
    trace_host_service inputs initial reset spaced n active host

/-- info: 'Metronome.Config.rtlStep_eq_step' does not depend on any axioms -/
#guard_msgs in #print axioms rtlStep_eq_step

/-- info: 'Metronome.Config.rtl_trace_result' does not depend on any axioms -/
#guard_msgs in #print axioms rtl_trace_result

/-- info: 'Metronome.Config.rtl_trace_spacing' depends on axioms: [propext] -/
#guard_msgs in #print axioms rtl_trace_spacing

/-- info: 'Metronome.Config.rtl_trace_host_service' depends on axioms: [propext] -/
#guard_msgs in #print axioms rtl_trace_host_service

end Metronome.Config
