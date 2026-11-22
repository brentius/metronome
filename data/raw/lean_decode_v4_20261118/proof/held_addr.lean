import Metronome.Config

set_option autoImplicit false

namespace Metronome.Config

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: d2c5c719c3d97bcca3f5220d253acd62db2f37422a1c7889051005764c5f11bf
def rtlStep (state : State) (input : Input) : Result :=
  let previousWrite := input.resetN && state.previousWrite
  let arb0 := !previousWrite
  let arb1 := input.coreValid && arb0
  let arb2 := !previousWrite
  let arb3 := input.hostValid && arb2
  let arb4 := state.heldValid || arb3
  let arb5 := !arb4
  let arb6 := arb1 && arb5
  let arb7 := arb4 || arb6
  let arb8 := if arb4 then input.host.addr else input.core.addr
  let arb9 := if state.heldValid then state.held.addr else arb8
  let arb10 := if arb4 then input.host.data else input.core.data
  let arb11 := if state.heldValid then state.held.data else arb10
  let arb12 := input.hostValid && previousWrite
  let arb13 := if input.resetN then arb12 else false
  let arb14 := if arb12 then input.core.addr else state.held.addr
  let arb15 := if arb12 then input.host.data else state.held.data
  let stage0 := if arb7 then arb11 else state.staged.data
  { coreIssue := arb6
    bankWrite := arb7
    bank := ⟨arb9, arb11⟩
    next := { previousWrite := (input.resetN && arb7)
              heldValid := arb13
              held := ⟨arb14, arb15⟩
              staged := ⟨arb9, stage0⟩ } }

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
