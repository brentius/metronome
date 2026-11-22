import Metronome.CoreQueue

set_option autoImplicit false

namespace Metronome.CoreQueue

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 1ea3808da85bf029c9212784491b1bc16e3ab5884eaa8cbd4c6d9e1aab063e39
-- `w_cw` (the picked CW group), `frz`, `cfg_core_issue`, `cw_is_cfg` and the
-- `CTRL.STICKY` clear leaf `c_wr_stk & h_wd[2]` are free per-cycle inputs.
def rtlStep (state : State) (input : Input) : State :=
  let cwq0 := ((BitVec.truncate 6 (BitVec.ushiftRight input.cw 8)) == (60 : BitVec 6))
  let cwq1 := ((BitVec.truncate 1 (BitVec.ushiftRight input.cw 14)) != 0) && cwq0
  let cwq2 := !state.pending
  let cwq3 := !input.isCfg
  let cwq4 := cwq3 || input.coreIssue
  let cwq5 := state.pending && cwq4
  let cwq6 := cwq2 || cwq5
  let cwq7 := cwq1 && cwq6
  let cwq8 := (state.addr + (1 : BitVec 16))
  let cwq9 := ((BitVec.truncate 6 (BitVec.ushiftRight input.cw 8)) == (58 : BitVec 6))
  let cwq10 := ((BitVec.truncate 1 (BitVec.ushiftRight input.cw 14)) != 0) && cwq9
  let cwq11 := if cwq10 then (BitVec.truncate 8 (BitVec.ushiftRight input.cw 0)) else (BitVec.truncate 8 (BitVec.ushiftRight state.addr 0))
  let cwq12 := if cwq7 then ((if ((BitVec.truncate 1 (BitVec.ushiftRight cwq8 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq8 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq8 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq8 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq8 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq8 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq8 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq8 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else cwq11
  let cwq13 := if input.resetN then cwq12 else (0 : BitVec 8)
  let cwq14 := ((BitVec.truncate 6 (BitVec.ushiftRight input.cw 8)) == (59 : BitVec 6))
  let cwq15 := ((BitVec.truncate 1 (BitVec.ushiftRight input.cw 14)) != 0) && cwq14
  let cwq16 := if cwq15 then (BitVec.truncate 8 (BitVec.ushiftRight input.cw 0)) else (BitVec.truncate 8 (BitVec.ushiftRight state.addr 8))
  let cwq17 := if cwq10 then (BitVec.truncate 8 (BitVec.ushiftRight state.addr 8)) else cwq16
  let cwq18 := if cwq7 then (BitVec.truncate 8 (BitVec.ushiftRight cwq8 8)) else cwq17
  let cwq19 := if input.resetN then cwq18 else (0 : BitVec 8)
  let cwq20 := if cwq5 then false else state.pending
  let cwq21 := if cwq7 then true else cwq20
  let cwq22 := if input.resetN then cwq21 else false
  let cwq23 := if cwq7 then state.addr else state.pendingAddr
  let cwq24 := if input.resetN then cwq23 else (0 : BitVec 16)
  let cwq25 := if cwq7 then (BitVec.truncate 8 (BitVec.ushiftRight input.cw 0)) else state.pendingData
  let cwq26 := if input.resetN then cwq25 else (0 : BitVec 8)
  let cwq27 := !cwq7
  let cwq28 := cwq1 && cwq27
  let cwq29 := input.clearSticky && ((BitVec.truncate 1 (BitVec.ushiftRight input.hostData 2)) != 0)
  let cwq30 := !cwq29
  let cwq31 := state.overrun && cwq30
  let cwq32 := cwq28 || cwq31
  let cwq33 := if input.resetN then cwq32 else false
  { addr := ((if ((BitVec.truncate 1 (BitVec.ushiftRight cwq13 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq13 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq13 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq13 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq13 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq13 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq13 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq13 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq19 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq19 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq19 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq19 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq19 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq19 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq19 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq19 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16)))
    pending := cwq22
    pendingAddr := cwq24
    pendingData := cwq26
    overrun := cwq33 }

end Metronome.CoreQueue

namespace Metronome.CoreQueue

/-- The extracted transition matches the independent SPEC_V2 §13.1 queue
specification for every state and input.  `state.addr`, the 15-bit picked CW
group and the free leaves are all symbolic. -/
theorem rtlStep_eq_step (state : State) (input : Input) :
    rtlStep state input = step state input := by
  apply State.ext <;> rfl

def rtlStateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun state input => rtlStep state input) inputs initial n

theorem rtlStateAt_eq (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStateAt inputs initial n = stateAt inputs initial n :=
  run_congr (fun state input => rtlStep_eq_step state input) inputs initial n

theorem rtl_trace_result (inputs : Nat → Input) (initial : State) (n : Nat) :
    rtlStep (rtlStateAt inputs initial n) (inputs n) =
      step (stateAt inputs initial n) (inputs n) := by
  rw [rtlStateAt_eq, rtlStep_eq_step]

theorem rtl_trace_held_until_drain (inputs : Nat → Input) (initial : State)
    (m n : Nat) (order : m ≤ n)
    (pending : (rtlStateAt inputs initial m).pending = true)
    (noDrain : ∀ k, m ≤ k → k < n →
      drain (rtlStateAt inputs initial k) (inputs k) = false)
    (noReset : ∀ k, m ≤ k → k < n → (inputs k).resetN = true) :
    (rtlStateAt inputs initial n).pending = true ∧
      (rtlStateAt inputs initial n).pendingAddr =
        (rtlStateAt inputs initial m).pendingAddr ∧
      (rtlStateAt inputs initial n).pendingData =
        (rtlStateAt inputs initial m).pendingData := by
  rw [rtlStateAt_eq inputs initial m] at pending
  rw [rtlStateAt_eq inputs initial n, rtlStateAt_eq inputs initial m]
  exact trace_held_until_drain inputs initial m n order pending
    (fun k le lt => by simpa only [rtlStateAt_eq] using noDrain k le lt) noReset

theorem rtl_trace_drain_delivers (inputs : Nat → Input) (initial : State)
    (m n : Nat) (order : m + 1 ≤ n)
    (accepted : accept (rtlStateAt inputs initial m) (inputs m) = true)
    (resetM : (inputs m).resetN = true)
    (noDrain : ∀ k, m + 1 ≤ k → k < n →
      drain (rtlStateAt inputs initial k) (inputs k) = false)
    (noReset : ∀ k, m + 1 ≤ k → k < n → (inputs k).resetN = true)
    (drained : drain (rtlStateAt inputs initial n) (inputs n) = true) :
    drain (rtlStateAt inputs initial n) (inputs n) = true ∧
      delivered (rtlStateAt inputs initial n) =
        acceptedWrite (rtlStateAt inputs initial m) (inputs m) := by
  rw [rtlStateAt_eq inputs initial m] at accepted
  rw [rtlStateAt_eq inputs initial n] at drained
  rw [rtlStateAt_eq inputs initial n, rtlStateAt_eq inputs initial m]
  exact trace_drain_delivers_accepted inputs initial m n order accepted resetM
    (fun k le lt => by simpa only [rtlStateAt_eq] using noDrain k le lt) noReset drained

theorem rtl_trace_drain_empties (inputs : Nat → Input) (initial : State) (n : Nat)
    (drained : drain (rtlStateAt inputs initial n) (inputs n) = true)
    (noAccept : accept (rtlStateAt inputs initial n) (inputs n) = false)
    (reset : (inputs n).resetN = true) :
    (rtlStateAt inputs initial (n + 1)).pending = false := by
  rw [rtlStateAt_eq inputs initial n] at drained noAccept
  rw [rtlStateAt_eq inputs initial (n + 1)]
  exact trace_drain_empties inputs initial n drained noAccept reset

theorem rtl_accepted_or_overrun (state : State) (input : Input)
    (reset : input.resetN = true) (write : writeData input = true)
    (dropped : accept state input = false) :
    (rtlStep state input).overrun = true := by
  rw [rtlStep_eq_step]
  exact accepted_or_overrun state input reset write dropped

theorem rtl_frz_holds (state : State) (input : Input)
    (frozen : input.frz = true) (pending : state.pending = true)
    (reset : input.resetN = true) :
    (rtlStep state input).pending = true ∧
      (rtlStep state input).pendingAddr = state.pendingAddr ∧
      (rtlStep state input).pendingData = state.pendingData := by
  rw [rtlStep_eq_step]
  obtain ⟨held, heldAddr, heldData, _⟩ := frz_holds state input frozen pending reset
  exact ⟨held, heldAddr, heldData⟩

theorem rtl_step_increments (state : State) (input : Input)
    (accepted : accept state input = true) (reset : input.resetN = true) :
    (rtlStep state input).addr = state.addr + 1 := by
  rw [rtlStep_eq_step]
  exact accept_increments state input accepted reset

/-- info: 'Metronome.CoreQueue.rtlStep_eq_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rtlStep_eq_step

/-- info: 'Metronome.CoreQueue.rtl_trace_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rtl_trace_result

end Metronome.CoreQueue
