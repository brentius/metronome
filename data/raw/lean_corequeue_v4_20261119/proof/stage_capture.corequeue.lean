import Metronome.CoreQueue

set_option autoImplicit false

namespace Metronome.CoreQueue

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: 3d61d82aec9093e10406e9e475ff3efedbfdccd39fd606796a127b89b505ee0f
-- `w_cw` (the picked CW group), `frz`, `cfg_core_issue`, `cw_is_cfg` and the
-- `CTRL.STICKY` clear leaf `c_wr_stk & h_wd[2]` are free per-cycle inputs.
def rtlStep (state : State) (input : Input) : State :=
  let cwq0 := ((BitVec.truncate 6 (BitVec.ushiftRight input.cw 8)) == (60 : BitVec 6))
  let cwq1 := ((BitVec.truncate 1 (BitVec.ushiftRight input.cw 14)) != 0) && cwq0
  let cwq2 := !state.pending
  let cwq3 := !input.frz
  let cwq4 := state.pending && cwq3
  let cwq5 := !input.isCfg
  let cwq6 := cwq5 || input.coreIssue
  let cwq7 := cwq4 && cwq6
  let cwq8 := cwq2 || cwq7
  let cwq9 := cwq1 && cwq8
  let cwq10 := (state.addr + (1 : BitVec 16))
  let cwq11 := ((BitVec.truncate 6 (BitVec.ushiftRight input.cw 8)) == (58 : BitVec 6))
  let cwq12 := ((BitVec.truncate 1 (BitVec.ushiftRight input.cw 14)) != 0) && cwq11
  let cwq13 := if cwq12 then (BitVec.truncate 8 (BitVec.ushiftRight input.cw 0)) else (BitVec.truncate 8 (BitVec.ushiftRight state.addr 0))
  let cwq14 := if cwq9 then ((if ((BitVec.truncate 1 (BitVec.ushiftRight cwq10 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 0) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq10 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 1) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq10 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 2) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq10 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 3) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq10 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 4) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq10 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 5) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq10 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 6) else (0 : BitVec 8)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq10 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 8) 7) else (0 : BitVec 8))) else cwq13
  let cwq15 := if input.resetN then cwq14 else (0 : BitVec 8)
  let cwq16 := ((BitVec.truncate 6 (BitVec.ushiftRight input.cw 8)) == (59 : BitVec 6))
  let cwq17 := ((BitVec.truncate 1 (BitVec.ushiftRight input.cw 14)) != 0) && cwq16
  let cwq18 := if cwq17 then (BitVec.truncate 8 (BitVec.ushiftRight input.cw 0)) else (BitVec.truncate 8 (BitVec.ushiftRight state.addr 8))
  let cwq19 := if cwq12 then (BitVec.truncate 8 (BitVec.ushiftRight state.addr 8)) else cwq18
  let cwq20 := if cwq9 then (BitVec.truncate 8 (BitVec.ushiftRight cwq10 8)) else cwq19
  let cwq21 := if input.resetN then cwq20 else (0 : BitVec 8)
  let cwq22 := if cwq7 then false else state.pending
  let cwq23 := if cwq9 then true else cwq22
  let cwq24 := if input.resetN then cwq23 else false
  let cwq25 := if cwq9 then state.addr else state.pendingAddr
  let cwq26 := if input.resetN then cwq25 else (0 : BitVec 16)
  let cwq27 := if cwq9 then (BitVec.truncate 8 (BitVec.ushiftRight input.cw 0)) else state.pendingData
  let cwq28 := if input.resetN then cwq27 else (0 : BitVec 8)
  let cwq29 := !cwq9
  let cwq30 := cwq1 && cwq29
  let cwq31 := input.clearSticky && ((BitVec.truncate 1 (BitVec.ushiftRight input.hostData 2)) != 0)
  let cwq32 := !cwq31
  let cwq33 := state.overrun && cwq32
  let cwq34 := cwq30 || cwq33
  let cwq35 := if input.resetN then cwq34 else false
  { addr := ((if ((BitVec.truncate 1 (BitVec.ushiftRight cwq15 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 0) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq15 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 1) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq15 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 2) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq15 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 3) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq15 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 4) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq15 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 5) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq15 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 6) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq15 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 7) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq21 0)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 8) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq21 1)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 9) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq21 2)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 10) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq21 3)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 11) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq21 4)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 12) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq21 5)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 13) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq21 6)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 14) else (0 : BitVec 16)) ||| (if ((BitVec.truncate 1 (BitVec.ushiftRight cwq21 7)) != 0) then (BitVec.shiftLeft (1 : BitVec 16) 15) else (0 : BitVec 16)))
    pending := cwq24
    pendingAddr := cwq26
    pendingData := cwq28
    overrun := cwq35 }

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
