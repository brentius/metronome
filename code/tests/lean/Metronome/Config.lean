import Metronome.Transition

namespace Metronome.Config

structure Write where
  addr : BitVec 9
  data : BitVec 8
  deriving DecidableEq, Repr

/-- Register state at the configuration arbiter and common write stage. -/
structure State where
  previousWrite : Bool
  heldValid : Bool
  held : Write
  staged : Write
  deriving DecidableEq, Repr

structure Input where
  resetN : Bool
  hostValid : Bool
  host : Write
  coreValid : Bool
  core : Write
  deriving DecidableEq, Repr

structure Result where
  bankWrite : Bool
  coreIssue : Bool
  bank : Write
  next : State
  deriving DecidableEq, Repr

inductive Grant where
  | host (write : Write)
  | core (write : Write)
  | idle

/-- The stage strobe has an asynchronous clear. The arbiter's valid bit does not. -/
def beforeEdge (state : State) (input : Input) : State :=
  { state with previousWrite := input.resetN && state.previousWrite }

/-- SPEC_V2 §13.1 priority at the single configuration write port. -/
def grant (state : State) (input : Input) : Grant :=
  if state.heldValid then .host state.held
  else if state.previousWrite then .idle
  else if input.hostValid then .host input.host
  else if input.coreValid then .core input.core
  else .idle

/-- One sampled edge. The payloads retain their RTL values even when invalid. -/
def step (state : State) (input : Input) : Result :=
  let state := beforeEdge state input
  let (bankWrite, coreIssue, bank) :=
    match grant state input with
    | .host write => (true, false, write)
    | .core write => (true, true, write)
    | .idle => (false, false, input.core)
  let holdHost := state.previousWrite && input.hostValid
  { bankWrite, coreIssue, bank
    next :=
      { previousWrite := input.resetN && bankWrite
        heldValid := input.resetN && holdHost
        held := if holdHost then input.host else state.held
        staged :=
          { addr := bank.addr
            data := if bankWrite then bank.data else state.staged.data } } }

def Safe (state : State) : Prop :=
  state.heldValid = true → state.previousWrite = false

theorem safe_reset (state : State) (input : Input) (reset : input.resetN = false) :
    Safe (step state input).next := by
  obtain ⟨previous, held, _, _⟩ := state
  obtain ⟨resetN, hostValid, _, coreValid, _⟩ := input
  cases resetN <;> cases previous <;> cases held <;>
    cases hostValid <;> cases coreValid <;> simp_all [Safe, step, grant, beforeEdge]

theorem safe_step (state : State) (input : Input) (safe : Safe state) :
    Safe (step state input).next := by
  obtain ⟨previous, held, _, _⟩ := state
  obtain ⟨resetN, hostValid, _, coreValid, _⟩ := input
  cases resetN <;> cases previous <;> cases held <;>
    cases hostValid <;> cases coreValid <;> simp_all [Safe, step, grant, beforeEdge]

theorem no_back_to_back (state : State) (input : Input) (safe : Safe state)
    (active : input.resetN = true)
    (busy : state.previousWrite = true) : (step state input).bankWrite = false := by
  cases held : state.heldValid
  · simp [step, grant, beforeEdge, held, busy, active]
  · simp [Safe, held, busy] at safe

theorem heldValid_next (state : State) (input : Input) :
    (step state input).next.heldValid = (input.resetN && (state.previousWrite && input.hostValid)) := by
  cases active : input.resetN <;>
    cases grant (beforeEdge state input) input <;>
    simp [step, beforeEdge, active]

theorem fresh_host_priority (state : State) (input : Input)
    (empty : state.heldValid = false) (ready : state.previousWrite = false)
    (host : input.hostValid = true) :
    (step state input).bankWrite = true ∧ (step state input).coreIssue = false ∧
      (step state input).bank = input.host := by
  simp [step, grant, beforeEdge, empty, ready, host]

theorem busy_host_delivered (state : State) (input following : Input)
    (safe : Safe state) (busy : state.previousWrite = true)
    (host : input.hostValid = true) (active : input.resetN = true) :
    (step state input).bankWrite = false ∧
      (step (step state input).next following).bankWrite = true ∧
      (step (step state input).next following).coreIssue = false ∧
      (step (step state input).next following).bank = input.host := by
  cases held : state.heldValid
  · simp [step, grant, beforeEdge, held, busy, host, active]
  · simp [Safe, held, busy] at safe

theorem core_granted (state : State) (input : Input)
    (empty : state.heldValid = false) (ready : state.previousWrite = false)
    (hostIdle : input.hostValid = false) (core : input.coreValid = true) :
    (step state input).bankWrite = true ∧ (step state input).coreIssue = true ∧
      (step state input).bank = input.core := by
  simp [step, grant, beforeEdge, empty, ready, hostIdle, core]

theorem stage_captures (state : State) (input : Input)
    (active : input.resetN = true) (write : (step state input).bankWrite = true) :
    (step state input).next.previousWrite = true ∧
      (step state input).next.staged = (step state input).bank := by
  unfold step at write ⊢
  cases selected : grant (beforeEdge state input) input <;> simp_all

def stateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => (step s i).next) inputs initial n

theorem safe_after_reset (inputs : Nat → Input) (initial : State)
    (reset : (inputs 0).resetN = false) (n : Nat) :
    Safe (stateAt inputs initial (n + 1)) :=
  invariant_after_first _ _ _ Safe (safe_reset initial (inputs 0) reset) safe_step n

/-- Consecutive active cycles cannot both issue a write after a sampled reset. -/
theorem trace_spacing (inputs : Nat → Input) (initial : State)
    (reset : (inputs 0).resetN = false) (n : Nat)
    (active : (inputs (n + 1)).resetN = true)
    (followingActive : (inputs (n + 2)).resetN = true)
    (write : (step (stateAt inputs initial (n + 1)) (inputs (n + 1))).bankWrite = true) :
    (step (stateAt inputs initial (n + 2)) (inputs (n + 2))).bankWrite = false := by
  apply no_back_to_back _ _ (safe_after_reset inputs initial reset (n + 1)) followingActive
  exact (stage_captures _ _ active write).1

def SpacedHost (inputs : Nat → Input) : Prop :=
  ∀ n, (inputs n).hostValid = true → (inputs (n + 1)).hostValid = false

def HostIssued (result : Result) (write : Write) : Prop :=
  result.bankWrite = true ∧ result.coreIssue = false ∧ result.bank = write

/-- In an active cycle after reset, each legal host byte issues now if the port is free,
or on the following active cycle if the port is busy. The core input is unrestricted. -/
theorem trace_host_service (inputs : Nat → Input) (initial : State)
    (reset : (inputs 0).resetN = false) (spaced : SpacedHost inputs) (n : Nat)
    (active : (inputs (n + 1)).resetN = true) (host : (inputs (n + 1)).hostValid = true) :
    let state := stateAt inputs initial (n + 1)
    let input := inputs (n + 1)
    if state.previousWrite then
      (step state input).bankWrite = false ∧
        ((inputs (n + 2)).resetN = true →
          HostIssued (step (stateAt inputs initial (n + 2)) (inputs (n + 2))) input.host)
    else HostIssued (step state input) input.host := by
  have empty : (stateAt inputs initial (n + 1)).heldValid = false := by
    change (step (stateAt inputs initial n) (inputs n)).next.heldValid = false
    rw [heldValid_next]
    cases earlier : (inputs n).hostValid
    · simp
    · simp [spaced n earlier] at host
  dsimp only
  cases busy : (stateAt inputs initial (n + 1)).previousWrite
  · simpa only [busy, Bool.false_eq_true, ↓reduceIte, HostIssued] using
      fresh_host_priority _ _ empty busy host
  · have delayed := busy_host_delivered _ _ (inputs (n + 2))
        (safe_after_reset inputs initial reset n) busy host active
    simp only [↓reduceIte]
    exact ⟨delayed.1, fun _ => delayed.2⟩

/-- A second adjacent strobe can be dropped while the first occupies the hold slot. -/
theorem adjacent_host_can_drop (first second : Write) :
    let initial : State := ⟨true, false, second, second⟩
    let blocked := step initial ⟨true, true, first, false, second⟩
    let issued := step blocked.next ⟨true, true, second, false, second⟩
    let following := step issued.next ⟨true, false, second, false, second⟩
    blocked.bankWrite = false ∧ HostIssued issued first ∧
      issued.next.heldValid = false ∧ following.bankWrite = false := by
  simp [step, grant, beforeEdge, HostIssued]

end Metronome.Config
