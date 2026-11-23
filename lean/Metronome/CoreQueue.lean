import Metronome.Transition
import Metronome.Config
import Std.Tactic.BVDecide

/-!
# Core pending-write queue (`CW.AL`, `CW.AH`, `CW.D`)

This module specifies the core-side configuration write path of SPEC_V2 §13.1 in
`src/project.v`: the address register `cw_addr`, the one-deep pending write
`cw_pending` / `cw_pending_addr` / `cw_pending_data`, and the sticky overflow
flag `cw_overrun`.

The queue is depth one, so no-loss and no-duplication reduce to a small set of
local facts:

* a queued write is held, byte for byte, until it drains (`hold_until_drain`);
* a drain delivers exactly the queued address and byte;
* the entry is empty afterwards unless the same cycle accepted a new `CW.D`
  (`drain_clears`, `accept_loads`);
* a `CW.D` that cannot be accepted because the queue is occupied and not
  draining is dropped and sets the sticky `CWOVR` flag
  (`accepted_or_overrun`, `no_silent_overwrite`).

`CWOVR` is sticky until the documented clear: a host write to `CTRL.STICKY`
with bit 2 set, which is the free per-cycle input `clearSticky` conjoined with
`hostData` bit 2 (the RTL term `c_wr_stk & h_wd[2]`).  A drop in the same cycle
as a clear still sets the flag, matching the RTL expression
`(writeData & ~accept) | (overrun & ~(c_wr_stk & h_wd[2]))`.

## Cycle boundary and free inputs

`stateAt inputs initial n` is the register state during chip cycle `n`, after
`n` sampled edges.  The reduced state is the five registers named above.
`rst_q` is `input.resetN`.  The remaining leaves are per-cycle inputs:

* `cw` is the picked 15-bit `CW` write group (`w_cw`), so the AL/AH/D decode and
  the accept/drain control are proved against the actual decoded nets;
* `frz` gates drain and is its own module in the freeze logic, so it is free
  here (treating it as free over-approximates the circuit, which is sound for
  the safety properties below);
* `coreIssue` is the arbiter's `cfg_core_issue` output, proved as a grant in
  `Metronome.Config` and composed in `queued_cfg_reaches_arbiter`;
* `isCfg` is `cw_is_cfg`, already proved equal to the bank mask rule by
  `Metronome.Decode.rtlCoreLive_eq_spec`;
* `clearSticky` and `hostData` carry the documented `CWOVR` clear leaf.

`frz` is not a state component, so a frozen cycle is a free input value; the
frozen state itself comes from the separate freeze cut.
-/

namespace Metronome.CoreQueue

/-- Register state at the core configuration write queue. -/
structure State where
  /-- `CWA`, the auto-incrementing write address. -/
  addr : BitVec 16
  /-- `CWV`, one queued write is present. -/
  pending : Bool
  /-- `CWQ.address`, the queued write address. -/
  pendingAddr : BitVec 16
  /-- `CWQ.byte`, the queued write byte. -/
  pendingData : BitVec 8
  /-- Sticky `CWOVR`. -/
  overrun : Bool
  deriving DecidableEq, Repr

/-- Sampled inputs. `cw` is the picked write group; the last two fields are the
documented `CTRL.STICKY` clear leaf. -/
structure Input where
  resetN : Bool
  cw : BitVec 15
  frz : Bool
  coreIssue : Bool
  isCfg : Bool
  clearSticky : Bool
  hostData : BitVec 8
  deriving DecidableEq, Repr

/-- One net bit as a `Bool`, the shape of a scalar RTL operand. -/
def bitAt {w : Nat} (x : BitVec w) (i : Nat) : Bool :=
  ((BitVec.truncate 1 (BitVec.ushiftRight x i)) != 0)

/-- `w_cw[13:8]`, the picked destination code. -/
def cwCode (c : BitVec 15) : BitVec 6 :=
  BitVec.truncate 6 (BitVec.ushiftRight c 8)

/-- `w_cw[7:0]`, the picked write byte. -/
def cwData (c : BitVec 15) : BitVec 8 :=
  BitVec.truncate 8 (BitVec.ushiftRight c 0)

def lowByte (a : BitVec 16) : BitVec 8 :=
  BitVec.truncate 8 (BitVec.ushiftRight a 0)

def highByte (a : BitVec 16) : BitVec 8 :=
  BitVec.truncate 8 (BitVec.ushiftRight a 8)

/-- `D_CW_D = 60`, `D_CW_AL = 58`, `D_CW_AH = 59`; `w_cw[14]` is the move hit. -/
def writeData (i : Input) : Bool := bitAt i.cw 14 && (cwCode i.cw == (60 : BitVec 6))

def writeLow (i : Input) : Bool := bitAt i.cw 14 && (cwCode i.cw == (58 : BitVec 6))

def writeHigh (i : Input) : Bool := bitAt i.cw 14 && (cwCode i.cw == (59 : BitVec 6))

/-- SPEC_V2 §13.1: the queued write drains when it is present, the machine is
not frozen, and it either targets an ordinary address or the arbiter accepted
the core write.  The parentheses follow the RTL's `(pending & ~frz) & (...)`
nesting so the extracted transition matches definitionally. -/
def drain (state : State) (input : Input) : Bool :=
  (state.pending && !input.frz) && (!input.isCfg || input.coreIssue)

/-- SPEC_V2 §13.1: a `CW.D` is accepted when the queue can take it, that is
when it is empty or drains in this cycle. -/
def accept (state : State) (input : Input) : Bool :=
  writeData input && (!state.pending || drain state input)

/-- The documented `CWOVR` clear leaf: `c_wr_stk & h_wd[2]`. -/
def hostClear (input : Input) : Bool :=
  input.clearSticky && bitAt input.hostData 2

/-- Eight low bits of a 16-bit value, assembled in the RTL bit order.  This is
the shape the RTLIL adapter emits for a byte-granular register update. -/
def take8 (x : BitVec 16) : BitVec 8 :=
  (if bitAt x 0 then BitVec.shiftLeft (1 : BitVec 8) 0 else (0 : BitVec 8)) |||
  (if bitAt x 1 then BitVec.shiftLeft (1 : BitVec 8) 1 else (0 : BitVec 8)) |||
  (if bitAt x 2 then BitVec.shiftLeft (1 : BitVec 8) 2 else (0 : BitVec 8)) |||
  (if bitAt x 3 then BitVec.shiftLeft (1 : BitVec 8) 3 else (0 : BitVec 8)) |||
  (if bitAt x 4 then BitVec.shiftLeft (1 : BitVec 8) 4 else (0 : BitVec 8)) |||
  (if bitAt x 5 then BitVec.shiftLeft (1 : BitVec 8) 5 else (0 : BitVec 8)) |||
  (if bitAt x 6 then BitVec.shiftLeft (1 : BitVec 8) 6 else (0 : BitVec 8)) |||
  (if bitAt x 7 then BitVec.shiftLeft (1 : BitVec 8) 7 else (0 : BitVec 8))

/-- Join the two byte halves, assembled in the RTL bit order. -/
def pack (lo hi : BitVec 8) : BitVec 16 :=
  (if bitAt lo 0 then BitVec.shiftLeft (1 : BitVec 16) 0 else (0 : BitVec 16)) |||
  (if bitAt lo 1 then BitVec.shiftLeft (1 : BitVec 16) 1 else (0 : BitVec 16)) |||
  (if bitAt lo 2 then BitVec.shiftLeft (1 : BitVec 16) 2 else (0 : BitVec 16)) |||
  (if bitAt lo 3 then BitVec.shiftLeft (1 : BitVec 16) 3 else (0 : BitVec 16)) |||
  (if bitAt lo 4 then BitVec.shiftLeft (1 : BitVec 16) 4 else (0 : BitVec 16)) |||
  (if bitAt lo 5 then BitVec.shiftLeft (1 : BitVec 16) 5 else (0 : BitVec 16)) |||
  (if bitAt lo 6 then BitVec.shiftLeft (1 : BitVec 16) 6 else (0 : BitVec 16)) |||
  (if bitAt lo 7 then BitVec.shiftLeft (1 : BitVec 16) 7 else (0 : BitVec 16)) |||
  (if bitAt hi 0 then BitVec.shiftLeft (1 : BitVec 16) 8 else (0 : BitVec 16)) |||
  (if bitAt hi 1 then BitVec.shiftLeft (1 : BitVec 16) 9 else (0 : BitVec 16)) |||
  (if bitAt hi 2 then BitVec.shiftLeft (1 : BitVec 16) 10 else (0 : BitVec 16)) |||
  (if bitAt hi 3 then BitVec.shiftLeft (1 : BitVec 16) 11 else (0 : BitVec 16)) |||
  (if bitAt hi 4 then BitVec.shiftLeft (1 : BitVec 16) 12 else (0 : BitVec 16)) |||
  (if bitAt hi 5 then BitVec.shiftLeft (1 : BitVec 16) 13 else (0 : BitVec 16)) |||
  (if bitAt hi 6 then BitVec.shiftLeft (1 : BitVec 16) 14 else (0 : BitVec 16)) |||
  (if bitAt hi 7 then BitVec.shiftLeft (1 : BitVec 16) 15 else (0 : BitVec 16))

/-- The low address byte after this edge. -/
def nextLow (state : State) (input : Input) : BitVec 8 :=
  let low :=
    if accept state input then take8 (state.addr + 1)
    else if writeLow input then cwData input.cw else lowByte state.addr
  if input.resetN then low else 0

/-- The high address byte after this edge.  `CW.AL` keeps it, `CW.AH` loads it,
and an accepted `CW.D` takes the auto-incremented value. -/
def nextHigh (state : State) (input : Input) : BitVec 8 :=
  let high :=
    if accept state input then highByte (state.addr + 1)
    else if writeLow input then highByte state.addr
    else if writeHigh input then cwData input.cw else highByte state.addr
  if input.resetN then high else 0

/-- SPEC_V2 §13.1: `CW.D` accepts `(CWA, bus)` and increments `CWA`; `CW.AL`
and `CW.AH` load the low and high byte of `CWA`. Reset clears every field. -/
def step (state : State) (input : Input) : State :=
  { addr := pack (nextLow state input) (nextHigh state input)
    pending :=
      if input.resetN then
        (if accept state input then true else if drain state input then false else state.pending)
      else false
    pendingAddr :=
      if input.resetN then (if accept state input then state.addr else state.pendingAddr)
      else 0
    pendingData :=
      if input.resetN then (if accept state input then cwData input.cw else state.pendingData)
      else 0
    overrun :=
      if input.resetN then
        ((writeData input && !accept state input) || (state.overrun && !hostClear input))
      else false }

/-- The write a queued entry presents to the arbiter: the low nine bits of the
queued address (the window offset checked by the decode cut) and the queued
byte.  The full 16-bit address stays in `pendingAddr`. -/
def queuedWrite (state : State) : Config.Write :=
  ⟨state.pendingAddr.truncate 9, state.pendingData⟩

/-- The arbiter request driven by this queue state.  `hostValid` and the host
payload are the arbiter's other inputs. -/
def arbInput (state : State) (input : Input) (hostValid : Bool) (host : Config.Write) :
    Config.Input :=
  { resetN := input.resetN
    hostValid := hostValid
    host := host
    coreValid := state.pending && !input.frz && input.isCfg
    core := queuedWrite state }

/-- The RTL's assembled low byte and plain high byte rebuild the whole value.
Proved by `bv_decide`, so it carries a native LRAT certificate like the decode
cut. -/
theorem pack_take (x : BitVec 16) : pack (take8 x) (highByte x) = x := by
  simp only [pack, take8, highByte, bitAt]
  bv_decide

theorem pack_low (lo hi : BitVec 8) : (pack lo hi).truncate 8 = lo := by
  simp only [pack, bitAt]
  bv_decide

theorem pack_high (lo hi : BitVec 8) :
    (BitVec.truncate 8 (BitVec.ushiftRight (pack lo hi) 8)) = hi := by
  simp only [pack, bitAt]
  bv_decide

/-- Two states with the same fields are equal.  The RTLIL adapter emits a
structure literal, so equality is checked field by field. -/
@[ext] theorem State.ext {a b : State} (addr : a.addr = b.addr)
    (pending : a.pending = b.pending) (pendingAddr : a.pendingAddr = b.pendingAddr)
    (pendingData : a.pendingData = b.pendingData) (overrun : a.overrun = b.overrun) :
    a = b := by
  obtain ⟨⟩ := a
  obtain ⟨⟩ := b
  simp_all

/-! ## Queue-level safety facts -/

theorem drain_eq_false_of_frozen (state : State) (input : Input)
    (frozen : input.frz = true) : drain state input = false := by
  simp [drain, frozen]

theorem drain_false_of_cfg_waiting (state : State) (input : Input)
    (cfg : input.isCfg = true) (noIssue : input.coreIssue = false) :
    drain state input = false := by
  simp [drain, cfg, noIssue]

/-- A queued write is held unchanged while it does not drain. -/
theorem hold_until_drain (state : State) (input : Input)
    (pending : state.pending = true) (blocked : drain state input = false)
    (reset : input.resetN = true) :
    (step state input).pending = true ∧
      (step state input).pendingAddr = state.pendingAddr ∧
      (step state input).pendingData = state.pendingData := by
  have noAccept : accept state input = false := by
    simp [accept, pending, blocked]
  simp [step, pending, blocked, noAccept, reset]

/-- An accepted write enters the queue with the address the counter held and
the write byte, and the counter advances to the next 16-bit value.  The
address is kept in the RTL's byte-assembled form here, so this fact does not
depend on the byte-packing certificate. -/
theorem accept_loads (state : State) (input : Input)
    (accepted : accept state input = true) (reset : input.resetN = true) :
    (step state input).pending = true ∧
      (step state input).pendingAddr = state.addr ∧
      (step state input).pendingData = cwData input.cw ∧
      (step state input).addr =
        pack (take8 (state.addr + 1)) (highByte (state.addr + 1)) := by
  exact ⟨by simp [step, accepted, reset],
    by simp [step, accepted, reset],
    by simp [step, accepted, reset],
    by simp [step, nextLow, nextHigh, accepted, reset]⟩

/-- The same acceptance as a plain increment of the address counter. -/
theorem accept_increments (state : State) (input : Input)
    (accepted : accept state input = true) (reset : input.resetN = true) :
    (step state input).addr = state.addr + 1 := by
  rw [(accept_loads state input accepted reset).2.2.2, pack_take]

/-- A drain without a simultaneous acceptance empties the queue and leaves the
payload untouched; that payload is exactly what the port delivers. -/
theorem drain_clears (state : State) (input : Input)
    (active : drain state input = true) (noAccept : accept state input = false)
    (reset : input.resetN = true) :
    (step state input).pending = false ∧
      (step state input).pendingAddr = state.pendingAddr ∧
      (step state input).pendingData = state.pendingData := by
  simp [step, active, noAccept, reset]

/-- A `CW.D` that arrives while the queue is occupied and not draining is
dropped: the queued payload is preserved and `CWOVR` becomes set. -/
theorem no_silent_overwrite (state : State) (input : Input)
    (pending : state.pending = true) (write : writeData input = true)
    (blocked : drain state input = false) (reset : input.resetN = true) :
    (step state input).pendingAddr = state.pendingAddr ∧
      (step state input).pendingData = state.pendingData ∧
      (step state input).overrun = true := by
  have noAccept : accept state input = false := by
    simp [accept, pending, blocked]
  refine ⟨by simp [step, noAccept, reset], by simp [step, noAccept, reset], ?_⟩
  simp [step, reset, write, noAccept]

/-- Every `CW.D` is either accepted into the queue or flagged by `CWOVR`; the
sticky flag is the only record of a dropped write. -/
theorem accepted_or_overrun (state : State) (input : Input)
    (reset : input.resetN = true) (write : writeData input = true)
    (dropped : accept state input = false) : (step state input).overrun = true := by
  simp [step, reset, write, dropped]

/-- `CWOVR` is sticky until its documented clear. -/
theorem overrun_sticky (state : State) (input : Input)
    (reset : input.resetN = true) (set : state.overrun = true)
    (noClear : hostClear input = false) : (step state input).overrun = true := by
  simp [step, reset, set, noClear]

/-- The documented clear is the only way to drop `CWOVR` without a new drop. -/
theorem overrun_cleared (state : State) (input : Input)
    (reset : input.resetN = true) (clear : hostClear input = true)
    (write : writeData input = true) (accepted : accept state input = true) :
    (step state input).overrun = false := by
  simp [step, reset, clear, write, accepted]

/-- A frozen queue keeps its entry: nothing drains, and a concurrent `CW.D`
cannot be accepted, so it is dropped and flagged instead. -/
theorem frz_holds (state : State) (input : Input)
    (frozen : input.frz = true) (pending : state.pending = true)
    (reset : input.resetN = true) :
    (step state input).pending = true ∧
      (step state input).pendingAddr = state.pendingAddr ∧
      (step state input).pendingData = state.pendingData ∧
      drain state input = false := by
  have noDrain : drain state input = false := drain_eq_false_of_frozen state input frozen
  obtain ⟨heldPending, heldAddr, heldData⟩ :=
    hold_until_drain state input pending noDrain reset
  exact ⟨heldPending, heldAddr, heldData, noDrain⟩

/-- `CW.AL` loads the low address byte while `CW.AH` loads the high byte; both
leave the other byte alone. -/
theorem low_load (state : State) (input : Input)
    (load : writeLow input = true) (noAccept : accept state input = false)
    (reset : input.resetN = true) :
    (step state input).addr = pack (cwData input.cw) (highByte state.addr) := by
  simp [step, nextLow, nextHigh, load, noAccept, reset]

theorem high_load (state : State) (input : Input)
    (load : writeHigh input = true) (noLow : writeLow input = false)
    (noAccept : accept state input = false) (reset : input.resetN = true) :
    (step state input).addr = pack (lowByte state.addr) (cwData input.cw) := by
  simp [step, nextLow, nextHigh, load, noLow, noAccept, reset]

/-- The readable byte view of a `CW.AL` load: only the low address byte
changes.  The byte-packing identities carry the native certificate. -/
theorem low_load_bytes (state : State) (input : Input)
    (load : writeLow input = true) (noAccept : accept state input = false)
    (reset : input.resetN = true) :
    (BitVec.truncate 8 (BitVec.ushiftRight (step state input).addr 0)) =
        cwData input.cw ∧
      (BitVec.truncate 8 (BitVec.ushiftRight (step state input).addr 8)) =
        highByte state.addr := by
  rw [low_load state input load noAccept reset]
  exact ⟨pack_low _ _, pack_high _ _⟩

/-- The readable byte view of a `CW.AH` load: only the high address byte
changes. -/
theorem high_load_bytes (state : State) (input : Input)
    (load : writeHigh input = true) (noLow : writeLow input = false)
    (noAccept : accept state input = false) (reset : input.resetN = true) :
    (BitVec.truncate 8 (BitVec.ushiftRight (step state input).addr 0)) =
        lowByte state.addr ∧
      (BitVec.truncate 8 (BitVec.ushiftRight (step state input).addr 8)) =
        cwData input.cw := by
  rw [high_load state input load noLow noAccept reset]
  exact ⟨pack_low _ _, pack_high _ _⟩

/-! ## Trace lifting -/

def stateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun state input => step state input) inputs initial n

theorem stateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    stateAt inputs initial (n + 1) = step (stateAt inputs initial n) (inputs n) := rfl

theorem trace_held_until_drain_aux (inputs : Nat → Input) (initial : State)
    (m : Nat) (pending : (stateAt inputs initial m).pending = true) :
    ∀ d, (∀ k, m ≤ k → k < m + d →
        drain (stateAt inputs initial k) (inputs k) = false) →
      (∀ k, m ≤ k → k < m + d → (inputs k).resetN = true) →
      (stateAt inputs initial (m + d)).pending = true ∧
        (stateAt inputs initial (m + d)).pendingAddr =
          (stateAt inputs initial m).pendingAddr ∧
        (stateAt inputs initial (m + d)).pendingData =
          (stateAt inputs initial m).pendingData := by
  intro d
  induction d with
  | zero =>
    intro _ _
    rw [Nat.add_zero]
    exact ⟨pending, rfl, rfl⟩
  | succ d ih =>
    intro noDrain noReset
    have noDrainD : ∀ k, m ≤ k → k < m + d →
        drain (stateAt inputs initial k) (inputs k) = false :=
      fun k le lt => noDrain k le (by omega)
    have noResetD : ∀ k, m ≤ k → k < m + d → (inputs k).resetN = true :=
      fun k le lt => noReset k le (by omega)
    have ihd := ih noDrainD noResetD
    have lt : m + d < m + (d + 1) := by omega
    have hstep := hold_until_drain (stateAt inputs initial (m + d)) (inputs (m + d))
      ihd.1 (noDrain (m + d) (Nat.le_add_right m d) lt)
      (noReset (m + d) (Nat.le_add_right m d) lt)
    rw [Nat.add_succ, stateAt_succ]
    exact ⟨hstep.1, hstep.2.1.trans ihd.2.1, hstep.2.2.trans ihd.2.2⟩

/-- A queued write is held, byte for byte, from cycle `m` until it drains: no
reset and no drain in between leaves the entry unchanged.  This is the
no-loss half of the queue contract, and it also excludes a second delivery of
the same entry, because only a drain removes it. -/
theorem trace_held_until_drain (inputs : Nat → Input) (initial : State) (m n : Nat)
    (order : m ≤ n) (pending : (stateAt inputs initial m).pending = true)
    (noDrain : ∀ k, m ≤ k → k < n → drain (stateAt inputs initial k) (inputs k) = false)
    (noReset : ∀ k, m ≤ k → k < n → (inputs k).resetN = true) :
    (stateAt inputs initial n).pending = true ∧
      (stateAt inputs initial n).pendingAddr = (stateAt inputs initial m).pendingAddr ∧
      (stateAt inputs initial n).pendingData = (stateAt inputs initial m).pendingData := by
  have bound : m + (n - m) = n := Nat.add_sub_of_le order
  have aux := trace_held_until_drain_aux inputs initial m pending (n - m)
    (fun k le lt => noDrain k le (by omega))
    (fun k le lt => noReset k le (by omega))
  simpa [bound] using aux

/-- The write a queued entry delivers, in arbiter coordinates. -/
def delivered (state : State) : Config.Write := queuedWrite state

/-- The arbiter-side write an acceptance loads: the counter's low nine bits and
the write byte.  The full 16-bit address is kept in `pendingAddr`. -/
def acceptedWrite (state : State) (input : Input) : Config.Write :=
  ⟨state.addr.truncate 9, cwData input.cw⟩

/-- A drained entry delivers exactly the address and byte it was accepted with.
The entry is loaded at `m` by an accepted `CW.D`, survives unchanged while no
drain occurs, and the drain at `n` presents that same entry. -/
theorem trace_drain_delivers_accepted (inputs : Nat → Input) (initial : State)
    (m n : Nat) (order : m + 1 ≤ n)
    (accepted : accept (stateAt inputs initial m) (inputs m) = true)
    (resetM : (inputs m).resetN = true)
    (noDrain : ∀ k, m + 1 ≤ k → k < n →
      drain (stateAt inputs initial k) (inputs k) = false)
    (noReset : ∀ k, m + 1 ≤ k → k < n → (inputs k).resetN = true)
    (drained : drain (stateAt inputs initial n) (inputs n) = true) :
    drain (stateAt inputs initial n) (inputs n) = true ∧
      delivered (stateAt inputs initial n) =
        acceptedWrite (stateAt inputs initial m) (inputs m) := by
  refine ⟨drained, ?_⟩
  have loaded := accept_loads (stateAt inputs initial m) (inputs m) accepted resetM
  have held := trace_held_until_drain inputs initial (m + 1) n order loaded.1
    noDrain noReset
  have hpa : (stateAt inputs initial n).pendingAddr = (stateAt inputs initial m).addr := by
    rw [held.2.1, stateAt_succ]
    exact loaded.2.1
  have hpd : (stateAt inputs initial n).pendingData = cwData (inputs m).cw := by
    rw [held.2.2, stateAt_succ]
    exact loaded.2.2.1
  simp only [delivered, queuedWrite, acceptedWrite, hpa, hpd]

/-- After a drain in cycle `n` without an acceptance, the queue is empty in
cycle `n+1`; `pending` can only become true again through a fresh acceptance.
Together with `trace_held_until_drain` this is the no-duplication half. -/
theorem trace_drain_empties (inputs : Nat → Input) (initial : State) (n : Nat)
    (drained : drain (stateAt inputs initial n) (inputs n) = true)
    (noAccept : accept (stateAt inputs initial n) (inputs n) = false)
    (reset : (inputs n).resetN = true) :
    (stateAt inputs initial (n + 1)).pending = false := by
  rw [stateAt_succ]
  exact (drain_clears _ _ drained noAccept reset).1

/-- `pending` after an edge is exactly "accepted now, or already pending and
not draining".  Reset clears it. -/
theorem pending_next (state : State) (input : Input) :
    (step state input).pending =
      (input.resetN &&
        (accept state input || (state.pending && !drain state input))) := by
  cases reset : input.resetN <;> simp only [step, reset]
  all_goals
    cases accepted : accept state input <;> cases active : drain state input <;>
      cases pending : state.pending <;> simp_all

/-! ## Composition with the configuration arbiter -/

/-- Under the arbiter's grant premises, a queued configuration write is
issued on the bank port with its original payload.  This is
`Metronome.Config.core_granted` instantiated at the queue's request. -/
theorem queued_cfg_reaches_arbiter (state : State) (input : Input)
    (arb : Config.State) (host : Config.Write)
    (empty : arb.heldValid = false) (ready : arb.previousWrite = false)
    (hostIdle : (arbInput state input false host).hostValid = false)
    (live : (arbInput state input false host).coreValid = true) :
    let result := Config.step arb (arbInput state input false host)
    result.bankWrite = true ∧ result.coreIssue = true ∧
      result.bank = queuedWrite state :=
  Config.core_granted arb (arbInput state input false host) empty ready hostIdle live

/-- A configuration write that the arbiter grants drains the queue in the same
cycle.  The queue input `coreIssue` is the arbiter output checked by the
adapter, and `isCfg` is the decode leaf; the adapter also checks that the
arbiter's `core_valid` is exactly `cw_pending & ~frz & cw_is_cfg`. -/
theorem queued_cfg_drains (state : State) (input : Input)
    (pending : state.pending = true) (unfrozen : input.frz = false)
    (cfg : input.isCfg = true) (issue : input.coreIssue = true) :
    drain state input = true := by
  simp [drain, pending, unfrozen, cfg, issue]

/-! ## Concrete witnesses -/

/-- A second `CW.D` while a configuration write waits for the arbiter is
dropped and sets `CWOVR`; the first write keeps its address and byte.  The
same write into an empty queue is accepted (last conjunct), so the "queue
occupied and not draining" premise is needed. -/
theorem overrun_witness :
    let state : State := ⟨0x2345, true, 0x2000, 0x5A, false⟩
    let input : Input := ⟨true, 0x7C5A, false, false, true, false, 0⟩
    writeData input = true ∧ accept state input = false ∧
      (step state input).overrun = true ∧
      (step state input).pendingAddr = 0x2000 ∧
      (step state input).pendingData = 0x5A ∧
      accept (⟨0x2345, false, 0, 0, false⟩ : State) input = true := by
  decide

end Metronome.CoreQueue
