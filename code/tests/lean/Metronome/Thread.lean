import Metronome.Transition
import Std.Tactic.BVDecide

/-!
# Metronome v4 threads (t = 0..5), stated independently

An independent specification of the six thread state machines of
`src/md2_thread.v`, written from SPEC_V2 §4 (threads), §5 (dispatch and pause),
§9 (host writes of thread `PC` and `STAT`) and §12.3 (the freeze gate).  The
module `thread_check.py` elaborates the chip top, extracts the next state of all
seven registers of each `md2_thread` instance and of the six instances' input
cones, and proves the extracted equations equal the ones below
(`Metronome.Thread.rtlStep_eq_step` and the `Metronome.Thread.Top` theorems).

## What SPEC_V2 says (the equations below)

§4: *State: `PC` (8), `EN`, `READY`, `RUNNING`, `ARMED`, sticky `LATE`, `OVR`.*
The **trigger event** in cycle t is `trig = EN && (event(TRIG) || DB[t])`, with
`DB[t]` the doorbell pulse of §9.  *On `trig`: if `READY || RUNNING` then
`OVR' = 1` and the trigger is dropped; otherwise `READY' = 1, ARMED' = 1`.*
**Disarm**: *if its line has `BEAT` in cycle t then `ARMED' = 0`, unless an
accepted trigger in the same cycle sets it to 1.*  **Late write**: every enabled
`L.SYM`/`L.DBIT`/`L.XOR` move by a thread whose `ARMED` is 0 sets `LATE' = 1`
(the `lateSet` input below; §4 also makes it conditional on the thread, which is
the chip-top cut's `own` term).  **Stop**: *an enabled move to `T.STOP`:
`EN' = 0`; a host write of `EN` in the same cycle wins.*  §4 closes with:
*dispatch and pause set `READY' = 0, RUNNING' = 1` and `RUNNING' = 0, PC' = npc`.
A host write of `PC` in the same cycle as a pause wins.*

§9 fixes the `STAT` byte: it *reads `{OVR, LATE, EN, ARMED, RUNNING, READY}` in
bits 5..0; a write sets `EN` from bit 3 and clears `LATE` or `OVR` where bit 4
or 5 is 1.*  §9 also says a sticky flag set in the same cycle as a host clear
stays set, so the two sticky equations set before they clear (`lateSet` and the
overrun event are OR-ed in, outside the clear term).

§12.3: a frozen cycle has *no moves*, so no `T.STOP` and no `LATE` update, and
*no trigger is accepted (no `READY`, `ARMED` or `OVR` change)*, while *every
host write with its §9 effect* still runs, including thread `PC` and `STAT`.
The freeze gate itself is on the chip-top input side: `thread_check.py` proves
that the `ev` and `db` inputs of every instance are `& ~frz` (SPEC 12.3) and
that the other inputs carry the SPEC quantities.  `resetN` below is the sampled
`rst_q`; a low sample leaves `resetState` (§4 names no reset values, the RTL
clears every register, and the equation is checked against the RTL).

## Two resolutions SPEC_V2 leaves implicit

The RTL gives `disp` priority over an accepted trigger for `READY`, and `pause`
priority over `disp` for `RUNNING` and `PC` (with the host `PC` write above both,
as §4 says).  §5 makes the two dispatch/pause cases address different threads —
`pause` is the executing thread `XT`, `disp` picks a `READY` thread, and a
thread cannot legally be both — so the ordering is only visible when the
free-input cut binds both, which is exactly what this model must pin down.  Both
orders are stated as the resolution below and are what the generated
`rtlStep_eq_step` proves the RTL implements.  SPEC_V2 does not order them
itself; this is recorded in `THREAD_NOTES.md`.

## Cycle boundary

`stateAt inputs initial n` is the register state during chip cycle `n`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Metronome.Thread

/-- Thread state: SPEC_V2 §4, `PC` and the six flags. -/
structure State where
  /-- Program counter `PC`. -/
  pc : BitVec 8
  /-- Enabled `EN`. -/
  en : Bool
  /-- Triggered and waiting for a core `READY`. -/
  ready : Bool
  /-- Dispatched and executing `RUNNING`. -/
  running : Bool
  /-- Armed for the line's next `BEAT` `ARMED`. -/
  armed : Bool
  /-- Sticky late-write flag `LATE`. -/
  late : Bool
  /-- Sticky overrun flag `OVR`. -/
  ovr : Bool
  deriving DecidableEq, Repr

/-- The sampled inputs of one thread.  `ev` is the decoded `event(TRIG)` of
§4/§3.2/§3.4/§9, `db` the §9 doorbell pulse, `npc` the pausing instruction's
next `PC` (§5), `stop` a winning `T.STOP` move, `lateSet` an enabled symbol move
while `ARMED = 0`, `lineBeat` the thread's line `BEAT`, and `hPcWe`/`hStatWe`/
`hD` the §9 host write of `PC` / `STAT`. -/
structure Input where
  resetN : Bool
  ev : Bool
  db : Bool
  disp : Bool
  pause : Bool
  npc : BitVec 8
  stop : Bool
  lateSet : Bool
  lineBeat : Bool
  hPcWe : Bool
  hStatWe : Bool
  hD : BitVec 8
  deriving DecidableEq, Repr

/-- The state after a sampled reset edge.  §4 gives no reset values; the RTL
clears all seven registers and the generated equivalence checks that. -/
def resetState : State := ⟨0, false, false, false, false, false, false⟩

/-- Bit `i` of a vector, in the shape the RTL adapter emits and `bv_decide`
bit-blasts.  Bit indices in this module are constants (the `STAT` byte's
fields), so no `Nat` conversion is involved. -/
def bitAt {n : Nat} (x : BitVec n) (i : Nat) : Bool :=
  ((BitVec.truncate 1 (BitVec.ushiftRight x i)) != 0)

/-! ## Combinational terms of SPEC_V2 §4 -/

/-- The trigger event `EN && (event(TRIG) || DB[t])`. -/
def trig (s : State) (i : Input) : Bool := s.en && (i.ev || i.db)

/-- `READY || RUNNING`: the thread already holds a claim. -/
def busy (s : State) : Bool := s.ready || s.running

/-- An accepted trigger: `trig` with no claim held; §4 sets `READY'`/`ARMED'`. -/
def accept (s : State) (i : Input) : Bool := trig s i && !busy s

/-- A trigger that arrives while the thread holds a claim: §4 sets `OVR'` and
drops the trigger. -/
def overrunEvent (s : State) (i : Input) : Bool := trig s i && busy s

/-- The `STAT` write's `EN` bit (bit 3 of §9). -/
def statEn (i : Input) : Bool := bitAt i.hD 3

/-- The `STAT` write's `LATE` clear bit (bit 4 of §9). -/
def statClearLate (i : Input) : Bool := i.hStatWe && bitAt i.hD 4

/-- The `STAT` write's `OVR` clear bit (bit 5 of §9). -/
def statClearOvr (i : Input) : Bool := i.hStatWe && bitAt i.hD 5

/-! ## Next state

Each equation is the SPEC text read literally, with the two documented
resolutions (see the module comment). -/

/-- `PC'`: a host write of `PC` wins over a pause (§4); otherwise a pause
retires with `PC' = npc` (§5). -/
def pcNext (s : State) (i : Input) : BitVec 8 :=
  if i.hPcWe then i.hD else if i.pause then i.npc else s.pc

/-- `EN'`: a host `STAT` write sets it from bit 3 and wins over `T.STOP` (§4). -/
def enNext (s : State) (i : Input) : Bool :=
  if i.hStatWe then statEn i else if i.stop then false else s.en

/-- `READY'`: dispatch clears it (§5), an accepted trigger sets it (§4);
dispatch wins. -/
def readyNext (s : State) (i : Input) : Bool :=
  if i.disp then false else if accept s i then true else s.ready

/-- `RUNNING'`: pause clears it and dispatch sets it (§4/§5); pause wins. -/
def runningNext (s : State) (i : Input) : Bool :=
  if i.pause then false else if i.disp then true else s.running

/-- `ARMED'`: an accepted trigger sets it; a `BEAT` on the line clears it
unless an accepted trigger is in the same cycle (§4). -/
def armedNext (s : State) (i : Input) : Bool :=
  if accept s i then true else if i.lineBeat then false else s.armed

/-- `LATE'`: sticky; a late symbol move sets it, a `STAT` write with bit 4
clears it, and a same-cycle set wins (§4/§9). -/
def lateNext (s : State) (i : Input) : Bool :=
  i.lateSet || (s.late && !statClearLate i)

/-- `OVR'`: sticky; a trigger while busy sets it, a `STAT` write with bit 5
clears it, and a same-cycle set wins (§4/§9). -/
def ovrNext (s : State) (i : Input) : Bool :=
  overrunEvent s i || (s.ovr && !statClearOvr i)

/-- The thread transition; `resetN` low leaves `resetState`. -/
def step (s : State) (i : Input) : State :=
  if !i.resetN then resetState
  else ⟨pcNext s i, enNext s i, readyNext s i, runningNext s i, armedNext s i,
        lateNext s i, ovrNext s i⟩

/-! ## One-step consequences -/

/-- A reset sample leaves the reset state. -/
theorem reset_step (s : State) (i : Input) (h : i.resetN = false) :
    step s i = resetState := by
  simp [step, h]

/-- An active cycle's transition, with the reset branch discharged. -/
theorem step_active (s : State) (i : Input) (h : i.resetN = true) :
    step s i = ⟨pcNext s i, enNext s i, readyNext s i, runningNext s i,
      armedNext s i, lateNext s i, ovrNext s i⟩ := by
  simp [step, h]

/-- A thread holding a claim never accepts a trigger: §4's `READY || RUNNING`
guard. -/
theorem no_accept_while_busy (s : State) (i : Input) (h : busy s = true) :
    accept s i = false := by
  simp only [accept, trig, busy] at h ⊢
  bv_decide

/-- A trigger while busy sets the sticky overrun flag. -/
theorem ovr_set (s : State) (i : Input) (hr : i.resetN = true)
    (h : overrunEvent s i = true) : (step s i).ovr = true := by
  rw [step_active _ _ hr]
  simp only [ovrNext] at h ⊢
  simp [h]

/-- A trigger while busy sets `OVR` even when the same cycle's host `STAT`
write clears it (§9: a sticky flag set in the same cycle as a host clear stays
set). -/
theorem ovr_set_beats_clear (s : State) (i : Input) (hr : i.resetN = true)
    (h : overrunEvent s i = true) (_hc : statClearOvr i = true) :
    (step s i).ovr = true := by
  rw [step_active _ _ hr]
  simp only [ovrNext] at h ⊢
  simp [h]

/-- A quiet cycle with no prior overrun leaves `OVR` clear: the flag only
records a trigger while busy. -/
theorem ovr_quiet (s : State) (i : Input) (hr : i.resetN = true)
    (h : overrunEvent s i = false) (hq : s.ovr = false) :
    (step s i).ovr = false := by
  rw [step_active _ _ hr]
  simp only [ovrNext] at h hq ⊢
  simp [h, hq]

/-- A `STAT` write with bit 5 clears a quiet `OVR` (§9). -/
theorem ovr_clear (s : State) (i : Input) (hr : i.resetN = true)
    (h : overrunEvent s i = false) (hc : statClearOvr i = true) :
    (step s i).ovr = false := by
  rw [step_active _ _ hr]
  simp only [ovrNext] at h hc ⊢
  simp [h, hc]

/-- A sticky `OVR` holds unless a `STAT` write with bit 5 clears it. -/
theorem ovr_sticky (s : State) (i : Input) (hr : i.resetN = true)
    (h : s.ovr = true) (hc : statClearOvr i = false) :
    (step s i).ovr = true := by
  rw [step_active _ _ hr]
  simp only [ovrNext] at h hc ⊢
  simp [h, hc]

/-- A trigger while busy is dropped: `READY` is unchanged when no dispatch
happens in the same cycle (§4). -/
theorem drop_trigger_ready (s : State) (i : Input) (hr : i.resetN = true)
    (h : trig s i = true) (hb : busy s = true) (hd : i.disp = false) :
    (step s i).ready = s.ready := by
  rw [step_active _ _ hr]
  simp only [readyNext, accept, busy, trig] at h hb hd ⊢
  bv_decide

/-- A trigger while busy is dropped: it cannot arm the thread in that cycle
(only a same-cycle `BEAT` may disarm it). -/
theorem drop_trigger_armed (s : State) (i : Input) (hr : i.resetN = true)
    (h : trig s i = true) (hb : busy s = true) (hbeat : i.lineBeat = false) :
    (step s i).armed = s.armed := by
  rw [step_active _ _ hr]
  simp only [armedNext, accept, busy, trig] at h hb hbeat ⊢
  bv_decide

/-- An accepted trigger sets `READY` and `ARMED` in the same cycle (§4), unless
the core dispatches the thread in that cycle (§5). -/
theorem accept_sets_ready (s : State) (i : Input) (hr : i.resetN = true)
    (h : accept s i = true) (hd : i.disp = false) :
    (step s i).ready = true := by
  rw [step_active _ _ hr]
  simp only [readyNext] at h hd ⊢
  simp [h, hd]

theorem accept_sets_armed (s : State) (i : Input) (hr : i.resetN = true)
    (h : accept s i = true) : (step s i).armed = true := by
  rw [step_active _ _ hr]
  simp only [armedNext] at h ⊢
  simp [h]

/-- A dispatch clears `READY` and sets `RUNNING` in the same cycle (§5). -/
theorem dispatch_clears_ready (s : State) (i : Input) (hr : i.resetN = true)
    (h : i.disp = true) : (step s i).ready = false := by
  rw [step_active _ _ hr]
  simp only [readyNext] at h ⊢
  simp [h]

theorem dispatch_sets_running (s : State) (i : Input) (hr : i.resetN = true)
    (h : i.disp = true) (hp : i.pause = false) :
    (step s i).running = true := by
  rw [step_active _ _ hr]
  simp only [runningNext] at h hp ⊢
  simp [h, hp]

/-- A pause clears `RUNNING`; it beats a same-cycle dispatch on the same
thread (the RTL resolution; §5 has the two cases target different threads). -/
theorem pause_clears_running (s : State) (i : Input) (hr : i.resetN = true)
    (h : i.pause = true) : (step s i).running = false := by
  rw [step_active _ _ hr]
  simp only [runningNext] at h ⊢
  simp [h]

/-- A pause retires to `npc` (§5). -/
theorem pause_sets_pc (s : State) (i : Input) (hr : i.resetN = true)
    (h : i.pause = true) (hh : i.hPcWe = false) :
    (step s i).pc = i.npc := by
  rw [step_active _ _ hr]
  simp only [pcNext] at h hh ⊢
  simp [h, hh]

/-- A host write of `PC` wins over a same-cycle pause (§4). -/
theorem host_pc_beats_pause (s : State) (i : Input) (hr : i.resetN = true)
    (h : i.hPcWe = true) : (step s i).pc = i.hD := by
  rw [step_active _ _ hr]
  simp only [pcNext] at h ⊢
  simp [h]

/-- A host `STAT` write sets `EN` from bit 3 and wins over `T.STOP` (§4). -/
theorem host_en_beats_stop (s : State) (i : Input) (hr : i.resetN = true)
    (h : i.hStatWe = true) : (step s i).en = statEn i := by
  rw [step_active _ _ hr]
  simp only [enNext] at h ⊢
  simp [h]

/-- A `T.STOP` move clears `EN` when no host `STAT` write is in the cycle. -/
theorem stop_clears_en (s : State) (i : Input) (hr : i.resetN = true)
    (h : i.stop = true) (hs : i.hStatWe = false) :
    (step s i).en = false := by
  rw [step_active _ _ hr]
  simp only [enNext] at h hs ⊢
  simp [h, hs]

/-- A late symbol write sets the sticky `LATE`, even if the same cycle's
`STAT` write clears it (§9). -/
theorem late_set (s : State) (i : Input) (hr : i.resetN = true)
    (h : i.lateSet = true) : (step s i).late = true := by
  rw [step_active _ _ hr]
  simp only [lateNext] at h ⊢
  simp [h]

/-- A `STAT` write with bit 4 clears a quiet `LATE` (§9). -/
theorem late_clear (s : State) (i : Input) (hr : i.resetN = true)
    (h : i.lateSet = false) (hc : statClearLate i = true) :
    (step s i).late = false := by
  rw [step_active _ _ hr]
  simp only [lateNext] at h hc ⊢
  simp [h, hc]

/-- A sticky `LATE` holds when nothing clears it. -/
theorem late_sticky (s : State) (i : Input) (hr : i.resetN = true)
    (h : s.late = true) (hc : statClearLate i = false) :
    (step s i).late = true := by
  rw [step_active _ _ hr]
  simp only [lateNext] at h hc ⊢
  simp [h, hc]

/-- `ARMED` only changes on an accepted trigger (set) or a line `BEAT`
(clear); otherwise it holds (§4). -/
theorem armed_hold (s : State) (i : Input) (hr : i.resetN = true)
    (h : i.lineBeat = false) (ha : accept s i = false) :
    (step s i).armed = s.armed := by
  rw [step_active _ _ hr]
  simp only [armedNext] at h ha ⊢
  simp [h, ha]

/-- A `BEAT` disarms unless an accepted trigger sets `ARMED` in the same cycle
(§4). -/
theorem armed_beat (s : State) (i : Input) (hr : i.resetN = true)
    (h : i.lineBeat = true) (ha : accept s i = false) :
    (step s i).armed = false := by
  rw [step_active _ _ hr]
  simp only [armedNext] at h ha ⊢
  simp [h, ha]

/-- Structure extensionality for the seven thread fields: the exported
`rtlStep_eq_step` assembles the extracted transition from field equalities. -/
@[ext] theorem State.ext {s t : State} (hpc : s.pc = t.pc) (hen : s.en = t.en)
    (hready : s.ready = t.ready) (hrunning : s.running = t.running)
    (harmed : s.armed = t.armed) (hlate : s.late = t.late) (hovr : s.ovr = t.ovr) :
    s = t := by
  cases s
  cases t
  simp_all

/-- `READY` and `RUNNING` are exclusive on every reachable state: a dispatch
clears `READY`, and an accepted trigger needs both clear. -/
def Exclusive (s : State) : Prop := ¬(s.ready = true ∧ s.running = true)

theorem exclusive_reset : Exclusive resetState := by
  simp only [Exclusive, resetState]
  decide

theorem exclusive_step (s : State) (i : Input) (h : Exclusive s) :
    Exclusive (step s i) := by
  cases hr : i.resetN
  · rw [reset_step _ _ hr]
    exact exclusive_reset
  · rw [step_active s i hr]
    simp only [Exclusive, readyNext, runningNext, accept, busy] at h ⊢
    bv_decide

/-! ## Traces -/

def stateAt (inputs : Nat → Input) (initial : State) (n : Nat) : State :=
  run (fun s i => step s i) inputs initial n

theorem stateAt_succ (inputs : Nat → Input) (initial : State) (n : Nat) :
    stateAt inputs initial (n + 1) = step (stateAt inputs initial n) (inputs n) := rfl

/-- Every finite prefix of a thread trace keeps `READY` and `RUNNING`
exclusive. -/
theorem trace_exclusive (inputs : Nat → Input) (n : Nat) :
    Exclusive (stateAt inputs resetState n) := by
  induction n with
  | zero => exact exclusive_reset
  | succ n ih => rw [stateAt_succ]; exact exclusive_step _ _ ih

/-- A trigger while busy in cycle `n` sets the sticky `OVR` in cycle `n+1`. -/
theorem trace_ovr_of_busy_trigger (inputs : Nat → Input) (n : Nat)
    (hr : (inputs n).resetN = true)
    (h : overrunEvent (stateAt inputs resetState n) (inputs n) = true) :
    (stateAt inputs resetState (n + 1)).ovr = true := by
  rw [stateAt_succ]
  exact ovr_set _ _ hr h

/-- A dispatch in cycle `n` leaves the thread running in cycle `n+1` unless it
also pauses (the pause resolution). -/
theorem trace_dispatch_running (inputs : Nat → Input) (n : Nat)
    (hr : (inputs n).resetN = true)
    (h : (inputs n).disp = true) (hp : (inputs n).pause = false) :
    (stateAt inputs resetState (n + 1)).running = true := by
  rw [stateAt_succ]
  exact dispatch_sets_running _ _ hr h hp

end Metronome.Thread
