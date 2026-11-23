import Metronome.Machine
import Metronome.Thread

/-!
# Bridge: the thread cut (`Metronome.Thread`) refines `Machine.Thread`

`Metronome.Thread` states the SPEC_V2 §4/§5/§9/§12.3 equations of the six
thread state machines as an independent cut, and `thread_check.py` proves that
the elaborated `md2_thread` registers implement them.  `Metronome.Machine`
states the same section as a whole-chip executable machine.  This file proves
that the cut's one-cycle transition *is* the machine's `Machine.threadNext`
under an explicit abstraction map, so the RTL steps compose with the machine
step for this component.

## Abstraction map

`absState` copies the seven state fields one for one.  `absInput` builds the
machine's per-thread input record:

* `trig` is the cut's own `trig = EN && (event(TRIG) || DB[t])`, with the
  machine's `ThreadIn.trig`; `absIn.trig` uses the cut state's `EN` exactly
  as the chip top does (`Chip.runStep` passes `!frozen && ts.en && (...)`).
* `beat`, `late` and `stop` are the cut's `lineBeat`, `lateSet` and `stop`.
* `dispatch` is the cut's `disp`; `pause` is `some npc` exactly when the cut's
  `pause` is high; `hPC`/`hStat` are `some hD` exactly when the corresponding
  host write strobe is high (and `none` otherwise, so the machine falls through
  to the next priority exactly as the cut's nested `if` does).
* the value-carrying options use `BitVec.toNat`; the machine reduces every
  `Nat` back to 8 bits with `Util.bv`, which is the identity on the cut's
  8-bit fields (`bv_toNat`).

## Side conditions (exactly the two orderings SPEC_V2 leaves implicit)

`Metronome.Thread` gives `disp` priority over an accepted trigger for `READY`
and `pause` priority over `disp` for `RUNNING`; `Machine.threadNext` gives the
accepted trigger and the dispatch priority.  The two are the same whenever a
thread is not both dispatched and triggered/paused in one cycle:

* `hacc_disp : ¬(accept s i = true ∧ i.disp = true)`
* `hpause_disp : ¬(i.pause = true ∧ i.disp = true)`

Both are properties of a *legal* chip cycle, not of the cut: `Machine`'s
`pickThread` only dispatches a `ready` thread (`ready` implies `busy`, so no
trigger is accepted), and a pause targets the executing thread `XT` while a
dispatch picks a `ready` (not `running`) thread.  They are therefore recorded
as side conditions of the bridge, not as disagreements: the two models agree
on every reachable cycle.

## Trigger event

`trig_refines` relates the cut's abstract `ev`/`db` inputs to the machine's
`trigEvent` decoder and doorbell register under the chip-top cut's freeze gate
(`ev = trigEvent && !FRZ`, `db = DB[t] && !FRZ`, SPEC_V2 §12.3).

No `sorry`, no `native_decide`; every proof is core Lean (`trunc_ne` uses
`bv_decide` on a concrete 8-bit field, the rest is rewriting and case analysis).
-/

set_option autoImplicit false

namespace Metronome.Bridge.Thread

/-! ## Bit-field plumbing: the cut's RTL-shaped `bitAt` is the machine's `nbit` -/

/-- The machine reads a field bit as `(x.toNat >>> i) % 2 == 1`. -/
theorem nbit_eq_testBit (x i : Nat) : Machine.Util.nbit x i = Nat.testBit x i := by
  rw [Machine.Util.nbit, Nat.testBit, Nat.and_comm, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (x >>> i) with h | h <;> simp [h]

/-- A one-bit truncation is nonzero exactly when bit 0 is set. -/
theorem trunc_ne (y : BitVec 8) :
    (BitVec.truncate 1 y != 0) = y.getLsbD 0 := by
  bv_decide

/-- The cut reads a field bit with `truncate 1 (ushiftRight x i) != 0`; that is
bit `i`. -/
theorem bitAt_eq_getLsbD (x : BitVec 8) (i : Nat) :
    Metronome.Thread.bitAt x i = x.getLsbD i := by
  simp only [Metronome.Thread.bitAt]
  rw [trunc_ne]
  show (x >>> i).getLsbD 0 = x.getLsbD i
  rw [BitVec.getLsbD_ushiftRight]
  simp

/-- The cut's `bitAt` is the machine's `nbit`. -/
theorem bitAt_eq_nbit (x : BitVec 8) (i : Nat) :
    Metronome.Thread.bitAt x i = Machine.Util.nbit x.toNat i := by
  rw [bitAt_eq_getLsbD, nbit_eq_testBit]
  rfl

/-- The machine's `bv n x.toNat` is the cut's `x` on every field the cut owns. -/
theorem bv_toNat {n : Nat} (x : BitVec n) : Machine.Util.bv n x.toNat = x := by
  simp [Machine.Util.bv]

/-- Structure extensionality for the machine's thread state (the structure has
no generated `ext` theorem: it carries `Repr`/`Inhabited` only). -/
theorem threadSt_ext {a b : Machine.ThreadSt} (hpc : a.pc = b.pc) (hen : a.en = b.en)
    (hready : a.ready = b.ready) (hrunning : a.running = b.running)
    (harmed : a.armed = b.armed) (hlate : a.late = b.late) (hovr : a.ovr = b.ovr) :
    a = b := by
  cases a
  cases b
  simp_all

/-! ## Abstraction map -/

/-- The cut's thread state is the machine's thread state, field for field. -/
def absState (s : Metronome.Thread.State) : Machine.ThreadSt :=
  { pc := s.pc, en := s.en, ready := s.ready, running := s.running, armed := s.armed,
    late := s.late, ovr := s.ovr }

/-- The cut's sampled inputs as the machine's `ThreadIn` record.  `trig` is the
cut's §4 trigger term (the machine's chip top forms the same conjunction); the
options encode the cut's priority chain, and every value is carried as a `Nat`
the machine reduces with `bv 8`. -/
def absInput (s : Metronome.Thread.State) (i : Metronome.Thread.Input) : Machine.ThreadIn :=
  { trig := Metronome.Thread.trig s i
    beat := i.lineBeat
    late := i.lateSet
    stop := i.stop
    dispatch := i.disp
    pause := if i.pause then some i.npc.toNat else none
    hPC := if i.hPcWe then some i.hD.toNat else none
    hStat := if i.hStatWe then some i.hD.toNat else none }

/-! ## Field bridges

Each field of `Machine.threadNext` is a one-line corollary of the cut's
equation; the two orderings appear only in `ready` and `running`. -/

theorem pc_bridge (s : Metronome.Thread.State) (i : Metronome.Thread.Input)
    (hreset : i.resetN = true) :
    (absState (Metronome.Thread.step s i)).pc =
      (Machine.threadNext (absState s) (absInput s i)).pc := by
  rw [Metronome.Thread.step_active s i hreset]
  simp only [absState, absInput, Machine.threadNext, Metronome.Thread.pcNext]
  by_cases hpc : i.hPcWe = true
  · simp [hpc, bv_toNat]
  · by_cases hp : i.pause = true
    · simp [hpc, hp, bv_toNat]
    · simp [hpc, hp]

theorem en_bridge (s : Metronome.Thread.State) (i : Metronome.Thread.Input)
    (hreset : i.resetN = true) :
    (absState (Metronome.Thread.step s i)).en =
      (Machine.threadNext (absState s) (absInput s i)).en := by
  rw [Metronome.Thread.step_active s i hreset]
  simp only [absState, absInput, Machine.threadNext, Metronome.Thread.enNext,
    Metronome.Thread.statEn]
  by_cases hs : i.hStatWe = true
  · simp [hs, bitAt_eq_nbit]
  · by_cases hstop : i.stop = true
    · simp [hs, hstop]
    · simp [hs, hstop]

theorem bool_eq_false_of_ne_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b <;> simp_all

theorem ready_bridge (s : Metronome.Thread.State) (i : Metronome.Thread.Input)
    (hreset : i.resetN = true)
    (hacc_disp : ¬(Metronome.Thread.accept s i = true ∧ i.disp = true)) :
    (absState (Metronome.Thread.step s i)).ready =
      (Machine.threadNext (absState s) (absInput s i)).ready := by
  rw [Metronome.Thread.step_active s i hreset]
  simp only [absState, absInput, Machine.threadNext, Metronome.Thread.readyNext]
  have hacc : (Metronome.Thread.trig s i && !(s.ready || s.running)) =
      Metronome.Thread.accept s i := rfl
  by_cases hd : i.disp = true
  · have ha : Metronome.Thread.accept s i = false :=
      bool_eq_false_of_ne_true (by intro h; exact hacc_disp ⟨h, hd⟩)
    simp only [hacc, hd, ha, ite_true, ite_false, Bool.false_eq_true]
  · simp only [hacc, hd, ite_false, Bool.false_eq_true]

theorem running_bridge (s : Metronome.Thread.State) (i : Metronome.Thread.Input)
    (hreset : i.resetN = true)
    (hpause_disp : ¬(i.pause = true ∧ i.disp = true)) :
    (absState (Metronome.Thread.step s i)).running =
      (Machine.threadNext (absState s) (absInput s i)).running := by
  rw [Metronome.Thread.step_active s i hreset]
  simp only [absState, absInput, Machine.threadNext, Metronome.Thread.runningNext]
  by_cases hd : i.disp = true
  · have hp : ¬(i.pause = true) := by
      intro htrue
      exact hpause_disp ⟨htrue, hd⟩
    simp [hd, hp]
  · by_cases hp : i.pause = true
    · simp [hd, hp]
    · simp [hd, hp]

theorem armed_bridge (s : Metronome.Thread.State) (i : Metronome.Thread.Input)
    (hreset : i.resetN = true) :
    (absState (Metronome.Thread.step s i)).armed =
      (Machine.threadNext (absState s) (absInput s i)).armed := by
  rw [Metronome.Thread.step_active s i hreset]
  simp only [absState, absInput, Machine.threadNext, Metronome.Thread.armedNext,
    Metronome.Thread.accept, Metronome.Thread.busy, Metronome.Thread.trig]
  by_cases hb : i.lineBeat = true
  · simp [hb]
  · simp [hb]

theorem late_bridge (s : Metronome.Thread.State) (i : Metronome.Thread.Input)
    (hreset : i.resetN = true) :
    (absState (Metronome.Thread.step s i)).late =
      (Machine.threadNext (absState s) (absInput s i)).late := by
  rw [Metronome.Thread.step_active s i hreset]
  simp only [absState, absInput, Machine.threadNext, Metronome.Thread.lateNext,
    Metronome.Thread.statClearLate]
  by_cases hs : i.hStatWe = true
  · simp [hs, bitAt_eq_nbit, Bool.or_comm]
  · simp [hs, Machine.Util.nbit, Bool.or_comm]

theorem ovr_bridge (s : Metronome.Thread.State) (i : Metronome.Thread.Input)
    (hreset : i.resetN = true) :
    (absState (Metronome.Thread.step s i)).ovr =
      (Machine.threadNext (absState s) (absInput s i)).ovr := by
  rw [Metronome.Thread.step_active s i hreset]
  simp only [absState, absInput, Machine.threadNext, Metronome.Thread.ovrNext,
    Metronome.Thread.overrunEvent, Metronome.Thread.busy, Metronome.Thread.trig,
    Metronome.Thread.statClearOvr]
  by_cases hs : i.hStatWe = true
  · simp [hs, bitAt_eq_nbit, Bool.or_comm]
  · simp [hs, Machine.Util.nbit, Bool.or_comm]

/-! ## The whole transition -/

/-- Reset on the cut side is the machine's global reset: the machine has no
per-thread reset input (its `Chip.resetStep` clears the whole register file),
so the bridge is stated for the active cycles and the reset case is
`resetState`. -/
theorem abs_reset : absState Metronome.Thread.resetState = (default : Machine.ThreadSt) := rfl

/-- On an active cycle, the cut's transition is the machine's `threadNext`
under the abstraction map and the two priority side conditions. -/
theorem step_eq (s : Metronome.Thread.State) (i : Metronome.Thread.Input)
    (hreset : i.resetN = true)
    (hacc_disp : ¬(Metronome.Thread.accept s i = true ∧ i.disp = true))
    (hpause_disp : ¬(i.pause = true ∧ i.disp = true)) :
    absState (Metronome.Thread.step s i) =
      Machine.threadNext (absState s) (absInput s i) := by
  apply threadSt_ext
  · exact pc_bridge s i hreset
  · exact en_bridge s i hreset
  · exact ready_bridge s i hreset hacc_disp
  · exact running_bridge s i hreset hpause_disp
  · exact armed_bridge s i hreset
  · exact late_bridge s i hreset
  · exact ovr_bridge s i hreset

/-- Reset cycle: the cut returns its reset state, whose abstraction is the
machine's all-zero thread state. -/
theorem step_reset_eq (s : Metronome.Thread.State) (i : Metronome.Thread.Input)
    (hreset : i.resetN = false) :
    absState (Metronome.Thread.step s i) = absState Metronome.Thread.resetState := by
  rw [Metronome.Thread.reset_step s i hreset]

/-! ## Chip-top event inputs vs the machine's `trigEvent`

`Machine.trigEvent` decodes §4's `event(TRIG)` from the line/pin/flag state.
The cut receives the decoded event as a free input `ev`, and the chip-top cut
proves it is wired to that decoder and to the doorbell, both gated by `!FRZ`
(§12.3).  `chipInput` writes that wiring down explicitly; `trig_refines` shows
the cut's trigger term is then exactly the machine's per-thread trigger input
in `Chip.runStep`. -/

/-- The cut input of thread `t` built from the chip state, with the chip-top
cut's wiring of the §4 trigger event and the §12.3 freeze gate.  Fields other
than `ev`/`db` are left at the caller's values. -/
def chipInput (i : Metronome.Thread.Input) (s : Machine.State) (cv : Machine.CfgView)
    (p : Machine.PinView) (lcs : Vector Machine.LineComb 4) (t : Nat) :
    Metronome.Thread.Input :=
  { i with
    ev := !s.dbg.frz && Machine.trigEvent s cv p lcs t
    db := !s.dbg.frz && Machine.Util.bit s.ctrl.db t }

/-- The cut's §4 trigger term on the chip-wired inputs equals the machine's
per-thread `trig` input, provided the cut's `EN` is the thread's `EN`. -/
theorem trig_refines (s : Metronome.Thread.State) (i : Metronome.Thread.Input)
    (ms : Machine.State) (cv : Machine.CfgView) (p : Machine.PinView)
    (lcs : Vector Machine.LineComb 4) (t : Nat)
    (hen : s.en = (Machine.Util.vget ms.threads t).en) :
    (absInput s (chipInput i ms cv p lcs t)).trig =
      (!ms.dbg.frz && (Machine.Util.vget ms.threads t).en &&
        (Machine.trigEvent ms cv p lcs t || Machine.Util.bit ms.ctrl.db t)) := by
  simp only [absInput, Metronome.Thread.trig, chipInput, hen]
  rcases ms.dbg.frz with _ | _ <;> simp

/-- A frozen cycle has no trigger on either side (§12.3). -/
theorem trig_frozen (i : Metronome.Thread.Input) (s : Machine.State)
    (cv : Machine.CfgView) (p : Machine.PinView) (lcs : Vector Machine.LineComb 4)
    (t : Nat) (hf : s.dbg.frz = true) :
    (chipInput i s cv p lcs t).ev = false ∧ (chipInput i s cv p lcs t).db = false := by
  simp [chipInput, hf]

end Metronome.Bridge.Thread
