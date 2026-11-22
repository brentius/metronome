/-
# ChipCut: discharging the configuration-write release window (AMBIG 1/2)

`Metronome/ChipCut/Discharge/MemHostCfg.lean` states `Premises.cw` from the
named fact `cw_open_window : mhcWindow m = false` (the §1 release window of
`Machine.CwWrite`).  That fact is *false* at cycle 0 and in the first two active
cycles after a reset: the machine's `rqh` shift starts at `0`, so
`mhcWindow m = !(bit rqh 0 && bit rqh 1)` is `true` for `rqh ∈ {0,1,2}`.  The
capstone `trace_refines'` quantifies over all cycles with `hact : runRst s pin`
and would therefore assume a false premise exactly where the window is open, so
the assumption makes the trace theorem vacuous.  This file removes it.

## What the window actually changes

In `Machine.cwNext` the window only suppresses the *performed* bank write:

```
let performed := if window then none else perf0
```

Every other register (the `CW` queue, `HH`/`HHA`/`HHD`) is independent of
`window`.  Hence the window-open cycle behaves exactly like a closed-window
cycle with **no bank write offered at all**, provided the cycle offers no write:

* no held host write (`HH = false`),
* no host configuration write (`hostCfg = none`, i.e. `hostCmd.wr = false`),
* no queued core write draining (`CWV = false`).

In the open window these are reachable-state facts, not assumptions:

* a window-open state is either a stalled/reset state (`rqh = 0` or `2`) or the
  **first active cycle** after one (`rqh = 1`); the cut's reset state has
  `hostCmd.wr = false`, an empty `CW` queue and no held write;
* one active cycle later the host link has at most one shifted bit (a write
  strobe needs a *completing* byte: `ST_DATA` and `bitc = 7`), the cores are
  still `XV = RV = 0` (a dispatch needs `RUN` plus `READY`, which needs a host
  `CTRL.RUN` byte), so `mvEn = 0` and the `CW` write group is empty, and the
  arbiter's `heldValid` needs a host byte one cycle earlier.

The invariant is therefore indexed by `rqh`:
`WindowQuiet s := (rqh = 1 → Quiet s) ∧ ((rqh = 0 ∨ rqh = 2) → ResetFields s)`,
where `Quiet` is the three no-write facts plus `XV = 0` on both cores and
`ResetFields` is the full reset-field shape (`ResetFields → Quiet`).  It starts
at `resetState` and is preserved by `step` (the active branch turns `rqh = 0,2`
into `rqh = 1` and a reset-shaped state into a quiet one; every other branch
leaves the window closed or resets the state).

## Deliverables

* `WindowQuiet`, `Quiet`, `ResetFields` — the invariant;
* `windowQuiet_reset`, `windowQuiet_step`, `windowQuiet_trace` — reset, step and
  trace preservation;
* `cw_window_open` — `CwRel` in the window-open case under `Quiet`;
* `cw_window_ok` (and `premise_cw_window`) — **the assembler's entry point**: the
  exact conclusion of `Discharge.premise_cw`, with `WindowQuiet s` in place of
  `mhcWindow m = false`.

No `sorry`, no `native_decide`.  `Assembly.lean` is deliberately not imported.
-/

import Metronome.ChipCut.Discharge.MemHostCfg

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Metronome.ChipCut.Discharge.WindowWire

open Metronome
open Metronome.ChipCut.Discharge

/-! ## The reset shapes and the invariant -/

/-- The cut's power-on `CW` queue. -/
def resetCq : CoreQueue.State := ⟨0, false, 0, 0, false⟩

/-- The cut's power-on configuration arbiter. -/
def resetArb : Config.State := ⟨false, false, ⟨0, 0⟩, ⟨0, 0⟩⟩

/-- A core in its power-on shape. -/
def resetCore : Core.State := ⟨false, false, 0, 0, 0, 0, 0⟩

/-- The three no-write facts of a window-open cycle, plus "both cores are idle
(`XV = 0`, so `mvEn = 0` and the `CW` write group is empty)". -/
def Quiet (s : State) : Prop :=
  s.hostCmd.wr = false ∧ s.cq.pending = false ∧ s.arb.heldValid = false ∧
    (∀ c : Fin 2, s.cores[c.val].xv = false)

/-- A state whose configuration path, host command register, arbiter and cores
are in their power-on shapes.  This is what a reset/reset-stalled state has. -/
def ResetFields (s : State) : Prop :=
  s.hostCmd = HostCmd.resetState ∧ s.cq = resetCq ∧ s.arb = resetArb ∧
    (∀ c : Fin 2, s.cores[c.val] = resetCore)

/-- **The window invariant.**  While the release window is open, the
configuration-write path is quiet.  `rqh = 0`/`2` are reset-produced states (the
two-cycle shift), `rqh = 1` is the first active cycle after one; `rqh = 3` is the
closed window and carries no obligation. -/
def WindowQuiet (s : State) : Prop :=
  (s.rqh.toNat = 1 → Quiet s) ∧
    ((s.rqh.toNat = 0 ∨ s.rqh.toNat = 2) → ResetFields s)

/-! ## Reset-shape facts -/

/-- A reset-shaped state is quiet. -/
theorem resetFields_quiet (s : State) (h : ResetFields s) : Quiet s := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]; rfl
  · rw [h2]; rfl
  · rw [h3]; rfl
  · intro c
    rw [h4 c]
    rfl

/-- The power-on product is reset-shaped. -/
theorem resetFields_reset (cont : Contents) : ResetFields (resetState cont) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro c
  simp [resetState, resetCore]

/-- A reset cycle leaves a reset-shaped product (except the reset synchroniser,
the window counter and the memory contents, none of which `ResetFields` reads). -/
theorem resetFields_resetChip (s : State) (pin : Machine.PinIn) :
    ResetFields (resetChip s pin) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro c
  simp [resetChip, resetState, resetCore]

/-! ## Bit arithmetic of the window counter -/

/-- A two-bit word has both bits set exactly at value `3`. -/
theorem bit_and_toNat_three (x : BitVec 2) :
    (Machine.Util.bit x 0 && Machine.Util.bit x 1) = true ↔ x.toNat = 3 := by
  revert x
  decide

/-- An open window is not `rqh = 3`. -/
theorem window_true_toNat_ne_three {rqh : BitVec 2}
    (h : !(Machine.Util.bit rqh 0 && Machine.Util.bit rqh 1) = true) :
    rqh.toNat ≠ 3 := by
  intro h3
  have hb : (Machine.Util.bit rqh 0 && Machine.Util.bit rqh 1) = true :=
    (bit_and_toNat_three rqh).2 h3
  rw [hb] at h
  exact Bool.noConfusion h

/-- The machine's release-window bit is high exactly on the counter values other
than `3`.  This turns the arithmetic fact above into a statement about
`mhcWindow`, which is what the assembler's old premise read. -/
theorem mhcWindow_eq_true_iff (m : Machine.State) :
    mhcWindow m = true ↔ m.rqh.toNat ≠ 3 := by
  unfold mhcWindow
  constructor
  · intro h h3
    rw [(bit_and_toNat_three m.rqh).2 h3] at h
    exact Bool.noConfusion h
  · intro h
    cases hb : (Machine.Util.bit m.rqh 0 && Machine.Util.bit m.rqh 1) with
    | false => rfl
    | true => exact absurd ((bit_and_toNat_three m.rqh).1 hb) h

/-- On an active cycle the counter is `2·(rqh mod 2) + 1`. -/
theorem rqhNext_active_toNat (s : State) (pin : Machine.PinIn)
    (h : runRst s pin = true) :
    (rqhNext s pin).toNat = (s.rqh.toNat % 2) * 2 + 1 := by
  unfold rqhNext
  rw [if_pos h, BitVec.toNat_ofNat]
  have hv := s.rqh.isLt
  have hlt : (s.rqh.toNat % 2) * 2 + 1 < 2 ^ 2 := by omega
  exact Nat.mod_eq_of_lt hlt

/-- On a reset cycle the counter is `2·(rqh mod 2)` (an even value). -/
theorem rqhNext_reset_toNat (s : State) (pin : Machine.PinIn)
    (h : runRst s pin = false) :
    (rqhNext s pin).toNat = (s.rqh.toNat % 2) * 2 := by
  unfold rqhNext
  rw [if_neg (by simp [h]), BitVec.toNat_ofNat]
  have hv := s.rqh.isLt
  have hlt : (s.rqh.toNat % 2) * 2 < 2 ^ 2 := by omega
  exact Nat.mod_eq_of_lt hlt

/-! ## The window-open facts: no move, no host configuration write, no drain -/

/-- `Quiet` gives a zero move-enable bus: both cores are `XV = 0`. -/
theorem quiet_mvEn (s : State) (pin : Machine.PinIn) (h : Quiet s) : mvEn s pin = 0 := by
  obtain ⟨-, -, -, hxv⟩ := h
  have h0 : (s.cores[0]).xv = false := by simpa using hxv 0
  have h1 : (s.cores[1]).xv = false := by simpa using hxv 1
  show (Core.out true s.cores[1] (coreIn s pin 1)).mvEn ++
    (Core.out false s.cores[0] (coreIn s pin 0)).mvEn = (0 : BitVec 6)
  rw [Core.mvEn_zero true s.cores[1] (coreIn s pin 1) (Or.inl h1),
    Core.mvEn_zero false s.cores[0] (coreIn s pin 0) (Or.inl h0)]
  simp

/-- A zero move-enable bus presents an empty group word. -/
theorem gw_quiet (s : State) (pin : Machine.PinIn) (h : mvEn s pin = 0)
    (D : BitVec 6) : gw s pin D = ⟨false, 0, 0⟩ := by
  unfold gw
  rw [h, hitsMask_zero6]
  exact Moves.pickWord_none _ _ _ rfl

/-- A zero move-enable bus gives a zero `CW` write group. -/
theorem cwWord_quiet (s : State) (pin : Machine.PinIn) (h : mvEn s pin = 0) :
    cwWord s pin = 0 := by
  unfold cwWord
  rw [gw_quiet s pin h]
  decide

/-- A zero `CW` group sets none of the queue's three write decodes. -/
theorem cqIn_writes_quiet (s : State) (pin : Machine.PinIn) (h : cwWord s pin = 0) :
    CoreQueue.writeData (cqIn s pin) = false ∧
      CoreQueue.writeLow (cqIn s pin) = false ∧
      CoreQueue.writeHigh (cqIn s pin) = false := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [CoreQueue.writeData, CoreQueue.writeLow, CoreQueue.writeHigh, cqIn, h,
      CoreQueue.bitAt]

/-- **The `CW` queue holds** when it is empty and no write group is presented:
nothing is accepted, nothing drains, the counter and the payload are unchanged. -/
theorem cq_step_quiet (s : State) (pin : Machine.PinIn)
    (hpend : s.cq.pending = false) (hword : cwWord s pin = 0)
    (hact : runRst s pin = true) :
    (CoreQueue.step s.cq (cqIn s pin)).pending = false ∧
      (CoreQueue.step s.cq (cqIn s pin)).addr = s.cq.addr ∧
      (CoreQueue.step s.cq (cqIn s pin)).pendingAddr = s.cq.pendingAddr ∧
      (CoreQueue.step s.cq (cqIn s pin)).pendingData = s.cq.pendingData := by
  obtain ⟨hD, hL, hH⟩ := cqIn_writes_quiet s pin hword
  have hacc : CoreQueue.accept s.cq (cqIn s pin) = false := by
    simp [CoreQueue.accept, hD]
  have hdr : CoreQueue.drain s.cq (cqIn s pin) = false := by
    simp [CoreQueue.drain, hpend]
  have hrn : (cqIn s pin).resetN = true := hact
  have hlow : CoreQueue.nextLow s.cq (cqIn s pin) = CoreQueue.lowByte s.cq.addr := by
    simp [CoreQueue.nextLow, hacc, hL, hrn]
  have hhigh : CoreQueue.nextHigh s.cq (cqIn s pin) = CoreQueue.highByte s.cq.addr := by
    simp [CoreQueue.nextHigh, hacc, hL, hH, hrn]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [CoreQueue.step, hacc, hdr, hrn, hpend]
  · show CoreQueue.pack (CoreQueue.nextLow s.cq (cqIn s pin))
      (CoreQueue.nextHigh s.cq (cqIn s pin)) = s.cq.addr
    rw [hlow, hhigh]
    exact Bridge.CfgWrite.pack_round s.cq.addr
  · simp [CoreQueue.step, hacc, hrn]
  · simp [CoreQueue.step, hacc, hrn]

/-- A quiet host command register offers no host write at all. -/
theorem hostCfgOf_none_of_wr_false (s : State) (h : s.hostCmd.wr = false) :
    hostCfgOf s = none := by
  unfold hostCfgOf hwOf
  rw [h]
  rfl

/-- The arbiter's `HH` is never raised from a cycle with no host write. -/
theorem arb_heldValid_quiet (s : State) (pin : Machine.PinIn)
    (hwr : s.hostCmd.wr = false) : (arbStep s).next.heldValid = false := by
  have hcfg : hostCfgOf s = none := hostCfgOf_none_of_wr_false s hwr
  have hhost : (arbIn s).hostValid = false := by
    simp [arbIn, Bridge.CfgWrite.cfgIn, hcfg]
  simp [arbStep, Config.step, Config.beforeEdge, hhost]

/-- With an empty queue and no host write, the arbiter grants nothing, so its
stage (`BWP`) is clear as well. -/
theorem arb_previousWrite_quiet (s : State) (pin : Machine.PinIn)
    (hwr : s.hostCmd.wr = false) (hpend : s.cq.pending = false)
    (hheld : s.arb.heldValid = false) (hact : runRst s pin = true) :
    (arbStep s).next.previousWrite = false := by
  have hcfg : hostCfgOf s = none := hostCfgOf_none_of_wr_false s hwr
  have hhost : (arbIn s).hostValid = false := by
    simp [arbIn, Bridge.CfgWrite.cfgIn, hcfg]
  have hcore : (arbIn s).coreValid = false := by
    simp [arbIn, hpend]
  have hreset : (arbIn s).resetN = true := by
    simp [arbIn, Bridge.CfgWrite.cfgIn, hact]
  simp [arbStep, Config.step, Config.grant, Config.beforeEdge, hheld, hhost, hcore,
    hreset]

/-- The arbiter's next bank-port flags in a quiet cycle. -/
theorem arb_quiet (s : State) (pin : Machine.PinIn)
    (hwr : s.hostCmd.wr = false) (hpend : s.cq.pending = false)
    (hheld : s.arb.heldValid = false) (hact : runRst s pin = true) :
    (arbStep s).next.previousWrite = false ∧ (arbStep s).next.heldValid = false :=
  ⟨arb_previousWrite_quiet s pin hwr hpend hheld hact,
    arb_heldValid_quiet s pin hwr⟩

/-! ## One active cycle from a reset-shaped state is quiet -/

/-- A write strobe needs a `ST_DATA` byte state; the reset byte state is
`ST_CMD`. -/
theorem wrNext_resetState (i : HostCmd.Input) :
    (HostCmd.step HostCmd.resetState i).wr = false :=
  HostCmd.not_data_no_wr _ _ (by decide)

/-- **The first active cycle after a reset is quiet.**  The host link is still
in the command byte at bit 0 (no strobe), both cores have `XV = 0` (so
`mvEn = 0` and the `CW` write group is empty), the queue holds, and the arbiter
sees neither a host write nor a core request. -/
theorem resetFields_activeStep_quiet (s : State) (pin : Machine.PinIn)
    (h : ResetFields s) : Quiet (activeStep s pin) := by
  obtain ⟨hhc, hcq, harb, hco⟩ := h
  have hmv : mvEn s pin = 0 := by
    have hq : Quiet s := resetFields_quiet s ⟨hhc, hcq, harb, hco⟩
    exact quiet_mvEn s pin hq
  have hword : cwWord s pin = 0 := cwWord_quiet s pin hmv
  obtain ⟨hD, -, -⟩ := cqIn_writes_quiet s pin hword
  have hwr : s.hostCmd.wr = false := by rw [hhc]; rfl
  have hpend : s.cq.pending = false := by rw [hcq]; rfl
  have hheld : s.arb.heldValid = false := by rw [harb]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (HostCmd.step s.hostCmd (hostCmdIn s pin)).wr = false
    rw [hhc]
    exact wrNext_resetState _
  · show (CoreQueue.step s.cq (cqIn s pin)).pending = false
    rw [hcq]
    by_cases hrn : (cqIn s pin).resetN = true
    · simp [resetCq, CoreQueue.step, CoreQueue.accept, CoreQueue.drain, hD, hrn]
    · have hrf : (cqIn s pin).resetN = false := by simpa using hrn
      simp [CoreQueue.step, hrf]
  · exact arb_heldValid_quiet s pin hwr
  · intro c
    simp only [activeStep, Vector.getElem_ofFn]
    rw [hco c]
    simp [Core.step, Core.next, Core.load, Core.ra, resetCore]

/-! ## Reset, step and trace preservation -/

/-- An open window at `rqh = 1` is the first active cycle after a reset, and at
`rqh = 0`/`2` a reset-shaped state; either way the cycle is quiet. -/
theorem quiet_of_window (s : State) (m : Machine.State) (hrel : ChipRel s m)
    (hq : WindowQuiet s) (h : mhcWindow m = true) : Quiet s := by
  have h3 : s.rqh.toNat ≠ 3 := by
    rw [hrel.rqh]
    exact window_true_toNat_ne_three h
  have hlt : s.rqh.toNat < 4 := by
    have := s.rqh.isLt
    simpa using this
  rcases (by omega : s.rqh.toNat = 0 ∨ s.rqh.toNat = 1 ∨ s.rqh.toNat = 2) with
    h0 | h1 | h2
  · exact resetFields_quiet s (hq.2 (Or.inl h0))
  · exact hq.1 h1
  · exact resetFields_quiet s (hq.2 (Or.inr h2))

/-- The window invariant holds at power-on. -/
theorem windowQuiet_reset (cont : Contents) : WindowQuiet (resetState cont) := by
  refine ⟨?_, ?_⟩
  · intro h1
    simp [resetState] at h1
  · intro _
    exact resetFields_reset cont

/-! ## The old premise is false at power-on (machine-checked witness) -/

/-- `absChip` copies the cut's window counter, so the abstracted power-on state
has `rqh = 0`. -/
theorem absChip_reset_rqh (cont : Contents) : (absChip (resetState cont)).rqh = 0 :=
  rfl

/-- **The release window is open on the abstracted power-on state.**  This is the
machine state that `trace_refines'` feeds to `ExplicitPremises` at `n = 0`. -/
theorem absChip_reset_window_open (cont : Contents) :
    mhcWindow (absChip (resetState cont)) = true := by
  rw [mhcWindow_eq_true_iff, absChip_reset_rqh]
  decide

/-- **The assembler's old premise is false at `n = 0`.**  `trace_refines'` passes
`machineStateAt pins (absChip (resetState cont)) n`, which at `n = 0` is
`absChip (resetState cont)`; its window bit is `true`, so the field
`cwWindow : mhcWindow m = false` of `ExplicitPremises` cannot be inhabited. -/
theorem old_premise_false_at_zero (pins : Nat → Machine.PinIn) (cont : Contents) :
    mhcWindow (machineStateAt pins (absChip (resetState cont)) 0) = true :=
  absChip_reset_window_open cont

/-- **The replacement premise is inhabited where the old one fails.**  At
power-on the invariant `WindowQuiet` holds *and* the machine's window is open. -/
theorem reset_premise_ok (cont : Contents) :
    WindowQuiet (resetState cont) ∧ mhcWindow (absChip (resetState cont)) = true :=
  ⟨windowQuiet_reset cont, absChip_reset_window_open cont⟩

/-- The window invariant is preserved by one product cycle. -/
theorem windowQuiet_step (s : State) (pin : Machine.PinIn) (h : WindowQuiet s) :
    WindowQuiet (step s pin) := by
  unfold step
  by_cases hact : runRst s pin = true
  · rw [if_pos hact]
    refine ⟨?_, ?_⟩
    · -- `rqh' = 1` only from `rqh = 0`/`2`, a reset-shaped state
      intro h1
      have hx : s.rqh.toNat = 0 ∨ s.rqh.toNat = 2 := by
        have hv := s.rqh.isLt
        have h' : (rqhNext s pin).toNat = 1 := h1
        rw [rqhNext_active_toNat s pin hact] at h'
        omega
      exact resetFields_activeStep_quiet s pin (h.2 hx)
    · -- an active cycle never leaves an even counter
      intro h02
      have hv := s.rqh.isLt
      have h' : (rqhNext s pin).toNat = 0 ∨ (rqhNext s pin).toNat = 2 := h02
      rw [rqhNext_active_toNat s pin hact] at h'
      omega
  · have hact' : runRst s pin = false := by simpa using hact
    rw [if_neg hact]
    refine ⟨?_, ?_⟩
    · -- a reset cycle leaves an even counter
      intro h1
      have hv := s.rqh.isLt
      have h' : (rqhNext s pin).toNat = 1 := h1
      rw [rqhNext_reset_toNat s pin hact'] at h'
      omega
    · intro _
      exact resetFields_resetChip s pin

/-- The window invariant along the product trace from reset. -/
theorem windowQuiet_trace (pins : Nat → Machine.PinIn) (cont : Contents) :
    ∀ n, WindowQuiet (cutStateAt pins (resetState cont) n) := by
  intro n
  induction n with
  | zero => exact windowQuiet_reset cont
  | succ n ih =>
    rw [cutStateAt_succ]
    exact windowQuiet_step _ _ ih

/-! ## The machine's `CW` step in the window-open case -/

/-- The machine's `CW` move is `none` when both cores are `XV = 0`: `coreComb`
emits no moves. -/
theorem machine_coreComb_moves_of_xv_false (cs : Machine.State) (cv : Machine.CfgView)
    (p : Machine.PinView) (c : Nat) (frozen : Bool)
    (h : (Machine.Util.vget cs.cores c).xv = false) :
    (Machine.coreComb cs cv p c frozen).moves = [] := by
  simp [Machine.coreComb, h]

/-- The machine's `CW` move is `none` in a quiet cycle. -/
theorem mhcCwMove_quiet (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hxv : ∀ c : Fin 2, s.cores[c.val].xv = false) :
    mhcCwMove m pin = none := by
  have h0 : (Machine.Util.vget m.cores 0).xv = false := by
    simpa [Machine.Util.vget] using (hrel.cores 0).1.trans (hxv 0)
  have h1 : (Machine.Util.vget m.cores 1).xv = false := by
    simpa [Machine.Util.vget] using (hrel.cores 1).1.trans (hxv 1)
  unfold mhcCwMove mhcWs mhcCbs
  simp [machine_coreComb_moves_of_xv_false, h0, h1, Machine.resolveMoves]

/-- **The machine's `cwNext` with the window open, no host write, no move and an
empty queue** holds the queue and raises none of the bank-port flags. -/
theorem cwNext_quiet (cw : Machine.CwSt) (frozen : Bool)
    (hh : cw.hh = false) (hv : cw.cwv = false) :
    (Machine.cwNext cw none none true frozen).st.cwa = cw.cwa ∧
      (Machine.cwNext cw none none true frozen).st.cwv = false ∧
      (Machine.cwNext cw none none true frozen).st.cwqa = cw.cwqa ∧
      (Machine.cwNext cw none none true frozen).st.cwqd = cw.cwqd ∧
      (Machine.cwNext cw none none true frozen).st.bwp = false ∧
      (Machine.cwNext cw none none true frozen).st.hh = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Machine.cwNext, hh, hv, Bridge.CfgWrite.bv_toNat, Bridge.CfgWrite.bv_mod8]

/-! ## The window-open `CwRel` -/

/-- In the window-open cycle the machine performs no bank write: `performed` is
suppressed by the window, and with `HH = 0`, `CWV = 0` and no host configuration
write there is nothing to suppress (`perf0 = none`). -/
theorem cwNext_performed_none (cw : Machine.CwSt) (frozen : Bool)
    (hh : cw.hh = false) (hv : cw.cwv = false) :
    (Machine.cwNext cw none none true frozen).performed = none := by
  simp [Machine.cwNext, hh, hv]

/-- The machine's performed configuration write is `none` throughout an open
release window.  This is the physical content of AMBIG 1/2: the window never
*drops* a write, because no write is offered. -/
theorem window_performed_none (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hquiet : Quiet s)
    (hwin : mhcWindow m = true) :
    (mhcCwo m pin).performed = none := by
  obtain ⟨hwr, hpend, hheld, hxv⟩ := hquiet
  have hcfgS : hostCfgOf s = none := hostCfgOf_none_of_wr_false s hwr
  have hcfg : mhcHostCfg m pin = none := by
    rw [cw_open_hostCfg s m pin hinv hrel, hcfgS]
  have hmove : mhcCwMove m pin = none := mhcCwMove_quiet s m pin hrel hxv
  have hhh : m.cw.hh = false := by rw [hrel.cw.hh]; exact hheld
  have hhv : m.cw.cwv = false := by rw [hrel.cw.cwv]; exact hpend
  unfold mhcCwo
  rw [hcfg, hmove, hwin]
  exact cwNext_performed_none m.cw m.dbg.frz hhh hhv

/-- **`Premises.cw` in the window-open case.**  With the release window open the
machine suppresses the bank write; the cut offers none (no held host write, no
host configuration write, no core drain) and its queue holds, so the two
configurations agree. -/
theorem cw_window_open (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hquiet : Quiet s) (hwin : mhcWindow m = true) :
    CwRel (Machine.step m pin).cw (activeStep s pin).cq (activeStep s pin).arb := by
  obtain ⟨hwr, hpend, hheld, hxv⟩ := hquiet
  have hq' : (m.rq && pin.rstn) = true := by rw [← hrel.rstQ]; exact hact
  have hmv : mvEn s pin = 0 := quiet_mvEn s pin ⟨hwr, hpend, hheld, hxv⟩
  have hword : cwWord s pin = 0 := cwWord_quiet s pin hmv
  have hcq := cq_step_quiet s pin hpend hword hact
  have harb := arb_quiet s pin hwr hpend hheld hact
  have hcfgS : hostCfgOf s = none := hostCfgOf_none_of_wr_false s hwr
  have hcfg : mhcHostCfg m pin = none := by
    rw [cw_open_hostCfg s m pin hinv hrel, hcfgS]
  have hmove : mhcCwMove m pin = none := mhcCwMove_quiet s m pin hrel hxv
  have hhh : m.cw.hh = false := by rw [hrel.cw.hh]; exact hheld
  have hhv : m.cw.cwv = false := by rw [hrel.cw.cwv]; exact hpend
  obtain ⟨hca, hcv, hcqa, hcqd, hbwp, hhhh⟩ := cwNext_quiet m.cw m.dbg.frz hhh hhv
  have hstepM : (Machine.step m pin).cw =
      (Machine.cwNext m.cw none none true m.dbg.frz).st := by
    rw [step_cw m pin hq']
    show (mhcCwo m pin).st = _
    unfold mhcCwo
    rw [hcfg, hmove, hwin]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (Machine.step m pin).cw.cwa = (activeStep s pin).cq.addr
    rw [hstepM, hca]
    exact hrel.cw.cwa.trans hcq.2.1.symm
  · show (Machine.step m pin).cw.cwv = (activeStep s pin).cq.pending
    rw [hstepM, hcv]
    exact hcq.1.symm
  · show (Machine.step m pin).cw.cwqa = (activeStep s pin).cq.pendingAddr
    rw [hstepM, hcqa]
    exact hrel.cw.cwqa.trans hcq.2.2.1.symm
  · show (Machine.step m pin).cw.cwqd = (activeStep s pin).cq.pendingData
    rw [hstepM, hcqd]
    exact hrel.cw.cwqd.trans hcq.2.2.2.symm
  · show (Machine.step m pin).cw.bwp = (activeStep s pin).arb.previousWrite
    rw [hstepM, hbwp]
    exact harb.1.symm
  · show (Machine.step m pin).cw.hh = (activeStep s pin).arb.heldValid
    rw [hstepM, hhhh]
    exact harb.2.symm
  · intro hb
    rw [hstepM, hbwp] at hb
    exact Bool.noConfusion hb
  · intro hb
    rw [hstepM, hbwp] at hb
    exact Bool.noConfusion hb
  · intro hh
    rw [hstepM, hhhh] at hh
    exact Bool.noConfusion hh
  · intro hh
    rw [hstepM, hhhh] at hh
    exact Bool.noConfusion hh

/-! ## The assembler's entry point -/

/-- **`Premises.cw` without the release-window premise.**  In the closed-window
case this is `Discharge.premise_cw`; in the open case it is `cw_window_open`,
whose no-write facts come from the `WindowQuiet` invariant. -/
theorem cw_window_ok (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (h19 : ¬ (s.arb.heldValid = true ∧ (hostCfgOf s).isSome = true))
    (hmove : mhcCwMove m pin = Bridge.CfgWrite.mvOf (cqIn s pin))
    (hq : WindowQuiet s) :
    CwRel (Machine.step m pin).cw (activeStep s pin).cq (activeStep s pin).arb := by
  by_cases hw : mhcWindow m = false
  · exact premise_cw s m pin hrel hinv hact h19 hmove hw
  · have hwt : mhcWindow m = true := by
      cases h : mhcWindow m <;> simp_all
    exact cw_window_open s m pin hrel hinv hact
      (quiet_of_window s m hrel hq hwt) hwt

/-- `cw_window_ok` under the name of the premise it replaces. -/
theorem premise_cw_window (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (h19 : ¬ (s.arb.heldValid = true ∧ (hostCfgOf s).isSome = true))
    (hmove : mhcCwMove m pin = Bridge.CfgWrite.mvOf (cqIn s pin))
    (hq : WindowQuiet s) :
    CwRel (Machine.step m pin).cw (activeStep s pin).cq (activeStep s pin).arb :=
  cw_window_ok s m pin hrel hinv hact h19 hmove hq

end Metronome.ChipCut.Discharge.WindowWire
