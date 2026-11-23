# Discharging the configuration-write release window (AMBIG 1/2)

Module: `Metronome/ChipCut/Discharge/WindowWire.lean`
Namespace: `Metronome.ChipCut.Discharge.WindowWire`
Acceptance: `lake build Metronome.ChipCut.Discharge.WindowWire` (exit 0,
`-DwarningAsError=true`), 2026-11-22.  Evidence:
`data/raw/lean_chipcut_window_v4_20261122/`.

## 1. The blocker

`Metronome/ChipCut/Assembly.lean` derives `trace_refines'` from
`(hexp : ∀ n, ExplicitPremises s_T m_T pin_T)`, one field of which is

```lean
cwWindow : Discharge.mhcWindow m = false
```

`mhcWindow m = !(bit m.rqh 0 && bit m.rqh 1)`, and the machine's `rqh` is the
two-bit shift of `rst_q` starting from `0`.  The field is therefore **false** at
cycle 0 and in the first two active cycles after every reset (`rqh ∈ {0,1,2}`),
while `trace_refines'` is used precisely on active cycles (`hact : runRst s pin`).
So `premise_cw` (and hence `trace_refines'`) assumed a false premise exactly
where the window is open, and the capstone was vacuous.

This is now machine-checked, not just prose:

```lean
theorem mhcWindow_eq_true_iff (m : Machine.State) :
    mhcWindow m = true ↔ m.rqh.toNat ≠ 3

theorem absChip_reset_rqh (cont : Contents) :
    (absChip (resetState cont)).rqh = 0

theorem absChip_reset_window_open (cont : Contents) :
    mhcWindow (absChip (resetState cont)) = true

/-- The exact machine state `trace_refines'` uses at `n = 0`. -/
theorem old_premise_false_at_zero (pins : Nat → Machine.PinIn) (cont : Contents) :
    mhcWindow (machineStateAt pins (absChip (resetState cont)) 0) = true

/-- The replacement premise holds where the old one fails. -/
theorem reset_premise_ok (cont : Contents) :
    WindowQuiet (resetState cont) ∧ mhcWindow (absChip (resetState cont)) = true
```

`cwWindow` was standing in for `MemHostCfg.lean`'s named fact `cw_open_window`,
consumed by `Discharge.premise_cw`.  This module removes it.

## 2. What the window actually changes, and why it can be removed

In `Machine.cwNext` the window has exactly one effect:

```lean
let performed := if window then none else perf0
```

Everything else — the `CW` queue registers `CWA/CWV/CWQA/CWQD`, the held host
write `HH/HHA/HHD`, and `BWP` as `performed.isSome` — is independent of
`window`.  Consequently a window-open cycle is indistinguishable from a
closed-window cycle in which **no bank write is offered at all**
(`perf0 = none`).  The three ways to offer one are all absent in every
reachable open-window cycle:

| offer | condition | why impossible |
|---|---|---|
| held host write | `HH` (`s.arb.heldValid`) | `HH'` needs a host byte one cycle earlier; the window is at most one active cycle past a reset-shaped state |
| host configuration write | `hostCmd.wr` | a write strobe needs a *completing* byte (`ST_DATA` and `bitc = 7`); the host FSM is in `ST_CMD` at bit 0 (or one shifted bit) |
| queued core write draining | `CWV` (`s.cq.pending`) | the queue starts empty; a `CW.D` move needs `XV = 1`, and the cores start `XV = RV = 0` (dispatch needs `RUN` + `READY`, i.e. a host `CTRL.RUN` byte) |

Note the bound is sharper than "an SPI write needs three bytes": while the
window is open **at most one active cycle has elapsed since a reset-shaped
state** (the counter is `0`/`2` after a reset cycle and `1` after the first
active cycle; the second active cycle makes it `3`, the closed window).  So no
byte can complete in the window.

Therefore AMBIG 1/2 is **not** a cut/machine divergence and no witness of a
divergence exists: the window never *drops* a write, because no write is
offered.  This is the theorem `window_performed_none` below.

## 3. The invariant

```lean
def Quiet (s : State) : Prop :=
  s.hostCmd.wr = false ∧ s.cq.pending = false ∧ s.arb.heldValid = false ∧
    (∀ c : Fin 2, s.cores[c.val].xv = false)

def ResetFields (s : State) : Prop :=
  s.hostCmd = HostCmd.resetState ∧ s.cq = resetCq ∧ s.arb = resetArb ∧
    (∀ c : Fin 2, s.cores[c.val] = resetCore)

def WindowQuiet (s : State) : Prop :=
  (s.rqh.toNat = 1 → Quiet s) ∧
    ((s.rqh.toNat = 0 ∨ s.rqh.toNat = 2) → ResetFields s)
```

`resetCq = ⟨0, false, 0, 0, false⟩`, `resetArb = ⟨false, false, ⟨0,0⟩, ⟨0,0⟩⟩`,
`resetCore = ⟨false, false, 0, 0, 0, 0, 0⟩`.

The counter structure is what makes the invariant inductive:

* a **reset branch** produces `rqh' ∈ {0,2}` and a reset-shaped state, so
  `ResetFields` holds unconditionally (`resetFields_resetChip`);
* an **active branch** produces `rqh' = 1` only from `rqh ∈ {0,2}` (a
  reset-shaped state by the invariant), and `rqh' = 3` otherwise; in the first
  case one active cycle from a reset-shaped state is `Quiet`
  (`resetFields_activeStep_quiet`), in the second there is no obligation.

`ResetFields → Quiet` is `resetFields_quiet`, so the `rqh = 0/2` case directly
supplies the no-write facts.  Note the invariant is *not* a hypothesis on the
machine: `quiet_of_window` reads the machine's window bit off the cut's counter
through `ChipRel.rqh`, and the two cycles `rqh = 0`/`2` are reset-produced.

## 4. Deliverables (exact statements)

Reset/step/trace preservation:

```lean
theorem windowQuiet_reset (cont : Contents) :
    WindowQuiet (resetState cont)

theorem windowQuiet_step (s : State) (pin : Machine.PinIn) :
    WindowQuiet s → WindowQuiet (step s pin)

theorem windowQuiet_trace (pins : Nat → Machine.PinIn) (cont : Contents) :
    ∀ n, WindowQuiet (cutStateAt pins (resetState cont) n)
```

Reading the machine's window bit off the cut's counter:

```lean
theorem quiet_of_window (s : State) (m : Machine.State) :
    ChipRel s m → WindowQuiet s → Discharge.mhcWindow m = true → Quiet s
```

The window-open cycle is a genuine no-write cycle:

```lean
theorem window_performed_none (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hquiet : Quiet s)
    (hwin : Discharge.mhcWindow m = true) :
    (Discharge.mhcCwo m pin).performed = none
```

The window-open case of `Premises.cw`:

```lean
theorem cw_window_open (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hquiet : Quiet s) (hwin : Discharge.mhcWindow m = true) :
    CwRel (Machine.step m pin).cw (activeStep s pin).cq (activeStep s pin).arb
```

**The assembler's entry point** — exactly `Discharge.premise_cw`'s conclusion
and argument order, with `WindowQuiet s` in place of `mhcWindow m = false`:

```lean
theorem cw_window_ok (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (h19 : ¬ (s.arb.heldValid = true ∧ (hostCfgOf s).isSome = true))
    (hmove : Discharge.mhcCwMove m pin = Bridge.CfgWrite.mvOf (cqIn s pin))
    (hq : WindowQuiet s) :
    CwRel (Machine.step m pin).cw (activeStep s pin).cq (activeStep s pin).arb

theorem premise_cw_window ... :=  -- the same statement, under the replaced name
  cw_window_ok ...
```

`cw_window_ok` splits on `mhcWindow m`:

* closed (`= false`): delegates verbatim to `Discharge.premise_cw` (the `h19`
  and `hmove` arguments the assembler already supplies);
* open (`= true`): `quiet_of_window` gives `Quiet s`, and `cw_window_open`
  proves the `CwRel` from `window_performed_none`'s inputs: the machine's
  `performed = none`, both queue sides hold (`cq_step_quiet`), the arbiter
  raises neither `BWP` nor `HH` (`arb_quiet`), and the guarded bank-port
  payloads are vacuous.  The frozen/unfrozen debug split is irrelevant here:
  with nothing offered, `performed` is `none` either way.

## 5. Proof map

| lemma | content |
|---|---|
| `bit_and_toNat_three`, `window_true_toNat_ne_three`, `mhcWindow_eq_true_iff` | open window ↔ `rqh ≠ 3` |
| `rqhNext_active_toNat`, `rqhNext_reset_toNat` | active: `2(x%2)+1`; reset: `2(x%2)` |
| `quiet_mvEn` | `Quiet` → `mvEn = 0` (`Core.mvEn_zero`, both cores `XV = 0`) |
| `gw_quiet`, `cwWord_quiet`, `cqIn_writes_quiet` | no move → empty `CW` group → no `CW.AL/AH/D` decode |
| `cq_step_quiet` | empty queue + no group → `CoreQueue.step` holds (uses `pack_round`) |
| `hostCfgOf_none_of_wr_false` | no strobe → no host configuration write |
| `arb_heldValid_quiet`, `arb_previousWrite_quiet`, `arb_quiet` | no host write + empty queue → arbiter grants nothing (`BWP = HH = 0`) |
| `wrNext_resetState` | reset host FSM is in `ST_CMD`, so no write strobe |
| `resetFields_activeStep_quiet` | first active cycle from a reset-shaped state is `Quiet` |
| `machine_coreComb_moves_of_xv_false`, `mhcCwMove_quiet` | machine cores `XV = 0` → no `CW` move |
| `cwNext_quiet`, `cwNext_performed_none` | machine `cwNext`: window open, no host cfg, no move, `CWV = HH = 0` → queue holds, `performed = none` |
| `cw_window_open` | the open-window `CwRel` |
| `absChip_reset_window_open`, `old_premise_false_at_zero` | the old premise is false at `n = 0` |

## 6. Integration (assembler, owned elsewhere)

1. Add `import Metronome.ChipCut.Discharge.WindowWire` to
   `Metronome/ChipCut/Assembly.lean` (no cycle: `WindowWire` imports
   `MemHostCfg`, not `Assembly`).
2. In `ExplicitPremises`, replace the false field
   `cwWindow : Discharge.mhcWindow m = false` by
   `cwQuiet : WindowWire.WindowQuiet s` (or drop the field and pass
   `WindowWire.windowQuiet_trace pins cont n` at the use site).  Every caller of
   `trace_refines'`/`trace_refines'_all` builds `hexp` from `pins` and `cont`, so
   the new field is discharged by `windowQuiet_trace pins cont n` — the trace
   shape already matches: `s_T = cutStateAt pins (resetState cont) n`.
3. In `premises_of` (Assembly.lean ~line 917), replace

   ```lean
   Discharge.premise_cw s m pin hrel hinv hact hexp.cwH19
     (Discharge.MovePayloadWire.cwMove ...) hexp.cwWindow
   ```

   by

   ```lean
   WindowWire.cw_window_ok s m pin hrel hinv hact hexp.cwH19
     (Discharge.MovePayloadWire.cwMove ...) hexp.cwQuiet
   ```

   (`premise_cw_window` is an alias with the same statement if a drop-in name is
   preferred.)

No other premise changes: `cwH19` (AMBIG 19) and `cwMove` are untouched, and the
frozen branch of `premise_cw` is still reached in the closed-window case.

## 7. Evidence and verification status

* Lean-verified: the theorem statements are checked by Lean 4.35.0
  (`lake build`, warnings as errors; also a from-source `lake env lean`
  compile).  `#print axioms` (`axioms.txt`) shows only `propext`,
  `Quot.sound`, `Classical.choice`, plus the pre-existing `bv_decide`
  certificates of the imported CfgWrite/CoreQueue bridge — no `sorryAx`, no
  `native_decide` in this module.  The window lemmas (`cw_window_open`,
  `windowQuiet_*`, `cwNext_quiet`, `cwNext_performed_none`,
  `absChip_reset_window_open`, `reset_premise_ok`) use only `propext`,
  `Quot.sound` and (where noted) `Classical.choice`.
* Acceptance run (2026-11-22, `lean`):
  `lake build Metronome.ChipCut.Discharge.WindowWire` → exit 0,
  `✔ [60/60] Built ... (2.2s)`, warnings-as-errors via the lakefile.
* The claims are about the Lean specification (`Metronome.Machine`,
  `Metronome.Config`, `Metronome.CoreQueue`, `Metronome.ChipCut`), not measured
  silicon.  They rely on the standing `ChipRel`/`Inv` invariants of the
  capstone and on the window counter being the machine's own `rqh` shift.
* The proof is consistent with `Machine/AMBIGUITIES.md` rows 1/2 ("the two
  cycles are the first two with `rst_q` high"; "this cannot happen through
  SPI"): it proves the stronger statement that in those cycles the write path
  is quiet on both sides, so the window's "drop" is a no-op.
* Scope: this module does not import or modify `Assembly.lean` (not owned here).
  The splice recipe is §6, and it is machine-checked against the current
  `Assembly.lean`: a scratch file (outside the repository build) imports both
  modules and confirms that the assembler's existing `premise_cw` call
  typechecks against `WindowWire.cw_window_ok` when only the final argument is
  replaced by `hq : WindowWire.WindowQuiet s`, that
  `windowQuiet_trace pins cont n` discharges it on the assembler's trace
  `cutStateAt pins (resetState cont) n`, and that the replaced field is false at
  `n = 0`.  Evidence: `splice_check.log`.
