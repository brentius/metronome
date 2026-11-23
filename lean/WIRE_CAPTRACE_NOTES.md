# W5 notes: the chip-level capture invariant `CapInv`

Written 2026-11-22.  Files:

* `lean/Metronome/ChipCut/Discharge/CapTrace.lean` — the new module
  (`namespace Metronome.ChipCut.Discharge`, imports
  `Metronome.ChipCut.Discharge.CoreCombWire` and `Metronome.Bridge.StreamBuf`;
  nothing else is edited).
* Evidence: `data/raw/lean_chipcut_captrace_v4_20261122/` — `axioms.txt`
  (18 `#print axioms` lines, none `sorryAx`), `statements.txt` (18 `#check`
  lines), `axioms.lean`, `statements.lean`, `commands.log`, and the
  first-draft scratch `scratch_captrace_draft.lean`.

Acceptance: `lake build Metronome.ChipCut.Discharge.CapTrace` exits 0 with
`-DwarningAsError=true` (from `lakefile.toml`; Lean 4.35.0, core libraries only):
125 s fresh, 65 jobs, no warnings; 0.4 s cached.  Every goal is closed
(`axioms.txt`: `[propext]`, `[propext, Quot.sound]` or
`[propext, Classical.choice, Quot.sound]`, never `sorryAx`); no decision is made
natively; no `lake clean` and no `.olean` deletion; `git diff --quiet HEAD -- src`
exits 0; `lake build Metronome.ChipCut.Assembly` still exits 0 (76 jobs, cached),
so the new file collides with nothing in the downstream assembly.

Purpose.  `CoreCombWire.contents_open_req_wb` (§11) takes the *unguarded*
premise `hwb : ∀ k, (streamAt s k).pv = true → m.streams[k].wb = (streamAt s
k).wb`, and `Assembly.OpenWiring.contentsWb` carries it as the last residual of
the `contents` premise.  That form is **false at a reachable state**
(`Bridge.StreamBuf.capWb_reachable_witness`: a receive state with a pending byte
and a stale `WB`; `capWb_hchange_excluded` shows the strengthened mode-quietness
excludes it), so no state relation can imply it.  `Bridge.StreamBuf`'s
`CapModeOK` is the true, mode-indexed form; this module lifts it to a chip-level
trace invariant and delivers the request congruence in the mode-2 form that
`Machine.streamReq` actually reads.

## 1. The relation and its index

```lean
def CapInv (s : State) (m : Machine.State) : Prop :=
  ∀ k : Fin 2, Bridge.StreamBuf.CapModeOK (stateMode s k) (streamAt s k.val) m.streams[k]
```

with `CapModeOK mode s m := (mode = 2 → s.ld = false) ∧ (mode = 2 → s.pv = true →
s.wb = m.wb)` (`Bridge.StreamBuf` §12).

The index is the cut's **current** mode `stateMode s k` — the `ShapeModeOK`
pattern of `Assembly.lean` §2 (A1's `streamShapeInv`).  That is exactly the index
`capModeOK_step` produces: the mode used to compute the next stream state is the
*cycle's* `modeOf`, and `stateMode s k = Bridge.StreamB.modeOf (k.val == 0)
(streamIn s pin k.val)` at the cycle (`stateMode_modeOf`).  Mode 2 never occurs
for stream 1: `CAP = 0` makes `modeOf false i ∈ {0, 1}` (`stateMode_cap_false`
in `Assembly.lean`), so the *invariant* itself is non-vacuous only at `k = 0`, but
stating it over every `k` costs nothing and keeps the relation uniform.

Supporting facts in §1 of the module:

| theorem | statement |
|---|---|
| `machMode_eq_stateMode` | `ChipRel s m → machMode m k = stateMode s k` (both read `cfg.rx` and the two mode bits; `ChipRel.cfg` + `DbgRel`) |
| `stateMode_modeOf` | `stateMode s k = modeOf (k.val == 0) (streamIn s pin k.val)` (`stateMode_eq` ∘ `absMode_eq`) |
| `streamAt_activeStep'` | `streamAt (activeStep s pin) k = Stream.step (k.val == 0) (streamAt s k) (streamIn s pin k)` |
| `ldNext_false` | `i.resetN = true → st.ld = false → st.rq = false → Stream.ldNext cap st i = false` |

## 2. Reset, step, trace

```lean
theorem capInv_reset (cont : Contents) :
    CapInv (resetState cont) (absChip (resetState cont))

theorem capInv_step_active (s) (m) (pin) (hrel : ChipRel s m)
    (hact : runRst s pin = true) (hcap : CapInv s m)
    (hin : ∀ k : Fin 2, StreamInputAgree m (streamAt s k.val) (streamIn s pin k.val) k)
    (hq : stream_mode_quiet s pin) :
    CapInv (step s pin) (Machine.step m pin)

theorem capInv_step_reset (s) (m) (pin) (hact : runRst s pin = false)
    (hcap : CapInv s m) :
    CapInv (step s pin) (Machine.step m pin)

theorem capInv_step_of_input (s) (m) (pin) (hrel : ChipRel s m) (hcap : CapInv s m)
    (hin : ∀ k, StreamInputAgree m (streamAt s k.val) (streamIn s pin k.val) k)
    (hq : stream_mode_quiet s pin) :
    CapInv (step s pin) (Machine.step m pin)

theorem capInv_step (s) (m) (pin) (hrel : ChipRel s m) (hinv : Inv s)
    (hcap : CapInv s m) (hw : StreamWire s m pin) (hq : stream_mode_quiet s pin) :
    CapInv (step s pin) (Machine.step m pin)

theorem capInv_trace (pins) (cont)
    (hrel : ∀ n, ChipRel (cutStateAt pins (resetState cont) n)
      (machineStateAt pins (absChip (resetState cont)) n))
    (hin : ∀ n, runRst (cutStateAt pins (resetState cont) n) (pins n) = true →
      ∀ k : Fin 2, StreamInputAgree (machineStateAt … n) (streamAt (cutStateAt … n) k.val)
        (streamIn (cutStateAt … n) (pins n) k.val) k)
    (hq : ∀ n, stream_mode_quiet (cutStateAt pins (resetState cont) n) (pins n)) :
    ∀ n, CapInv (cutStateAt pins (resetState cont) n)
      (machineStateAt pins (absChip (resetState cont)) n)
```

`capInv_reset` is at the reset *pair* of `trace_refines`
(`resetState cont` against `absChip (resetState cont)`): the cut stream is
`Stream.resetState` (`streamAt_resetState`), the machine stream is
`Bridge.StreamB.abs Stream.resetState = default` (`by decide`), and
`capModeOK_reset` closes it for any mode index.

The active step splits on whether the mode changes (the two-state comparison is
what `stream_mode_quiet` is stated over):

* **unchanged** (`stateMode (activeStep s pin) k = stateMode s k`): rewrite the
  goal's index to the cycle's `modeOf` (`stateMode_modeOf`), rewrite the
  machine's next stream with `streamsNext_eq` (as `premise_streams` does — it
  needs the `StreamInputAgree` of `hin` and `ChipRel.cfg`, and the `frz`
  agreement `DbgRel.frz_eq`), and apply `Bridge.StreamBuf.capModeOK_step` at
  `pmode = stateMode s k` with `hchange = Or.inl (modeOf … = stateMode s k)`.
  `hcfg` is `rfl` (the machine's config is `cfgOf`, the bridge's).
* **changed**: `stream_mode_quiet` gives `PV = 0` in the state and in the next
  state and `LD = RQ = 0`, so the next `LD` is `false` (`ldNext_false`) and the
  next `PV` is `false`; both capture clauses are vacuous and **no machine fact is
  used**.  This is the branch that the extended quietness (§12 of
  `BRIDGE_STREAMBUF_NOTES.md`, decision of 2026-11-22d) makes true: a
  receive → capture switch with `PV = 1` is excluded, so the capture slot never
  has to be related across a mode change.

The reset edge is vacuous with no premise: the cut loads `Stream.resetState`,
whose `LD` and `PV` are clear, so both clauses are true whatever the machine
does (no `Machine.resetStep`/`State.init` reasoning needed).

Frozen cycles need nothing extra: both branches run under `i.frz = m.dbg.frz`
freely (B1's `capModeOK_step` is proved for all `i.frz`), and a frozen cycle
that changes a mode register is covered by the changed branch.

## 3. The consumer: the exact shape delivered

```lean
theorem contentsWb_of_capInv (s) (m) (k : Fin 2) (hcap : CapInv s m)
    (hm2 : stateMode s k = 2) (hpv : (streamAt s k.val).pv = true) :
    m.streams[k].wb = (streamAt s k.val).wb          -- machine-first (`.symm` of CapModeOK's clause)

theorem capLd_of_capInv (s) (m) (k) (hcap : CapInv s m) (hm2 : stateMode s k = 2) :
    (streamAt s k.val).ld = false
```

The **unguarded** form `hwb : PV → m.WB = cut.WB` is *not* delivered because it
is not true (§11 of `BRIDGE_STREAMBUF_NOTES.md`); the mode-2 guard is exact for
the request congruence:

* `streamReq_congr_cap` — `CoreCombWire.streamReq_congr` with the `WB` clause
  weakened to `mode = 2 → a.pv = true → a.wb = b.wb` (mode 2 is the only branch
  of `Machine.streamReq` that reads `WB`: the capture `wrWord`);
* `mhcModesReq_abs_cap` / `_cap0` / `_cap1` — `mhcModesReq_abs_wb` with that
  premise (guarded by the cut's `stateMode s k = 2`, converted to the `modeOf`
  form inside with `stateMode_modeOf`);
* `contents_open_req_cap` — **`contents_open_req_wb`, verbatim in its
  conclusion** (`mhcReq m pin = mhcReq (absChip s) pin`) with the `hwb` premise
  replaced by `hcap : CapInv s m` (plus `ChipRel`, `Inv`, and the mode
  hypothesis `hmode`, exactly as `contents_open_req_wb`).

### Splice for `Assembly.lean`

The residual `OpenWiring.contentsWb` (unguarded) must be *replaced*, not
discharged: in `premises_of`'s `contents` field, use

```lean
Discharge.contents_open_req_cap s m pin hrel hinv hwire_mode hcap
```

in place of `Discharge.contents_open_req_wb s m pin hrel hinv hmode hopen.contentsWb`,
and carry `hcap : Discharge.CapInv s m` (or `hcap : ∀ n, CapInv (cutStateAt … n)
(machineStateAt … n)`, from `Discharge.capInv_trace`) instead of the
`contentsWb` field of `OpenWiring`.  The mode hypothesis is `streamWire_mode`'s
statement, which `premises_of` already builds as its local `hmode`
(`fun k => streamWire_mode s m pin hrel k`).

To get the per-cycle `hin`, `premises_of`'s local `hIn` (the `StreamInputAgree`
construction from `StreamMoveWire.streams_rx_low1`, `MoveFabricKeyed.streams_adv`,
`streams_ctl_combined'`, `stream_served`, …) has to be factored out into a
standalone theorem (`hact → ∀ k, StreamInputAgree …`) so that `capInv_trace` can
consume it at every cycle; `capInv_trace` takes it in exactly that guarded shape
(`trace_refines`' `hprem` pattern).

## 4. Hypotheses and limitations

* The step takes the per-stream input agreement `StreamInputAgree` (packaged as
  `StreamWire.input` in `capInv_step`).  It is genuine wiring, not a relation
  fact: the machine's next `WB` is `Machine.streamNext`'s, so the capture word of
  the next state is read from the machine's own `StreamIn` record.  The unchanged
  branch is the only place that needs it; the changed and reset branches need no
  machine fact.
* `Inv s` is in `capInv_step`'s signature for uniformity with the other discharge
  invariants but is not consumed (no `Mem`/`HostPins`/core fact enters the
  capture invariant).
* `CapInv` says nothing in modes `0, 1, 3`; that is exactly the strength the
  consumer needs and exactly the strength that is true (the unguarded form is
  witnessed false).  The capture-mode `LD = false` conjunct is what makes the
  coupling to `BufRel`/`AbsRelB` unnecessary.
* Lean-checked implications between the cut spec and the machine spec (no RTL
  co-simulation); the witnesses quoted for the unguarded form are B1's
  (`Bridge.StreamBuf`).

## 5. Evidence and commands

`data/raw/lean_chipcut_captrace_v4_20261122/commands.log` records exit codes and
wall times.  Reproduce:

```powershell
cd lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.CapTrace
lake env lean -DwarningAsError=true ../data/raw/lean_chipcut_captrace_v4_20261122/axioms.lean
lake env lean ../data/raw/lean_chipcut_captrace_v4_20261122/statements.lean
lake build Metronome.ChipCut.Assembly
cd ..
git diff --quiet HEAD -- src
```
