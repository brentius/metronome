# ChipCut assembly (round 12): `Metronome/ChipCut/Assembly.lean`

Status: **`lake build Metronome.ChipCut.Assembly` exits 0** with the lakefile's
`-DwarningAsError=true` (77 jobs); axioms driver exit 0, no `sorryAx`, no
`native_decide`, no `admit`, no warnings.  `src/` untouched.

**No residual wiring record is left.**  `OpenWiring` is **deleted** (it had one
field, `dbgReal`) and `ExplicitPremises.rlvpFrozen` is deleted: every one of the
sixteen `Premises` fields is now a theorem of the discharge suite.

| file | SHA-256 | bytes |
|---|---|---|
| `Assembly.lean` | `AE75B0D0866F0791A75B63A912470980ACE78C8C5BF2997DB9B54B1F1F2A5781` | 53455 |
| `Discharge/StreamDbg.lean` | `FBE04171909718EDBC7F9BDB5DA2E9F401DF38145E49B69F00DBC89133A1861C` | 58752 |

## Round 12: the frozen debug cycle — `dbgReal` gone

The orchestrator fixed the machine spec (`Machine.dbgNext`: `rlvp := if frozen
then rlvp else rlv`, RTL/Python-consistent), restated `Bridge.Debug.dbgNext_rlvp`
and patched `dbg_step_bridge`/`hc8` for the unfrozen case.  Consequently:

* `DbgWire.real` (the `FRZ = false` field) is **deleted**; `premise_dbg` is now
  proved for **both** `FRZ` values.  Its only use was `hc8` (`RLVP`), which now
  splits on `(dbgCtrlIn s pin).frz`:
  - frozen: `m.dbg.frz = true`, `dbgNext_rlvp` gives `m.dbg.rlvp` and
    `Debug.Ctrl.rlvPrevNext` gives `s.dbgCtrl.rlvPrev`, joined by
    `DbgRel.rlvp_eq`;
  - unfrozen: the previous `DBGNext_rlvp` + `rlvp_agree` + `DbgRel.rlv_eq` path.
  Every other field is `FRZ`-agnostic: `ectl_bridge`/`dc_bridge`/`men_bridge`/
  `misr_bridge` already take `frozen` as a parameter, the `EMASK`/`RLV` value
  theorems take only `ChipRel`/`Inv`/`runRst` (+ the `WV`-guarded slot and
  `happly`), and `FREEZE`/`FRZ`/`FRZD` read `CoreCtl.freezeStep`/`dbgNext_*`.
* `ExplicitPremises.rlvpFrozen` deleted (false after the machine fix).
* `OpenWiring` (one field: `dbgReal`) deleted; `premises_of`,
  `chip_step_refines'`, `trace_refines'_all`, `trace_refines'` no longer take it.
  `streamRelX_step` loses its (now unused) `hopen` parameter too.

### Final statements

```lean
premise_dbg : ChipRel s m → Inv s → runRst s pin = true → DbgWire s m pin →
  DbgRel (activeStep s pin) (Machine.step m pin).dbg

premises_of : ChipRel s m → Inv s → AbsInv s → ExecInv s → HostPinInv s →
  ldModeInv s → LandingP0 s → LandingStream s → laneInv s → CapInv s m →
  streamShapeInv s → StreamRelX s m → ExplicitPremises s m pin →
  runRst s pin = true → Premises s m pin

chip_step_refines' : (same invariants) → ExplicitPremises s m pin →
  ChipRel (step s pin) (Machine.step m pin)

trace_refines'_all : cont.ramOwner = 0 →
  (∀ n, stream_mode_quiet (cut n) (pins n)) →
  (∀ n, ExplicitPremises (cut n) (mach n) (pins n)) →
  ∀ n, ChipRel (cut n) (mach n) ∧ CapInv (cut n) (mach n) ∧ StreamRelX (cut n) (mach n)

trace_refines' : (same three hypotheses) → ∀ n, ChipRel (cut n) (mach n)
```

## Round 11: (3) step/trace + (4) the stream residuals

### (3) `StreamRelX` — step and trace

The relation was restated to its **disjunctive** form (`HeldOK`'s own shape), so
an unfrozen cycle discharges it trivially (`FRZD' = FRZ = false`) and only a
frozen cycle needs content:

```lean
def StreamRelX (s) (m) : Prop := ∀ k, (streamAt s k).ld = true →
  s.freeze.frzd = false ∨ (stateMode s k = 0 ∧ wb = m.streams[k].wb) ∨
    (stateMode s k = 3 ∧ HeldLanding (streamAt s k) m.streams[k])
```

New proved pieces:

* `stateMode_zero_txMode` / `stateMode_three_rpl` / `ldMode_branch` (moved to
  `Discharge/CoreCombWire.lean` — the stream bridge needs them and `StreamDbg`
  precedes `CoreCombWire` in the import graph);
* `streamRelX_hok` — `StreamRelX` ⇒ `HeldOK` per stream, **no** `ldModeInv`
  needed (the disjunction carries the branch facts);
* `frzd_activeStep` (`FRZD' = FRZ`), `frozen_holds_unguarded` (cut `WB`/`NB`/
  `WV`/`LD` hold when `FRZD`), `mach_frozen_holds_unguarded` (machine `WB`/`NB`
  hold);
* `streamRelX_step_active` — per stream: unfrozen ⇒ `Or.inl`; frozen landing ⇒
  `wb_after_frozen_tx` / `heldLanding_after_frozen_replay`; frozen non-landing ⇒
  the pre-state disjunct carried through the holds; frozen *mode change* ⇒
  `stream_mode_quiet` gives `LD = false`;
* `streamRelX_step` — reset branch (`resetChip` streams are `resetState` ⇒
  `LD = false`) plus the active branch;
* `trace_refines'_all` — the trace induction now carries
  `ChipRel ∧ CapInv ∧ StreamRelX` (reset: `rel_reset`, `capInv_reset`,
  `streamRelX_reset`); the headline `trace_refines'` is its `.1`.

### (4) The stream residuals

* **`streamBufrel` proved** (`streamBufrel_of`): frozen cycles use B1's
  `frozen_rel_landing_flush` / `_rewind_flush` (which cover `LD ∧ !FRZD`), with
  `hldmode` from `ldModeInv` and `hshape` from `streamShapeInv`; unfrozen cycles
  use `bufRel_step_unfrozen_guarded` with `hok` from `streamRelX_hok`.
* **`StreamWire` restated** to `mode` + `input` + `bufrel` (`StreamDbg.lean`):
  the `hostctl` field (flush = false) and the **false** `landing` field are
  deleted.  `streams_field_0/1` now close the frozen cycle with the `_flush`
  bridges, taking only `hldmode` (a per-stream `LD`-branch hypothesis) and
  `hshp` (`ShapeOK`), instead of `hland`/`hfl`.  `HostPinWire.lean` is untouched
  (its doc comment still mentions the old field; it is a W-series file).
* `premises_of` / `chip_step_refines'` gained `(hshape : streamShapeInv s)
  (hX : StreamRelX s m)`; `trace_refines'_all` supplies them
  (`streamShapeInv_trace`, the induction hypothesis).

## Round 10: (3) `StreamRelX` spliced (conditional landing relation)

**Key correction found this round:** `Bridge.StreamBuf.HeldOK` is a
**disjunction**, not a conjunction:

```lean
def HeldOK (cap) (s) (i) (m) : Prop :=
  i.frzd = false ∨ (Stream.txMode cap i = true ∧ s.wb = m.wb) ∨
    (Stream.rpl cap i = true ∧ HeldLanding s m)
```

So `bufRel_step_unfrozen_guarded`'s `hok` is discharged by `FRZD = 0` alone, and
real content is needed only on a cycle whose `FRZD` is set — the first unfrozen
cycle after a freeze.  That is exactly what `StreamRelX` carries, and it also
means the relation does **not** need a `FRZD` conjunct (which would be false:
`Stream.ldNext` holds `LD` through a freeze).

Landed in `Assembly.lean` (all proved, all `#print axioms` clean):

```lean
def StreamRelX (s : State) (m : Machine.State) : Prop :=
  ∀ k : Fin 2, (streamAt s k.val).ld = true →
    ((stateMode s k = 0 → (streamAt s k.val).wb = m.streams[k].wb) ∧
     (stateMode s k = 3 → Bridge.StreamBuf.HeldLanding (streamAt s k.val) m.streams[k]))

theorem streamRelX_reset (cont) (m) : StreamRelX (resetState cont) m
theorem stateMode_of_txMode  : txMode ⇒ stateMode = 0
theorem stateMode_of_rpl     : rpl ⇒ stateMode = 3
theorem ldMode_branch        : ldModeInv + LD ⇒ txMode ∨ rpl
theorem streamRelX_hok       : StreamRelX + ldModeInv ⇒ ∀ k, LD → HeldOK …
theorem heldLanding_after_frozen_replay
    : frozen + replay landing ⇒ HeldLanding at the next state   -- mode-3 producer
theorem wb_after_frozen_tx
    : frozen + transmit landing ⇒ WB agreement at the next state -- mode-0 producer
```

`streamRelX_hok` is the (4) interface: it turns the relation plus the already
proved `ldModeInv` into the exact `hok` hypothesis of
`bufRel_step_unfrozen_guarded`.  The two "producer" theorems are B1's
`heldLanding_frozen_landing` / `wb_frozen_tx_landing` lifted through
`streamsNext_eq` (mode/input agreement) and `streamAt_activeStep`.

**Not yet done (next round, (4)):** `StreamRelX` preservation as a single step
lemma.  Its cases are: the two frozen-landing producers above (done), the frozen
no-landing case (`LD`/slots held), and the unfrozen cases (where `hok` is free
from `streamRelX_hok` and the post-state content comes back from
`BufRel` + `ShapeOK` for the `WV`-valid half and from the landing event for the
`WV`-empty half).  Only then can `StreamWire` be restated to
`mode` + `input` + `held` and the three stream fields (`streamHostctl`,
`streamLanding`, `streamBufrel`) be removed.

## Round 10c: `contentsWb` CLOSED via A2's `CapTrace.lean`

`Discharge/CapTrace.lean` (A2) provides `CapInv` (mode-indexed `CapModeOK`),
`capInv_reset`, `capInv_step_active/_reset/_of_input`, `capInv_trace`,
`contentsWb_of_capInv` and `contents_open_req_cap`.  `Assembly.lean` imports it
and closes the residual:

1. `premises_of` takes `(hcap : Discharge.CapInv s m)` and calls
   `contents_open_req_cap … hcap` instead of `contents_open_req_wb …
   hopen.contentsWb`;
2. `chip_step_refines'` threads `hcap`;
3. the per-cycle `StreamInputAgree` block was extracted from `premises_of` into
   **`streamInputAgree_of`** (same proof, now parameterised by `hrel`, `hinv`,
   `hls`, `hexp`, `hact`), plus a wrapper `capInv_step_of_premises` that
   case-splits on `runRst` (`capInv_step_active` with the agreement,
   `capInv_step_reset` without), so no `hact` is needed at every cycle;
4. `trace_refines'_capInv` proves `ChipRel … ∧ CapInv …` by induction from
   `⟨rel_reset, capInv_reset⟩`; `trace_refines'` is its `.1` projection (the
   headline statement is unchanged);
5. `OpenWiring.contentsWb` and its docstring are deleted.

`CapModeOK` is *not* derivable from `ChipRel`/`AbsRelB` alone (the mode-2 `PV`
clause needs `WB` under `PV`, which `BufRel` only gives under `WV`), so the
strengthened trace induction is genuinely required.

**Counts:** `OpenWiring` **4** — `dbgReal`, `streamHostctl`, `streamLanding`,
`streamBufrel`.

## Round 9b: `dbgHwb` closed

W6's guarded pair is plugged in:

* `DbgMapWire.dbg_wb_of_wv` proves the slot fact from `ChipRel.streams 0` +
  `BufRel.wb_of_wv` (no hypothesis);
* `DbgMapWire.dbgRlvValue_of_wv` takes only that `WV`-guarded fact (plus the
  proved `happly`), so `dbgRlvValue` is filled without an unguarded `hwb`.

`DbgWire.hwb` and `OpenWiring.dbgHwb` are **deleted** (`premise_dbg` no longer
reads either: the `dbg_step_bridge` call was replaced by per-field bridges in
round 6b).

**Counts:** `OpenWiring` **5** — `contentsWb`, `dbgReal`, `streamHostctl`,
`streamLanding`, `streamBufrel`.  `DbgWire` is down to 9 fields, of which only
`real` (the carried frozen-`RLVP` deviation) is unproved.

Pending: A2's `Discharge/CapTrace.lean` (relational `CapInv` reset/step +
`contentsWb_of_capInv`) plugs into `contentsWb` when it lands; (3)/(4) unchanged
(`StreamRelX` form recorded in the round-9 section).

---


Status: **`lake build Metronome.ChipCut.Assembly` exits 0** with the lakefile's
`-DwarningAsError=true` (76 jobs); axioms driver exit 0, no `sorryAx`, no
`native_decide`, no `Lean.trustCompiler`, no warnings.  `src/` untouched.

| file | SHA-256 | bytes |
|---|---|---|
| `Assembly.lean` | `AF740FB58BBD29D176D73B5E7347BDE0AA578C2F7208DF3575D92A6097791BDA` | 35924 |

## Round 9 — (2) SPLICED: the mode-indexed shape invariant

`Assembly.lean` now carries (and `Bridge.StreamBuf` is imported):

```lean
def streamShapeInv (s : State) : Prop :=
  ∀ k : Fin 2, Bridge.StreamBuf.ShapeModeOK (stateMode s k) (streamAt s k.val)

theorem streamShapeInv_reset (cont : Contents) : streamShapeInv (resetState cont)
theorem streamShapeInv_step (s) (pin) (h : streamShapeInv s)
    (hq : stream_mode_quiet s pin) : streamShapeInv (step s pin)
theorem streamShapeInv_trace (pins) (cont)
    (hq : ∀ n, stream_mode_quiet (cutStateAt … n) (pins n)) : ∀ n, streamShapeInv (…)
```

with the four supporting facts `stateMode_eq_modeOf`
(`stateMode s k = modeOf (k.val == 0) (streamIn s pin k)`),
`stateMode_cap_false` (`CAP = 0` ⇒ mode 0 or 1), `streamAt_activeStep`
(`streamAt (activeStep s pin) k = Stream.step (k.val == 0) …`) and
`nv_step_zero` (`ld = nv = false ⇒ NV' = false`; `nvNext`'s only `true` branch
needs `s.ld`).

Step structure per stream `k`: on a **mode change** the strengthened
`stream_mode_quiet` clears `LD/RQ/WV/NV/PV`, so the stream is idle — `ShapeOK`
comes from B1's `shapeModeOK_step`/`shapeOK_step_cap_false` and the mode-indexed
clause is vacuous by `NV' = 0`; with **no mode change** the goal's mode is the
step's `modeOf` argument and `shapeModeOK_step` applies directly.  `CAP = 0`
uses `nv_step_cap_false` + `shapeOK_step_cap_false`, with `s.nv = false` derived
from `ShapeModeOK` + `stateMode_cap_false` (mode 1 is impossible with `NV = 1`).

Not landed: **(3)** and **(4)**.  (3)'s state-level form is now pinned down:
`StreamRelX s m := ∀ k, (streamAt s k).ld = true →
  (s.freeze.frzd = false ∨
   (stateMode s k = 0 ∧ (streamAt s k).wb = m.streams[k].wb) ∨
   (stateMode s k = 3 ∧ Bridge.StreamBuf.HeldLanding (streamAt s k) m.streams[k]))`
(the `HeldOK` disjunction with the cut's `frzd`/mode in place of the input
record); preservation needs `heldLanding_frozen_landing`/`wb_frozen_tx_landing`
for the frozen landing and the unfrozen `LD`-consumption case.  (4) then uses
`streamShapeInv` for `hshape`, `ldModeInv` for `hldmode` and `StreamRelX` for
`hok`.

---


Status: **`lake build Metronome.ChipCut.Assembly` exits 0** (75 jobs, 0.4 s
cached).  No source file changed in round 8: items (2)-(4) were **not** spliced;
the tree is exactly the round-7 state (green, `OpenWiring` 6).

## Round 8 — (2)/(3)/(4) NOT landed: verified design and blockers

**Addition (b) landed**: `stream_mode_quiet` extended once more (orchestrator
decision 2026-11-22c) — on a mode-change cycle it also requires
`(streamAt s k).pv = false` **and** `(streamAt (step s pin) k).pv = false`:

```lean
def stream_mode_quiet (s : State) (pin : Machine.PinIn) : Prop :=
  ∀ k : Fin 2,
    stateMode (step s pin) k ≠ stateMode s k →
      (streamAt s k.val).ld = false ∧ (streamAt s k.val).rq = false ∧
        (streamAt s k.val).wv = false ∧ (streamAt s k.val).nv = false ∧
        (streamAt s k.val).pv = false ∧ (streamAt (step s pin) k.val).pv = false
```

The docstring records the B1 finding (`Bridge.StreamBuf.capWb_reachable_witness`:
a receive→capture switch with a pending byte makes the capture `WB` diverge) and
that "a stream's mode may only change while it is completely idle" is stricter
than SPEC §9a.13.  `ldModeInv_step` projects the first two conjuncts.

**Addition (a) deferred**: restating `DbgWire.hwb`/`OpenWiring.dbgHwb` to the
`WV`-guarded form is safe at the field level (`Bridge.StreamBuf.dbgHwb_of_wv`
supplies it from `AbsRelB`), but its consumer `DbgMapWire.dbgRlvValue_of` takes
the **unconditional** `hwb`, so in the current API the guard merely moves the
open fact from `dbgHwb` to `dbgRlvValue`.  The restatement should be done
together with W6's guarded `dbgRlvValue_of_wv` (same proof, guarded `wb` read
under `replayValid = RPL && WV`), which is the clean form B1 describes.

The round was otherwise spent on the (2) draft and on a dependency stall: B1's
`Bridge.StreamBuf` olean was momentarily absent (round-3 edit in progress), so
the module had to be rebuilt (126 s) before any scratch could be checked.

The (2) draft (`data/raw/lean_chipcut_assembly_v4_20261122/scratch_shape.lean`)
contains the full skeleton and the two new facts it needs, both of which compile
individually:

```lean
theorem stateMode_eq_modeOf (s) (pin) (k) :
    stateMode s k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val)
theorem stateMode_cap_false (s) (pin) (k) (hk : (k.val == 0) = false) :
    stateMode s k = 0 ∨ stateMode s k = 1
theorem streamAt_activeStep (s) (pin) (k) :
    streamAt (activeStep s pin) k.val =
      Stream.step (k.val == 0) (streamAt s k.val) (streamIn s pin k.val)
theorem nv_step_zero (s) (i) (hld : s.ld = false) (hnv : s.nv = false) :
    (Stream.step true s i).nv = false          -- nvNext's only `true` branch needs `s.ld`
def streamShapeInv (s : State) : Prop :=
  ∀ k, Bridge.StreamBuf.ShapeModeOK (stateMode s k) (streamAt s k.val)
```

Remaining proof work for (2) (the scratch has the case split, 7 goals open):

* k = 0, no mode change: `shapeModeOK_step` + `stateMode_eq_modeOf` (the `rwa`
  needs the goal's `modeOf (k.val == 0)` literal aligned with `true`).
* k = 0, mode change: `shapeModeOK_step` with `Or.inr ⟨hwv, hnv⟩` from the
  strengthened quietness; the `NV' = 0` clause is `nv_step_zero`.
* k = 1 (CAP = 0): `shapeOK_step_cap_false` + `nv_step_cap_false`; the "no mode
  change" branch needs `s.nv = false` from `ShapeModeOK` + `stateMode_cap_false`
  (`NV = 1` would force mode 3, impossible for CAP = 0).
* reset branch: `streamAt_resetChip`/`resetState` + `shapeModeOK_reset`.

(3) is approved in the conditional form `StreamRelX s m := ∀ k, ld → HeldOK …`;
(4)'s split (frozen ← `frozen_rel_landing_flush` with `hslot`/`hshape`/
`hldmode`; unfrozen ← `bufRel_step_unfrozen_guarded` with `hok` from (3)) is
approved as previously recorded.  Both need (2) first (the `ShapeOK`/`hshape`
component comes from `streamShapeInv`).

---


Status: **`lake build Metronome.ChipCut.Assembly` exits 0** with the lakefile's
`-DwarningAsError=true` (Lean 4.35.0, core libraries only); axioms driver exit 0,
no `sorryAx`, no `native_decide`, no `Lean.trustCompiler`, no warnings.  `src/`
untouched.

| file | SHA-256 | bytes |
|---|---|---|
| `Discharge/CoreCombWire.lean` | `BBA14DABADB5E97545F8089324AB11E7F0C05996B82A8215614D7A07ADB68435` | 130175 |

## Round 7 — landed: the strengthened mode-quiet premise (item 1)

`stream_mode_quiet` (`CoreCombWire.lean`) is strengthened per the orchestrator
decision of 2026-11-22b:

```lean
def stream_mode_quiet (s : State) (pin : Machine.PinIn) : Prop :=
  ∀ k : Fin 2,
    stateMode (step s pin) k ≠ stateMode s k →
      (streamAt s k.val).ld = false ∧ (streamAt s k.val).rq = false ∧
        (streamAt s k.val).wv = false ∧ (streamAt s k.val).nv = false
```

The docstring records that the `WV`/`NV` half is **stricter than SPEC §9a.13**
and is the assumption B1's `ShapeModeOK` needs (`BRIDGE_STREAMBUF_NOTES.md` §9:
a mode change while a replay-buffer slot is live is excluded).  The only consumer
that destructured the premise was `ldModeInv_step`; it now takes the first two
conjuncts, and `ldModeInv_trace` / `landingStream_trace` /
`stream_landNow_ld_trace` are unchanged (verified: the full chain rebuilds,
13.2 s; `Assembly` full elaboration 204.8 s).

## Round 7 — NOT landed: items 2-5 (exact state and next steps)

* **`ShapeModeOK` chip-level trace (item 2).**  `Bridge.StreamBuf` imports only
  `Metronome.Bridge.Stream`, so `CoreCombWire` can import it.  The plan:
  `streamShapeInv s := ∀ k, StreamBuf.ShapeModeOK (stateMode s k) (streamAt s k.val)`;
  reset from `shapeModeOK_reset`; step from `shapeModeOK_step` with
  `hchange := Or.inl (stateMode_branch)` in the no-change case and
  `Or.inr ⟨hwv, hnv⟩` from the strengthened `stream_mode_quiet` otherwise.
  **Subtlety found:** `shapeModeOK_step` concludes at mode `modeOf cap i`
  (= the *current* `stateMode s k`), while the chip-level invariant at the next
  state wants `stateMode (step s pin) k`; these differ exactly when the mode
  changed, and in that case one must show `NV' = 0` (from
  `StreamBuf.nv_step_true_or` and `wv = nv = 0`) so the mode-indexed clause is
  vacuous.  Needs ~50 lines in `CoreCombWire` plus the two `nv'` facts.
* **Relational held-landing invariant (item 3).**  `Bridge.StreamBuf` provides
  `HeldLanding`, `HeldOK`, `heldLanding_frozen_landing`,
  `wb_frozen_tx_landing`.  `HeldLanding` is *not* preserved unconditionally by
  the step (a consumed pending word leaves a stale `NB`; §10's `bufRelX_step`
  needs `hslot`/`hfresh`), so a `StreamRelX` carried alongside `ChipRel` has to
  be the *conditional* form (`LD → HeldOK` at the cycle where the landing
  happens, or a `HeldLanding` guarded by `WV`/`NV`), not a blanket state
  relation.  This is the main design question for the next pass; it is why
  items 3 and 4 are entangled.
* **`streamBufrel`/`streamHostctl`/`streamLanding` via `buf_step` (item 4).**
  `buf_step` covers unfrozen (fresh *and* held landing), frozen (with/without a
  host rewind), any flush and all modes, but needs
  `hside : adv = rxWe = capPush = replayLate = false` — i.e. **no stream inputs
  at all** — so it cannot be the single bridge for an arbitrary cycle.  The
  workable route is: frozen branch ← `frozen_rel_landing_flush`
  (`hslot`/`hshape`/`hldmode`, dropping `landing`/`hostctl`), unfrozen branch ←
  `bufRel_step_unfrozen_guarded` (needs `hok`, i.e. item 3).  That restates
  `StreamWire` to `mode` + `input` + `held` and re-proves
  `streams_field_0/1` (two 60-line proofs) — not attempted this round.
* **`contentsWb`, `dbgHwb`** — left for B1 round 3, as instructed.

`OpenWiring` is unchanged at **6** (`contentsWb`, `dbgReal`, `dbgHwb`,
`streamHostctl`, `streamLanding`, `streamBufrel`); the final theorem statement is
unchanged (`trace_refines'` over `ChipRel`/`Premises`).

---


Status: **`lake build Metronome.ChipCut.Assembly` exits 0** with the lakefile's
`-DwarningAsError=true` (Lean 4.35.0, core libraries only, 75 jobs); axioms
driver exit 0, no `sorryAx`, no `native_decide`, no `Lean.trustCompiler`, no
warnings.  `src/` untouched.

| file | SHA-256 | bytes |
|---|---|---|
| `Assembly.lean` | `58ADB0820E55232B39271F35A89E871658D8EBEDC407C65948A7AF3109D9032D` | 29617 |

## Round 6c: `dbgHmctl` / `dbgHectl` plugged in

W6's round-1 theorems `DbgMapWire.dbgHmctl` and `DbgMapWire.dbgHectl`
(hypotheses `ChipRel`/`Inv`/`runRst`) have exactly the two `OpenWiring`
statements, so they are passed verbatim; no adapter was needed.

**Counts:** `OpenWiring` **6** fields — `contentsWb`, `dbgReal`, `dbgHwb`,
`streamHostctl`, `streamLanding`, `streamBufrel`.  `DbgWire` is now down to
`real` + `hdbg` + `hmctl` + `hectl` + the two `EMASK`/`RLV` value fields + `hwb`
+ `hword` + `happly` + `hcev`, of which only `real` and `hwb` are unproved.

## Remaining `OpenWiring` (6) and owners

| field(s) | owner / blocker |
|---|---|
| `dbgHwb`, `contentsWb`, `streamBufrel`, `streamHostctl` | B1 (`StreamBuf`, frozen bridge incl. the flush generalisation) |
| `streamLanding` | B1: **false** (witness `Discharge.streamWire_landing_false`); the frozen bridge must cover `LD ∧ !FRZD` |
| `dbgReal` | carried frozen-`RLVP` deviation (the only permanent one) |

---


Status: **`lake build Metronome.ChipCut.Assembly` exits 0** with the lakefile's
`-DwarningAsError=true` (Lean 4.35.0, core libraries only, 75 jobs); axioms
driver exit 0, no `sorryAx`, no `native_decide`, no `Lean.trustCompiler`, no
warnings.  `src/` untouched.

| file | SHA-256 | bytes |
|---|---|---|
| `Assembly.lean` | `1D5309A4DA54778D8922A0726500EB62D40B8B54C11C6B65D1569075F78AB594` | 29945 |
| `Discharge/StreamDbg.lean` | `C66C83D52B665568D1A77ABA211370939A8CC7FDD7173B5B7139EC7B6571264D` | 58063 |

## Round 6b: W6 plugged in (`DbgMapWire`)

`DbgWire` lost its eight per-port `EMASK`/`RLV` host/drain byte leaves
(`hEH`, `hEC`, `hESH`, `hESC`, `hRH`, `hRC`, `hRSH`, `hRSC`) and gained two
register-value fields (W6's proposal, `WIRE_DBGMAP_NOTES.md` §3):

```lean
dbgEmaskValue : (machDbgNext m).emask = (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).emask
dbgRlvValue   : (machDbgNext m).rlv   = (Debug.Ctrl.step s.dbgCtrl (dbgCtrlIn s pin)).rlv
```

`premise_dbg` is re-proved: the `EMASK`/`RLV` bullets are now the two value
fields verbatim, and the other eight `DbgRel` fields are rebuilt from the
per-field bridges (`ectl_bridge` for `cen`/`rpl`, `dc_bridge`, `men_bridge`,
`misr_bridge`, `dbgNext_rlvp` + `rlvp_agree`) instead of one
`dbg_step_bridge` call — so the six host-byte hypotheses are gone from the
consumer as well.  The capstone fills the two new fields from
`DbgMapWire.dbgEmaskValue_of` and `DbgMapWire.dbgRlvValue_of` (the latter with
`hopen.dbgHwb` and the `happly` fact, now a named `have` used by both `DbgWire`
and the value field).

**Counts:** `OpenWiring` **8** fields — `contentsWb`, `dbgReal`, `dbgHmctl`,
`dbgHectl`, `dbgHwb`, `streamHostctl`, `streamLanding`, `streamBufrel`.  13
`Premises` fields have no residual; `streams` (3 leaves), `dbg` (4 leaves) and
`contents` (1) carry the rest.

## Remaining `OpenWiring` (8) and owners

| field(s) | owner / blocker |
|---|---|
| `dbgHmctl`, `dbgHectl` | clean-up: the two remaining `DBG` byte-interface leaves (W6's scope is complete for `EMASK`/`RLV`) |
| `dbgHwb`, `contentsWb`, `streamBufrel`, `streamHostctl` | B1 (`StreamBuf`, frozen bridge incl. the flush generalisation) |
| `streamLanding` | B1: **false** (witness `Discharge.streamWire_landing_false`); the frozen bridge must cover `LD ∧ !FRZD` |
| `dbgReal` | carried frozen-`RLVP` deviation (the only permanent one) |

---


Status: **`lake build Metronome.ChipCut.Assembly` exits 0** with the lakefile's
`-DwarningAsError=true` (Lean 4.35.0, core libraries only, 74 jobs); axioms
driver exit 0, no `sorryAx`, no `native_decide`, no `Lean.trustCompiler`, no
warnings.  `src/` untouched.

Edited this round: `Metronome/ChipCut/Assembly.lean` only (plus this note and
the evidence directory).

| file | SHA-256 | bytes |
|---|---|---|
| `Assembly.lean` | `172F50A7BAC6645124FAE85838DCF2413B9251D27E8BFAF7F1DE6B203776A9BE` | 30569 |

## Round 6a: W5 plugged in (`MovePayloadWire`)

`ExplicitPremises` gained

```lean
dstFlagP0Cw : Discharge.MovePayloadWire.DstFlagP0CwTable
```

(the checked `FLAGS`/`P0`/`CW` code table: 64 codes × 11 rows, compiled
evaluation 0 failures, `WIRE_MOVEPAYLOAD_NOTES.md` §2), and five `OpenWiring`
fields are now theorems:

| field | supplied by |
|---|---|
| `unitFlagPQ` | `MovePayloadWire.unitFlagPQ` (+ `MoveFabric.unitInputs_flag_low4`) |
| `p0Move` | `MovePayloadWire.p0Move` |
| `cwMove` | `MovePayloadWire.cwMove` |
| `ctrlMemhaz` | `MovePayloadWire.ctrlMemhaz` (+ `hexp.srcTable`, `p0_open_served`) |
| `ctrlCwovr` | `MovePayloadWire.ctrlCwovr` |

`ctrlMemhaz`'s `hserved` argument is the existing `Discharge.p0_open_served`
(definitionally the `machineServed` form; `WIRE_MOVEPAYLOAD_NOTES.md` §6 checked
it).

**Counts:** `OpenWiring` **14** fields — `contentsWb`, `dbgReal`, 8 `DBG`-map
leaves (`dbgHmctl`, `dbgHectl`, `dbgHEH`, `dbgHEC`, `dbgHESH`, `dbgHRH`,
`dbgHRC`, `dbgHRSH`), `dbgHwb`, `streamHostctl`, `streamLanding`,
`streamBufrel`.  Of the 16 `Premises` fields, **13 have no residual at all**
(`sync`, `lines`, `threads`, `cores`, `units`, `host`, `hostReq`, `p0`, `ctrl`,
`cw`, `bank`, `out`, `oen`) and 3 have residual facts (`streams` ← 3 stream
leaves, `dbg` ← 10 leaves, `contents` ← `contentsWb`).

## Remaining `OpenWiring` (14) and owners

| field(s) | owner / blocker |
|---|---|
| 8 `DBG`-map leaves (`dbgHmctl` … `dbgHRSH`) | W6 (`DbgMapWire`) |
| `dbgHwb`, `contentsWb`, `streamBufrel`, `streamHostctl` | B1 (`StreamBuf` / frozen bridge, incl. the flush generalisation) |
| `streamLanding` | B1: **false** (witness `Discharge.streamWire_landing_false`); the frozen bridge must cover `LD ∧ !FRZD`, then the field goes |
| `dbgReal` | carried frozen-`RLVP` deviation (the only permanent one) |

---


Status: **`lake build Metronome.ChipCut.Assembly` exits 0** with the lakefile's
`-DwarningAsError=true` (Lean 4.35.0, core libraries only, 73 jobs); axioms
driver exit 0, no `sorryAx`, no `native_decide`, no `Lean.trustCompiler`, no
warnings.  `src/` untouched.

Edited this round: `Discharge/StreamDbg.lean` and `Metronome/ChipCut/Assembly.lean`.

| file | SHA-256 | bytes |
|---|---|---|
| `Assembly.lean` | `7C2BEDDC9536A2A5A8CF201FB86E89F7435DCF6B35EFDFA3F186E3B29CB42F3E` | 30894 |
| `Discharge/StreamDbg.lean` | `4EAEFDA52455714AF84F619499EA5493D8F2E0D71B27F4271EF13F5B0370DBF7` | 57790 |

## Round 5: `streamInput` closed

`StreamWire.input` is restated from the false exact record equality to the
13-field **`StreamInputAgree`** (the quantities `Machine.streamNext` reads), and
the capstone builds the agreement:

1. **`StreamInputAgree`** (StreamDbg): `adv`, `rxSome`, `rxBit`, `rewind`,
   `flush` (guarded by `¬frz`), `clr`, `served`, `landNow` (guarded by
   `m.streams[k].ld`), `ramOut`, `cev`, `record`, `apply`, `late` — all stated
   against `absInOf`.
2. **`streamsNext_eq`** re-proved through `streamNext_congr` (the round-4
   congruence) and `streamNext_gate_irrel` for stream 1; `streams_field_0/1` are
   unchanged (they only pass `hw.input k`).
3. **LD adapter** `stream_ld_eq` (`AbsRelB`'s `LD` clause) so the `landNow` guard
   in `m.streams[k].ld` transfers to the cut's `LD` for `stream_landNow_ld`.
4. **`rx` bridge** `rx_agree_of_mod2` + `option_isSome_map`,
   `option_getD_map_mod2`, `nbit_mod2_zero`, `option_map_mod2_self`,
   `absInOf_rx_lt` (the bridge's `Sk.RX` value is a bit).
5. **Assembly** builds `hIn : ∀ k, StreamInputAgree …` from
   `MoveFabricKeyed.streams_adv`, `StreamMoveWire.streams_rx_low1`,
   `streams_ctl_combined'`, `CoreCombWire.stream_served`,
   `stream_landNow_ld` + `stream_ld_eq`, `hrel.ramOut`, and
   `CoreCombCbs.stream_{cev,record,apply,late}_eq`; `OpenWiring` lost
   `streamInput`.

**Counts:** `OpenWiring` **19** fields — `unitFlagPQ`, `p0Move`, `cwMove`,
`ctrlMemhaz`, `ctrlCwovr`, `contentsWb`, `streamHostctl`, `streamLanding`,
`streamBufrel`, 10 `dbg*`.  10 `Premises` fields no-residual, 6 with residual
(`p0`, `streams`, `ctrl`, `dbg`, `cw`, `contents`), 0 carried whole.

## Round-5 failures fixed (for the record)

* `streams_adv` lives in namespace `Discharge.MoveFabricKeyed`, not `Discharge`.
* `rx_agree_of_mod2` first wanted both options in the `% 2` form;
  `streams_rx_low1` gives the *unmapped* right side, so the lemma takes
  `h : o1.map f = o2` plus `h2 : o2.map f = o2`, with `option_map_mod2_self` and
  `absInOf_rx_lt` supplying `h2` (`Sk.RX` values are 0/1).
* `absInOf`/`gatedIn` need the `Discharge.` prefix in `Assembly` (no `open`), and
  the `rewind`/`flush`/`clr` simp sets must unfold `absInOf` + `gatedIn` before
  the `@[simp]` `nbit_ctl*`/`nbit_clr*` lemmas can fire.
* `nbit_mod2_zero`: plain `simp` (the explicit `Nat.mod_mod` was unused →
  warning-as-error).

## Remaining `OpenWiring` (19) and owners

| field(s) | owner / blocker |
|---|---|
| `unitFlagPQ`, `p0Move`, `cwMove`, `ctrlMemhaz`, `ctrlCwovr` | W5 (`MovePayloadWire`) |
| 8 `DBG`-map leaves (`dbgHmctl`…`dbgHRSH`) | W6 (`DbgMapWire`) |
| `dbgHwb`, `contentsWb`, `streamBufrel`, `streamHostctl` | B1 (`StreamBuf` / frozen bridge) |
| `streamLanding` | B1: **false** (witness `streamWire_landing_false`); the frozen bridge must cover `LD ∧ !FRZD` and then the field goes |
| `dbgReal` | carried frozen-`RLVP` deviation (the only permanent one) |

---

## Round 4 (for reference)

Status: **`lake build Metronome.ChipCut.Assembly` exits 0** with the lakefile's
`-DwarningAsError=true` (Lean 4.35.0, core libraries only, 73 jobs); axioms
driver exit 0, no `sorryAx`, no `native_decide`, no `Lean.trustCompiler`, no
warnings.  `src/` untouched.

Edited this round: `Discharge/StreamDbg.lean` only (plus these notes and the
evidence directory).  `Assembly.lean`, `LineThread.lean`, `MemHostCfg.lean` are
unchanged from round 3.

| file | SHA-256 | bytes |
|---|---|---|
| `Assembly.lean` | `050225C46613E140D5B81C6B35C495D5941B630C1CD06BB1FF1ED640777E0EA6` | 26482 |
| `Discharge/StreamDbg.lean` | `CB1C191E8977DB2985A46920FA18072F89F1CD467FE8355BBC382F39AAA29FC1` | 54875 |
| `Discharge/LineThread.lean` | `3F149362206B4D6EDDACE1B32362DB921C2D8239BD64395D52E94A0C0A1B875D` | 39350 |
| `Discharge/MemHostCfg.lean` | `32289E9216331F9D56E910AAFD176497C24A810E0B5F846ABABD04AF2FBC3653` | 72079 |

## Round 4

### 4.1 `streamNext_congr` (proved)

`Machine.streamNext` reads its `StreamIn` only through: `adv`; `rx.isSome` and
`nbit (rx.getD 0) 0`; `nbit ctlMove 0` and `nbit hCtl 0` (rewind); `nbit ctlMove
1` and `nbit hCtl 1` (flush, only unfrozen); `nbit hCtl 7` (clr); `served`;
`landNow` (only while `LD`); `ramOut`; `cev`; `record`; `apply`; `late`.  It
never reads the full `rx` byte or `ctlMove` bits beyond 0/1 — **no real
mismatch**.  The congruence is proved as

```lean
theorem streamNext_congr (c) (mode) (st) (i1 i2 : StreamIn) (frz)
  (hadv) (hrxSome) (hrxBit) (hserved) (hland : st.ld = true → i1.landNow = i2.landNow)
  (hram) (hcev) (hrec) (happly) (hlate) (hrew) (hflush : frz = false → …) (hclr) :
  Machine.streamNext c mode st i1 frz = Machine.streamNext c mode st i2 frz
```

by `by_cases` on `st.ld` and `frz`, `unfold Machine.streamNext
Machine.Util.streamAuto`, the field rewrites, and a closing `simp`.

**Not landed: the `StreamWire.input` restatement.**  It is a two-part
mechanical step that needs one detail checked first:

1. a `StreamInputAgree` structure (13 fields, exactly the hypothesis list
   above), and
2. `streamsNext_eq`/`streams_field_0`/`streams_field_1` re-proved through
   `streamNext_congr` instead of `hin : machStreamIn = absInOf`.

The `landNow` guard of `streamNext_congr` is on `m.streams[k].ld` (the machine
register passed to `streamNext`), while the discharge `stream_landNow_ld`
provides the fact under the *cut's* `LD`; the bridge needs
`(m.streams[k].ld = true) ↔ ((streamAt s k.val).ld = true)` (`AbsRelB`'s `LD`
clause) as an adapter.  Everything else is directly available:
`MoveFabricKeyed.streams_adv`, `StreamMoveWire.streams_rx_low1`,
`streams_ctl_combined'`, `CoreCombWire.stream_served`, `stream_landNow_ld`,
`CoreCombCbs.stream_cev_eq`/`stream_record_eq`/`stream_apply_eq`/`stream_late_eq`.

### 4.2 `StreamWire.landing` is **false** (witness proved)

`StreamWire.landing` (`LD = true → FRZD = true`) is not an invariant.
`Stream.ldNext` holds `LD` in a frozen cycle (`if i.frz then s.ld`) and `FRZD`
is the *previous* cycle's `FRZ` (`CoreCtl.freezeStep`), so **a host freeze one
cycle after a served read** gives `LD = 1, FRZD = 0`.  Constructive witness in
`StreamDbg.lean`:

```lean
theorem sz_rq     : (Stream.step true Stream.resetState szIn₀).rq = true
theorem sz_ld     : (Stream.step true (… sz_rq …) szIn₁).ld = true
theorem sz_ld_frz : (Stream.step true (… sz_ld …) szInFrz).ld = true       -- frozen holds LD
theorem sz_freeze : CoreCtl.freezeStep ⟨false,false,false⟩
  {resetN := true, dbgWrite := true, data := 1} = ⟨true,true,false⟩        -- FRZ = 1, FRZD = 0
theorem streamWire_landing_false (cont) :
  ∃ s pin, (streamAt s 0).ld = true ∧ (streamIn s pin 0).frzd = false
```

so `streamLanding` **stays in `OpenWiring`**, and it is *not* a cut-wiring bug:
the corner is benign (both readings store the RAM word in `WB`; the notes'
§3.1), but the frozen bridge (`frozen_rel`/`abs_step_frozen`) has to be extended
to cover `LD ∧ !FRZD`.  `StreamWire.landing`'s docstring could then be dropped
together with the bridge change.

## Counts (unchanged by round 4)

10 fields no-residual / 6 with residual / 0 whole; `OpenWiring` 20 fields
(`unitFlagPQ`, `p0Move`, `cwMove`, `ctrlMemhaz`, `ctrlCwovr`, `contentsWb`,
`streamInput`, `streamHostctl`, `streamLanding`, `streamBufrel`, 10 `dbg*`).

## Next pass

1. `streamInput` (§4.1): add `StreamInputAgree` + the `AbsRelB` `LD` adapter,
   re-prove `streamsNext_eq`/`streams_field_*`, then build the agreement in
   `Assembly` from `streams_adv`/`streams_rx_low1`/`streams_ctl_combined'` + the
   five exact facts.  This removes `streamInput`.
2. `streamLanding`: with the bridge extended to `LD ∧ !FRZD` (B1's frozen work),
   drop the field; until then it stays with the witness above.
3. W5/W6/B1 results: plug in the remaining payload rows, `DBG`-map leaves,
   `dbgHwb`, `contentsWb`, `streamBufrel`.

---

## Round 3 (for reference)

Status: **`lake build Metronome.ChipCut.Assembly` exits 0** with the lakefile's
`-DwarningAsError=true` (Lean 4.35.0, core libraries only, 73 jobs, 0.4 s when
up to date / 4.2 s full module elaboration); axioms driver exit 0 (2.6 s), no
`sorryAx`, no `native_decide`, no `Lean.trustCompiler`, no warnings.  `src/`
untouched (`git diff --quiet HEAD -- src` exit 0).

Edited this round: `Metronome/ChipCut/Assembly.lean`,
`Discharge/LineThread.lean`, `Discharge/MemHostCfg.lean`.  (`Discharge/CoreUnits.lean`
is unchanged from round 2.)  Nothing outside these, the notes and the evidence
directory.

| file | SHA-256 | bytes |
|---|---|---|
| `Assembly.lean` | `050225C46613E140D5B81C6B35C495D5941B630C1CD06BB1FF1ED640777E0EA6` | 26482 |
| `Discharge/LineThread.lean` | `3F149362206B4D6EDDACE1B32362DB921C2D8239BD64395D52E94A0C0A1B875D` | 39350 |
| `Discharge/MemHostCfg.lean` | `32289E9216331F9D56E910AAFD176497C24A810E0B5F846ABABD04AF2FBC3653` | 72079 |

---

## 0. Counts

| of the 16 `Premises` fields | r1 | r2 | **r3** |
|---|---|---|---|
| no residual at all | 5 | 8 | **10** |
| from residual facts | 7 | 5 | **6** |
| carried whole | 4 | 3 | **0** |

**Every one of the 16 fields is now produced by a `Discharge.premise_*`
theorem.**  `OpenWiring` is 20 fields: `unitFlagPQ`, `p0Move`, `contentsWb`,
`cwMove`, `ctrlMemhaz`, `ctrlCwovr`, `streamInput`, `streamHostctl`,
`streamLanding`, `streamBufrel`, and the 10 `dbg*` leaves
(`dbgReal`, `dbgHmctl`, `dbgHectl`, `dbgHEH`, `dbgHEC`, `dbgHESH`, `dbgHRH`,
`dbgHRC`, `dbgHRSH`, `dbgHwb`).

## 1. What round 3 landed

**(1) `dbgHapply` proved and removed.**  The orchestrator's `Wire.lean` fix
(`replayValid = s1 ++ s0`, bit 0 = S0) makes the machine's apply agree with the
cut's decode.  Proof: `CoreCombCbs.stream_apply_eq` at `k = 0` plus
`bitAt_replayValid` (`Debug.bitAt (dbgCtrlIn …).replayValid 0 = (streamAt s 0).wv`,
by case split on the two `WV` bits).  `DbgWire` is now built with
`happly` proved, so the 7th wiring bug is closed end to end.

**(2) `lines` / `threads` closed** (`Discharge/LineThread.lean`).

* `WireAgree.sym`/`.ctl` are restated to the **projected** forms
  (`(op, v % 16)`, `v % 8`) that `LineMoveWire.wireAgree_sym_low4` /
  `wireAgree_ctl_low3` prove.  Consumer check (done): `Machine.lineNext` reads
  `sym` only through `stagedNext` (`bv 4 v` for SET, `v % 2` for DBIT/XOR) and
  `ctlMove` only through `nbit v 0..2`; `hPhase`/`hCtl`/`hTapmissClr` stay
  exact.  **No consumer needs the full byte.**
* New: `lineInTrunc` (the projected record), **`lineNext_trunc`** (the
  record-level wrapper: the `let`-chain congruence, proved by `obtain` +
  `cases sy <;> cases ct` + `simp only [Machine.lineNext, lineInTrunc,
  nbit_mod8_0/1/2, Option.map_none/some, stagedNext_mod16_some] <;> rfl`), and
  `lineIn_proj_eq` (the projected record is `Bridge.Line.absIn` of the cut
  input, via `Option.map_map` and the pair/record round trip).
* `premise_lines` now rewrites the *machine's own* `lineNext` by
  `lineNext_trunc` (`conv => lhs; rw`) and then by `lineIn_proj_eq`, instead of
  the false exact `lineIn_eq` (deleted).
* Consequence: the whole `WireAgree` bundle is now constructible in the
  capstone from `HostPinWire.wire_*`, `LineMoveWire.wireAgree_*_low*`,
  `MoveFabricKeyed.wireAgree_late/stop`, `CoreCombWire.ccw_dispatch/pause` and
  `ccw_pauseDisp_cut`, so `lines` and `threads` are **`premise_lines` /
  `premise_threads` with no residual**.

**(3) `p0Lane` removed: the guarded lane** (`Discharge/MemHostCfg.lean`).
`Machine.p0Next` reads the lane only in `d' := if landNow then … else p.d`, and
`landNow` is exactly `land && !FRZD` — the `laneInv` guard.  New
`p0Next_lane_irrel` (`landNow = false → p0Next … l1 … = p0Next … l2 …`);
`premise_p0`'s lane hypothesis is now the guarded
`land → frzd = false → ramLane = landLane`, discharged by
`Discharge.laneInv s` (which `premises_of` already receives).  The proof splits
on `landNow`: true → `ChipRel.ramLane` + the guard, false → the irrel lemma.

**(4) `contents` reduced to one capture-buffer fact.**  `premise_contents`'s
`contents_open_cbs` is false (whole `CoreComb` bundle), so the capstone now uses
a new `premise_contents_proj` (in `Assembly.lean`: the body of
`premise_contents` with its `mout` bullet replaced by
`CoreCombCbs.contents_mout_of_fetch`).  It takes the per-core `fetch`
congruence — supplied from `CoreCombCbs.contents_open_proj_abs`'s fifth
component — plus `contents_open_req_wb` (with a named `contentsWb : PV → WB`)
and `contents_open_served`.  `OpenWiring.contents : ContentsEq` became
`OpenWiring.contentsWb : ∀ k, pv → m.streams[k].wb = (streamAt s k).wb`
(B1's `Bridge/StreamBuf.lean`).

## 2. Remaining `OpenWiring` and its exact owner/blocker

| field | feeds | blocker / owner |
|---|---|---|
| `unitFlagPQ` | `units` | `FLAGS` payload row (codes 5/6) not in `DstPayloadTable.codeOf` — **W5** |
| `p0Move` | `p0` | `Fam.p0` payload row (`p0_open_move`'s `hPQ`) — **W5** |
| `cwMove` | `cw` | `Fam.cw` payload row — **W5** |
| `ctrlMemhaz` | `ctrl` | `P0.D`-read scan + pointer hazard — **W5** |
| `ctrlCwovr` | `ctrl` | machine `cwNext.ovr` vs the cut queue drop — **W5** |
| `dbgReal` | `dbg` | `DbgWire.real`: the frozen debug cycle diverges (`RLVP`) — carried deviation |
| `dbgHmctl`, `dbgHectl`, `dbgHEH`, `dbgHEC`, `dbgHESH`, `dbgHRH`, `dbgHRC`, `dbgHRSH` | `dbg` | host `DBG`-map byte geometry — **W6** |
| `dbgHwb` | `dbg` | first replay slot `WB`, only `BufRel`-guarded — **B1** |
| `contentsWb` | `contents` | capture buffer `PV → WB` — **B1** |
| `streamInput` | `streams` | `Sk.CTL` combined form + `rx % 2`; needs `StreamWire.input` restated and a `Machine.streamNext` congruence in the derived `rewind`/`flush`/`clrStarved` (round 3 did **not** land this) |
| `streamHostctl` | `streams` | no stream flush in a frozen cycle (glue: `SRT.CTL[1] = 0` while frozen) |
| `streamLanding` | `streams` | `LD → FRZD`; `LandingStream` alone does **not** imply it (it constrains `ramOwner`, not the cut's `frzd`), so this needs its own glue/Spec fact |
| `streamBufrel` | `streams` | the three recorded replay-buffer corners — **B1** |

## 3. Findings

* The `lineNext` wrapper is the only place the projected `L.SYM`/`Lk.CTL` data
  mattered: `Machine.lineNext` is invariant under the truncation, and the two
  ingredients (`stagedNext_mod16`, `ctlTriple_mod8`) had been proved in round 2;
  the missing piece was purely the record-level rewriting, now
  `lineNext_trunc`.
* `p0Next`'s lane argument is read **only** through the guarded landing write,
  so the unguarded consumer hypothesis was strictly stronger than needed — the
  `laneInv` form is exactly what `Mem.step`/`p0Next` consume.
* `contents`: no further hypothesis is needed beyond the projection, `mout`,
  `served` and `hwb`; `contents_open_req`'s `hwv` form is unsound (already known)
  and `contents_open_req_wb` is the sound one.

## 4. Round-3 failures fixed (for the record)

* `bitAt_replayValid` needed the bit-order lemma, and `simp` had to be kept from
  expanding `Debug.bitAt` before the lemma could fire (rewrite first, `simpa`
  second).
* `lineNext_trunc` by `unfold` + `rw` failed on the def's pattern-`let`
  (`let (a,b,c) := match …`); `{i with …}` nested inside a `fun` inside a
  structure update does not parse.  Fixed by a named `lineInTrunc` def,
  `obtain` + `cases` on the two option fields, `simp only [Machine.lineNext,
  lineInTrunc, …]` and a trailing `<;> rfl` (the two sides are only
  *definitionally* equal after the simp).
* `premise_p0`'s lane rewrite: unconditional `rw` is impossible under a guard;
  split on `landNow` and use `p0Next_lane_irrel` in the false branch.
* `premise_contents_proj`'s copied bullets: the `pmem` one needs a final `rfl`
  (the `rw` chain leaves a definitional, not syntactic, equality); the other
  four close by `rw` alone.

## 5. Next pass

1. **W5/W6/B1 results**: plug in `unitFlagPQ`, `p0Move`, `cwMove`, `ctrlMemhaz`,
   `ctrlCwovr`, the eight `DBG`-map leaves, `dbgHwb`, `contentsWb`,
   `streamBufrel` → `OpenWiring` drops to the four `stream*` fields + `dbgReal`.
2. `streamInput`: add a `Machine.streamNext` congruence in
   `(rewind, flush, clrStarved, advance/rx/capture/replay/land fields)`; restate
   `StreamWire.input` as "record matches `absInOf` except `ctlMove`/`hCtl`, and
   the derived control bits are the combined forms"; re-prove `streams_field_0/1`
   through it.  `streams_ctl_combined'`/`streams_rx_low1`/`streams_adv` supply
   the facts.
3. `streamLanding`: a dedicated glue fact (no host stream flush/freeze
   coincidence) — `LandingStream` is not enough.
4. `dbgReal`: keep as the carried frozen-`RLVP` deviation (the only field that
   should stay).

## 6. Reproduce

```powershell
cd code/tests/lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.LineThread      # exit 0
lake build Metronome.ChipCut.Discharge.MemHostCfg      # exit 0
lake build Metronome.ChipCut.Assembly                  # exit 0, 73 jobs
lake env lean -DwarningAsError=true Metronome/ChipCut/Assembly.lean
lake env lean -DwarningAsError=true ..\..\..\data\raw\lean_chipcut_assembly_v4_20261122\axioms.lean
lake env lean ..\..\..\data\raw\lean_chipcut_assembly_v4_20261122\statements.lean
```

Evidence: `data/raw/lean_chipcut_assembly_v4_20261122/` — `build.log`,
`lean_module.log` (empty = no warnings), `axioms.lean`/`axioms.txt` (11 theorems,
no `sorryAx`), `statements.lean`/`statements.txt`, `commands.log`,
`scratch_proj.lean`/`scratch_proj2.lean`/`scratch_proj3.lean` (the
`lineNext_trunc` attempts), `scratch_bits.lean` (the `replayValid` bit check),
`scratch_adapters.lean` (round-1 draft).

## Final integration after independent review

Lean 4.35.0, branch `metronome-v4.0`, working-tree base `b7b4068`.
The module build completed with warnings as errors and 80 jobs, exit 0
in 5.20 s. The statement and axiom drivers both exited 0. This is
verification of the Lean cut and machine models.

The trace refinement takes three groups of hypotheses.

- `Tables` supplies the eight global closed propositions `SrcTable`,
  `GuardTable`, `JGTable`, `DstKindTable`, `DstPayloadTable`,
  `DstFlagP0CwTable`, `DstPortTable`, and `DstStreamLineTable`.
  Compiled evaluation found zero failing rows in all eight. They remain
  explicit hypotheses of the refinement theorem.
- `InitialConditions cont` requires `cont.ramOwner = 0`,
  `MaskedZero cont.cfg`, and `cont.cfg.img.size = Machine.Util.cfgSize`.
- `PinPremises` supplies `host_sck_spacing` and `stream_mode_quiet` for each
  sample on the cut trace. A changing stream mode requires pre-step
  LD, RQ, NV and PV to be low and post-step PV to be low. WV is allowed.

`cw_window_ok` uses `windowQuiet_trace` while the release window is open.
`grpPacked_holds` and `cwH19_trace` discharge move-group packing and host-write
exclusion. The bank premise uses the per-bit relation with the RTL mask.
`trace_cfg_size` carries the size condition and `maskedZero_release_trace`
proves masked zero on reset release. The general one-step lemmas take the
corresponding state facts as inputs. The trace induction supplies those facts.

The witness uses `Contents.init` and holds the SPI pins idle with CS_N high
and SCK and MOSI low. It releases reset at sample 1. At sample 3, `runRst` is
true and stream 0 raises RQ in the next state. Reset is reasserted from
sample 4 onward. SCK stays low through the synchronizer and both stream modes
stay at zero for every sample.

### Lean-printed statements

```lean
Metronome.ChipCut.trace_refines' (pins : Nat → Metronome.Machine.PinIn) (cont : Contents) (tables : Tables)
  (initial : InitialConditions cont) (env : ∀ (n : Nat), PinPremises (cutStateAt pins (resetState cont) n) (pins n))
  (n : Nat) : ChipRel (cutStateAt pins (resetState cont) n) (machineStateAt pins (absChip (resetState cont)) n)
Metronome.ChipCut.trace_refines'_all (pins : Nat → Metronome.Machine.PinIn) (cont : Contents) (tables : Tables)
  (initial : InitialConditions cont) (env : ∀ (n : Nat), PinPremises (cutStateAt pins (resetState cont) n) (pins n))
  (n : Nat) :
  ChipRel (cutStateAt pins (resetState cont) n) (machineStateAt pins (absChip (resetState cont)) n) ∧
    Discharge.CapInv (cutStateAt pins (resetState cont) n) (machineStateAt pins (absChip (resetState cont)) n) ∧
      StreamRelX (cutStateAt pins (resetState cont) n) (machineStateAt pins (absChip (resetState cont)) n)
Metronome.ChipCut.chip_step_refines' (s : State) (m : Metronome.Machine.State) (pin : Metronome.Machine.PinIn)
  (hrel : ChipRel s m) (hinv : Metronome.ChipCut.Inv s) (habs : Discharge.AbsInv s) (hexec : Discharge.ExecInv s)
  (hpinv : Discharge.HostPinInv s) (hldm : Discharge.ldModeInv s) (hlp0 : Discharge.LandingP0 s)
  (hls : Discharge.LandingStream s) (hlane : Discharge.laneInv s) (hcap : Discharge.CapInv s m)
  (hshape : streamShapeInv s) (hX : StreamRelX s m) (tables : Tables) (hspacing : Discharge.host_sck_spacing s pin)
  (h19 : ¬(s.arb.heldValid = true ∧ (hostCfgOf s).isSome = true)) (hwindow : Discharge.WindowWire.WindowQuiet s)
  (hsize : m.cfg.img.size = Metronome.Machine.Util.cfgSize)
  (hrelease :
    runRst s pin = false → pin.rstn = true → Discharge.BankWire.MaskedZero (Metronome.Machine.cfgNext m.cfg m.cw)) :
  ChipRel (step s pin) (Metronome.Machine.step m pin)
Metronome.ChipCut.premises_of (s : State) (m : Metronome.Machine.State) (pin : Metronome.Machine.PinIn)
  (hrel : ChipRel s m) (hinv : Metronome.ChipCut.Inv s) (habs : Discharge.AbsInv s) (hexec : Discharge.ExecInv s)
  (hpinv : Discharge.HostPinInv s) (hldm : Discharge.ldModeInv s) (hlp0 : Discharge.LandingP0 s)
  (hls : Discharge.LandingStream s) (hlane : Discharge.laneInv s) (hcap : Discharge.CapInv s m)
  (hshape : streamShapeInv s) (hX : StreamRelX s m) (tables : Tables) (hspacing : Discharge.host_sck_spacing s pin)
  (h19 : ¬(s.arb.heldValid = true ∧ (hostCfgOf s).isSome = true)) (hwindow : Discharge.WindowWire.WindowQuiet s)
  (hsize : m.cfg.img.size = Metronome.Machine.Util.cfgSize) (hact : runRst s pin = true) : Premises s m pin
Metronome.ChipCut.trace_premises_satisfiable (_tables : Tables) :
  ∃ pins cont, InitialConditions cont ∧ ∀ (n : Nat), PinPremises (cutStateAt pins (resetState cont) n) (pins n)
Metronome.ChipCut.trace_premises_satisfiable_active :
  ∃ pins cont,
    InitialConditions cont ∧
      (∀ (n : Nat), PinPremises (cutStateAt pins (resetState cont) n) (pins n)) ∧
        ∃ n,
          runRst (cutStateAt pins (resetState cont) n) (pins n) = true ∧
            (streamAt (cutStateAt pins (resetState cont) (n + 1)) 0).rq = true
```

`trace_refines'` uses `propext`, `Classical.choice`, `Quot.sound`, and 96
`bv_decide` certificate axioms. Each witness theorem uses only the three
standard axioms. The evidence includes exact statements with the premise
record fields, the complete axiom list, and build and table check timings.

- [Lean statements](../../../data/raw/lean_chipcut_final_v4_20261122/statements.txt)
- [Axiom audit](../../../data/raw/lean_chipcut_final_v4_20261122/axioms.txt)
- [Commands and outputs](../../../data/raw/lean_chipcut_final_v4_20261122/commands.log)
