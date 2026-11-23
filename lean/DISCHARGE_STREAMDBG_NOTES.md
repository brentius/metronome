# Discharge notes: the `streams` and `dbg` premise fields

Written 2026-11-21.  Files:

* `lean/Metronome/ChipCut/Discharge/StreamDbg.lean` — the discharge
  (`namespace Metronome.ChipCut.Discharge`).
* Evidence: `data/raw/lean_chipcut_discharge_streamdbg_v4_20261121/` —
  `axioms.txt` (47 `#print axioms` lines, no `sorryAx`), `axioms.lean`,
  `commands.log`, `run_evidence.ps1`; the frozen-rewind round is also recorded in
  `data/raw/lean_bridge_stream_frozen_v4_20261121/` (`axioms.txt`,
  `commands.log`, `build.log`).

Acceptance: `lake build Metronome.ChipCut.Discharge.StreamDbg` exits 0 with
`-DwarningAsError=true` (Lean 4.35.0, core libraries only); a clean rebuild of
the module (its `olean` removed) takes 12.5 s, the frozen-rewind round 14 s, the
axioms dump 3.3 s, and `git diff --quiet HEAD -- src` is true.  No
`sorry`/`sorryAx`, no `native_decide`, no `admit`.

## 1. Deliverables

```lean
theorem premise_streams (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hw : StreamWire s m pin) :
    ∀ k : Fin 2, Bridge.StreamB.AbsRelB (k.val == 0) (streamAt (activeStep s pin) k.val)
      (Machine.step m pin).streams[k]

theorem premise_dbg (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hrel : ChipRel s m) (hinv : Inv s) (hact : runRst s pin = true)
    (hw : DbgWire s m pin) :
    DbgRel (activeStep s pin) (Machine.step m pin).dbg
```

`StreamWire`/`DbgWire` are *structures of explicit wiring hypotheses*, not
opaque blobs: each field is a named, independently checkable equality about one
cross-component input, and the notes below say which bridge would close it.

## 2. What is proved unconditionally

Everything that follows is proved from `ChipRel`, `Inv`, the active-cycle sample
and the cited bridges; no extra hypothesis of its own.

* **Projections of the machine's inline records.**  `Machine.runStep` builds its
  per-cycle inputs inline; `machLcs`/`machCbs`/`machAllMoves`/`machWs`/
  `machMode`/`machSreq`/`machServed`/`machCevRec`/`machApplyLate`/`machHw`/
  `machCw`/`machStreamIn`/`machDbgNext` are verbatim copies of its `let`
  bindings, and `runStep_streams` / `runStep_dbg` are definitional (no rewriting
  of `Machine.**`):
  `(runStep m pin).1.streams[k] = streamNext (cfgView m.cfg).streams[k]
  (machMode m k) m.streams[k] (machStreamIn m k) m.dbg.frz`, and
  `(runStep m pin).1.dbg = machDbgNext m`.
* **Projections of the cut's active step** for `streams`, `dbgCtrl`,
  `dbgDigest` and `freeze`, plus the `streamAt`-indexed forms
  `activeStep_streamAt_zero/one` used by the next-state `BufRel`.
* **The stream configuration decode** `cfgOf_streamIn`:
  `Bridge.StreamB.cfgOf (streamIn s pin k) = (cfgView s.cont.cfg).streams[k]`,
  including the machine's `START`/`LEN`/`MARK` masks (`nbits … 0 11/12`); with
  `ChipRel.cfg` this is the `StreamWire.cfg` obligation, **proved in
  `streams_field_0/1`** (the field is not a hypothesis).
* **The zero-move bus**: `hitsMask 0 = 0`, `dsteqMask 0 = false`, `opg 0 = false`
  (used for `frozenNoMove ⇒ no stream strobe`).
* **The frozen relational stream step** `frozen_rel` (see §3.1) and its
  host-rewind form `frozen_rel_rewind` (§3.1.1).
* **The `CAP = 0` input gating** `streamNext_gate_irrel`: the machine's stream
  step at `modeOf false i` ignores `cev`/`apply`/`late`, so the per-stream
  capture/replay gating of `runStep` (`k == 0 && …`) is harmless for `S1`.
* **The ten `dbg` fields that `ChipRel.dbg` already relates**: `cen`, `rpl`,
  `emask`, `rlv`, `dc`, `men`, `misr`, `rlvp` (from `dbg_step_bridge`, whose
  `hcen…hmisr`, `hdifrz`, `hout`, `hoen` inputs are `DbgRel` fields plus the
  definitional `dbgDigestIn.frz/oOut/oEe`), and `freeze`, `frz`, `frzd` (from
  `CoreCtl.freeze_next/frz_next/frzd_next`; the bit conversion is `nbit_core`,
  `nbit x.toNat k = CoreCtl.bitAt x k`, and the host `DBG` byte decode is
  `DbgWire.hdbg`).
* The `Debug.Ctrl`/`Debug.Digest` step projections (`ctrl_step_*`,
  `digest_step_*`) and the `dbgNext_*`/`machDbgNext_eq` projections.

## 3. Findings that changed the intended proof

### 3.1 `abs_step_frozen` cannot be applied relationally — `frozen_rel` instead

`Bridge.StreamB.abs_step_frozen` concludes
`abs (Stream.step cap s i) = streamNext … (abs s) … true`: the machine state is
**`abs s`**, not the related `m`.  `ChipRel.streams` gives `AbsRelB`, which does
not fix `WB`/`NV` when the slots are invalid, so the exact-state bridge cannot be
instantiated at a related machine state.  This file therefore proves the
relational frozen step it needs:

> In a frozen cycle (`frz = 1`), with `resetN = 1`, no rewind, no landing
> (`LD → FRZD`), and no move/`late` input, both readings hold every register
> except `STARVED`; `STARVED' = STARVED && !clr` on both sides, and `BufRel` is
> preserved *reflexively* (no replay-buffer corner can fire).  `frozen_rel`.

The cut's half uses `Stream.frozen_holds` plus the `ld`/`wb`/`nb`/`nv`/`starved`
equations; the machine's half uses the fact that its frozen landing test is
`m.ld && (s.ld && !i.frzd)`, false under `LD → FRZD`.

### 3.1.1 The frozen rewind: `frozen_rel_rewind`

SPEC_V2 §12.3 keeps the host stream `CTL` (rewind and `STARVED` clear) running
while frozen, so a frozen cycle may rewind and the no-rewind form above is not
enough for the discharge.  `frozen_rel_rewind` covers it: it keeps every premise
of `frozen_rel` except `rewind = true`, adds `hstart : bv 11 c.start =
i.cfgStart` — the only configuration field §6.3's rewind reads (`BA' = START`) —
and concludes `AbsRelB` at `streamNext c mode m (absIn cap s i) true`.

The machine's frozen branch with a rewind is closed to the record
`{m with pos := 0, bidx := 0, ba := bv 11 c.start, cur := 0, cv := false,
wv := false, rq := false, ld := false, pv := false, starved := m.starved &&
!i.clrStarved, nv := false}`; the cut's half is `Stream.rewind_overrides`
(`POS' = 0`, `BIDX' = 0`, `BA' = START`, `CUR' = 0`,
`CV' = WV' = RQ' = LD' = PV' = 0`) plus the holding equations for `WB`, `NB`,
`PEND` and `STARVED' = STARVED && !CTL[7]`.  No `nv` hypothesis is needed here
(unlike the bridge's exact-state `abs_step_frozen_rewind`): `BufRel` constrains
`NV` only through `s.nv = m.nv` for `CAP = 1`, and for `CAP = 0` the inert slot
is unconstrained — which is exactly the recorded divergence (b')
(`Bridge.StreamB.frozen_rewind_inert_nv_disagrees`, `BRIDGE_UNITS_STREAM_NOTES.md`).
Both sides hold `WB`/`NB` because §6.3's rewind list omits them and no landing
can fire (`LD → FRZD`).

### 3.2 The `absIn` host-`CTL` map is *not* a gap

The bridge's `absIn` maps `ctlMove := some (ctlVal i)` with
`ctlVal i = rewind + 2·flush`, i.e. the **combined** cut rewind/flush (move OR
host `SRT.CTL` bits, as `Wire.streamIn` builds it), and `hCtl := clrVal i`
(host bit 7 only).  `streamNext`'s `rewind = nbit mctl 0 || nbit hctl 0` is
therefore the cut's combined rewind, and its `flushReq` the combined flush (the
host half gated by `!frozen` on both sides).  There is **no** translation loss,
so no witness of an `absIn` gap exists and none is claimed.

The earlier round treated the host `SRT.CTL` rewind as a side condition of the
frozen bridge (`StreamWire.hostctl`).  That was a limitation of the *bridge
statement*, not of the RTL or the machine: §12.3 lets a frozen cycle rewind, and
`abs_step_frozen_rewind`/`frozen_rel_rewind` (§3.1.1) now prove it, so
`StreamWire.hostctl` keeps only the **flush** half (§12.3 ignores a host stream
flush while frozen — the cut's `fl` and the machine's `flushReq` are both gated
by `FRZ`, and it stays an explicit side condition because the glue does not yet
prove `SRT.CTL[1] = 0` while frozen).  The one genuine reading difference at a
frozen rewind is the inert `CAP = 0` `NV` (witness (b'), §6.3 vs AMBIG(14)); it
is unobservable and needs no hypothesis in the relational form.

### 3.3 The `S1` capture/replay gating is harmless

`Machine.runStep` inserts `cev`/`apply`/`late` into `S0` only, while the cut's
`streamIn` presents them to both streams.  For `S1` (`CAP = 0`), `cen` and `rpl`
are false (a `CAP = 0` stream has no capture/replay), and every use of those
inputs is guarded by them, so the machine's gating is a no-op on the step:
`streamNext_gate_irrel`.  (`S1`'s unused `record`/`NB` fields are inert for the
same reason.)

## 4. Named hypotheses (open items)

All hypotheses are fields of `StreamWire` or `DbgWire`.

| field | why it is open |
|---|---|
| `StreamWire.mode` | `machMode` against `Bridge.StreamB.modeOf` (`streamMode_zero` plus `DbgRel.cen/rpl`).  Same index normalisation. |
| `StreamWire.input` | the machine's `StreamIn` against `absIn`: the `Sk.ADV`/`Sk.RX`/`Sk.CTL` picks (`resolveMoves` winners vs `Strobes.opg`/`Moves.pickWord`), the arbiter's `served == k+1` (`Mem.grantS0/1`), the landing (`ramOwner == k+1` vs the cut's `LD && !FRZD`), the capture record (`{DC, PIN}`), and `apply`/`late`.  These need the `MoveAgree` construction (`Bridge/Moves.lean` proves the fold *under* `MoveAgree`, and the `cores` thread owns `Core.Rel`), `Bridge.Mem.arbiter_eq` with the machine's `sreq` normalised to `someReq`, and the trace invariant `ramOwner == k+1 ↔ LD` (not a single-cycle relation). |
| `StreamWire.hostctl` | no stream **flush** this (frozen) cycle (§3.2).  A host `SRT.CTL` rewind and the `STARVED` clear are legal while frozen (§12.3) and are *proved*, by `frozen_rel_rewind` (§3.1.1), so they are not a side condition. |
| `StreamWire.landing` | `abs_step_frozen`/`frozen_rel`'s `LD → FRZD`; a host freeze one cycle after a served read is reachable and *both* readings land there — the corner §3.1 excludes. |
| `StreamWire.bufrel` | next-state `BufRel`: the three recorded replay-buffer corners (frozen landing with `WV = 0`, `apply ∧ LD`, `LD ∧ occupied ∧ FRZD`; `BRIDGE_UNITS_STREAM_NOTES.md`).  The frozen case needs none (proved by `frozen_rel`/`frozen_rel_rewind`); the unfrozen case is exactly the documented open bridge item. |
| `DbgWire.hdbg` | the host `DBG` byte (`hwByte (machHw m) "DBG" 0 "DBG"`) against the cut's `freezeIn.dbgWrite`/`data`.  It needs `machHw m = hwOf s` (`Bridge.Host.hw_bridge` + `LinkRel` + the cut/machine pin view). |
| `DbgWire.hmctl`, `hectl`, `hEH/hEC/hESH/hESC`, `hRH/hRC/hRSH/hRSC` | `dbg_step_bridge`'s host-map/`DBG`-window byte interface: the `hwAt` byte index against `Wire.dbgOff` (host map geometry) and the single core drain per cycle (`cwDrain`). |
| `DbgWire.hwb`/`hword` | the bridge's exact first replay slot `(vget m.streams 0).wb = wbw` with `wbw` the cut's `WB`; `BufRel` only guards `WB` by `WV`, so the raw slot is not a `ChipRel` consequence (the same stale-slot corner as `streams`). |
| `DbgWire.happly`/`hcev` | the replay `apply` comparison and the capture `cev`: `Bridge.Debug.apply_bridge`/`cev_bridge` close them given the machine's `WV`/`WB` and the pin view (`pinView` level/previous against `pinLvl`/`pinPrev`). |
| `DbgWire.real` | the cycle is unfrozen.  `dbg_step_bridge` requires `i.frz = false`; the frozen debug cycle is not bridged, and its recorded divergence is `RLVP` (`Bridge.Debug.rlvp_frozen_witness`: the machine sets `rlvp := RLV` even when frozen, the cut holds it). |

No new RTL/machine disagreement was found: the two anomalies above are bridge
statement limitations (§3.1, §3.3), and the `absIn` host-`CTL` concern of the
brief's checklist turned out not to be a loss (§3.2).  The one spec-reading
difference that survives is the inert `CAP = 0` `NV` at a rewind (witness (b'),
`BRIDGE_UNITS_STREAM_NOTES.md`), which §6.3 and AMBIG(14) read differently and
which the relational frozen step does not need.

## 5. Reproduce

```powershell
cd lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.StreamDbg        # exit 0, 14 s after the
                                                        # frozen-rewind edit
lake build Metronome.Bridge.Stream Metronome.ChipCut.Discharge.StreamDbg
                                                        # exit 0, 0.4 s (up to date)
lake env lean ..\..\..\data\raw\lean_chipcut_discharge_streamdbg_v4_20261121\axioms.lean
                                                        # exit 0, 3.8 s, 47 lines, no sorryAx
cd ..
git diff --quiet HEAD -- src                            # exit 0
```

`commands.log` records these commands with their exit codes and wall times; the
frozen-rewind round (including the stream bridge's 862 s re-elaboration) is in
`data/raw/lean_bridge_stream_frozen_v4_20261121/commands.log`.
