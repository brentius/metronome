# Bridge notes: the strong replay-buffer relation `BufRelX`

Written 2026-11-22.  Files:

* `lean/Metronome/Bridge/StreamBuf.lean` — the new module
  (`namespace Metronome.Bridge.StreamBuf`), importing
  `Metronome.Bridge.Stream` only.
* Evidence: `data/raw/lean_bridge_streambuf_v4_20261122/` — `axioms.txt`
  (25 `#print axioms` lines, no `sorryAx`), `axioms.lean`, `commands.log`.

Acceptance: `lake build Metronome.Bridge.StreamBuf` exits 0 with
`-DwarningAsError=true` from the lakefile (Lean 4.35.0, core libraries only):
42 s, 23 jobs, no warnings, in a checkout whose `Metronome.Bridge.Stream`
olean was already built.  No `sorry`, no `native_decide`, no `admit`; `src/` is
untouched (`git diff --quiet HEAD -- src` exits 0).

Purpose.  `Metronome/Bridge/Stream.lean` bridges the ten scalar stream
registers under `AbsRelB` and the replay buffer only through `BufRel`, which
guards `WB` by `WV` and `NB` by `NV`, leaving the three replay corners of
`BRIDGE_UNITS_STREAM_NOTES.md` ("The replay buffer relation") open.  This module
defines a strict relation on the buffer, proves it is preserved by one stream
step in both the unfrozen and the frozen cycle (host rewind included, flush
unconstrained), witnesses the one genuine divergence on a trace from reset, and
re-proves the frozen state bridges without the `flush = false` side condition.

## 1. The relation

```lean
def BufRelX (cap : Bool) (s : Stream.State) (m : Machine.StreamSt) : Prop :=
  s.wb = m.wb ∧ s.wv = m.wv ∧ s.nb = m.nb ∧ (cap = true → s.nv = m.nv)
```

`WB`, `WV` and `NB` always agree; `NV` agrees for a `CAP = 1` stream.  With
`CAP = 0` the cut's `NV` is inert (the RTL has no second slot) and the machine
clears it on a rewind (§6.3 vs AMBIG(14), witness (b′) of
`BRIDGE_UNITS_STREAM_NOTES.md`), so it is excluded exactly as in `BufRel`'s
`CAP = 0` part.  There is no shape clause (`WV = 0 → NV = 0`) and no
pending-landing clause: slot equality carries both where they are valid.

| theorem | statement |
|---|---|
| `BufRelX.wb_eq` / `.wv_eq` / `.nb_eq` / `.nv_eq` | the four projections (`nv_eq` takes `cap = true`) |
| `BufRelX.capture_wb` | `BufRelX cap s m → s.pv = true → s.wb = m.wb` — the `PV → WB` clause of `WIRE_CORECOMB_NOTES.md` §8, for every mode |
| `BufRelX.toBufRel` | `BufRelX cap s m → ¬ (s.rq = true ∧ s.ld = true) → BufRel cap s m` |
| `bufRelX_reset` | `BufRelX cap Stream.resetState (default : Machine.StreamSt)` |
| `bufRelX_abs_reset` | `BufRelX cap Stream.resetState (abs Stream.resetState)` |

`toBufRel` takes the read-handshake clause `¬ (RQ ∧ LD)` separately: it is not
a buffer fact (the receive and capture branches of `Stream.ldNext` hold `LD`,
so a mode change while a read is outstanding keeps `RQ ∧ LD`; that is the
`stream_mode_quiet` item of `WIRE_CORECOMB_NOTES.md` §11).  The current
`ChipRel` gets the clause from `AbsRelB`'s `BufRel`; at the next state it is
still the assembler's obligation, not a consequence of the buffer relation.

## 2. Step preservation

The unfrozen step (all four modes, `frz = false` as in `abs_step_unfrozen`):

```lean
theorem bufRelX_step_unfrozen (cap) (s) (i) (m)
    (hreset : i.resetN = true) (hfrz : i.frz = false)
    (hfresh : s.ld = true → i.frzd = false)
    (h : AbsRelB cap s m) (hb : BufRelX cap s m) :
    BufRelX cap (Stream.step cap s i)
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false)
```

with one lemma per field (`wb_step_unfrozen`, `wv_step_unfrozen`,
`nb_step_unfrozen`, `nv_step_unfrozen`, the last under `cap = true`).  The proof is the same mode split as `abs_step_unfrozen`
(`mode_cases`) plus a split on `rewind`, `LD`, `FRZD`, `apply`, `WV`, `NV`;
each branch closes by substituting the slot equalities and `bv_id` for the
machine's `bv 32 ramOut`.

The frozen step:

```lean
theorem bufRelX_step_frozen (cap) (s) (i) (m)
    (hreset : i.resetN = true) (hfrz : i.frz = true)
    (hland : s.ld = true → i.frzd = true)
    (h : AbsRelB cap s m) (hb : BufRelX cap s m) :
    BufRelX cap (Stream.step cap s i)
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) true)
```

No move, rewind, flush or `FRZD` side condition beyond `hland`: with the
landing exception off, both readings hold the whole buffer (`WB` by
`wbNext`'s `frz` branch and the machine's frozen branch, `WV`/`NV` by their
`frz` holds, `NB` because `nbNext`'s frozen branch needs `!FRZD` and the
machine's frozen landing test is `s.ld && landNow`), and a rewind clears `WV`
(and `NV` for `CAP = 1`) on both sides.  Field lemmas: `wb_step_frozen`,
`wv_step_frozen`, `nb_step_frozen`, `nv_step_frozen` (the last under
`cap = true`).

## 3. The three corners

| corner (`BRIDGE_UNITS_STREAM_NOTES.md`) | status |
|---|---|
| 1. frozen landing with `WV = 0` (AMBIG 11) | **witnessed** in the raw slots; corrects to a same-slot bridge under `hslot` and to the guarded `BufRel` under `ShapeOK` (§8); the one genuinely divergent sub-case has `WV = 0 ∧ NV = 1` |
| 2. `apply ∧ LD` in one cycle | **closed**: `apply` shifts both readings identically (`WB' = NB`, `WV' = NV`, `NV' = 0`, then the landing fills the free slot from the RAM output); the stale `NB` is now related by slot equality, so the machine's next landing word (`NB` after the shift) and the cut's agree |
| 3. `LD ∧ occupied ∧ FRZD` (landing into the second slot one cycle after a freeze) | **closed** by `hfresh`: it needs `LD = 1` with `FRZD = 1`, impossible under `hland` along a trace (§4) |

Corners 2 and 3 were artefacts of guarding the slots: the raw `NB`/`WB` slots
never diverge under the chip's freeze discipline, so relating *all* slots is
both sound and sufficient, and no pending-landing clause is needed.  The shape
clause is implied too (for `CAP = 1`, `WV = 0` with `NV = 1` would need a
landing into an empty first slot on both sides, which would have set `WV`).

Corner 1 is real.  `frozen_landing_witness` is a three-cycle composed trace
from reset — cycle 1 requests a replay read, cycle 2 serves it, cycle 3 freezes
with `FRZD = 0`:

```lean
theorem frozen_landing_witness :
    (Stream.step true wS2 wV3).wb = 0 ∧ (Stream.step true wS2 wV3).wv = false ∧
    (Stream.step true wS2 wV3).nb = 0xAAAAAAAA ∧ (Stream.step true wS2 wV3).nv = false ∧
    wM3.wb = 0xAAAAAAAA ∧ wM3.nb = 0
theorem frozen_landing_bufrelX_fails :
    ¬ BufRelX true (Stream.step true wS2 wV3) wM3
theorem frozen_landing_ld : wS2.ld = true ∧ wS2.wv = false ∧ wS2.rq = false
```

(`wS2` is the cut state entering the frozen cycle, `wM3` the machine state after
it; `wV1`/`wV2`/`wV3` are replay-mode inputs, `wV3` has `frz = true`,
`frzd = false`, `rdata = 0xAAAAAAAA`.)  The cut parks the word in `NB`
(`nbNext`'s `rpl && ld && !frzd && frz` branch) and the machine in `WB`
(`streamNext`'s `mode == 3 && s.wv` test, AMBIG(11)), so `WV = 0` with the word
*pending*; the next unfrozen cycle re-converges (both land from `NB`/`WB`), but
the raw slots differ at the frozen state.  Hence corner 1 cannot be closed by
slot equality: it stays the named hypothesis `hland`.  All three witness
theorems are kernel `decide` on concrete values (no `native_decide`).

## 4. Why the unfrozen step may assume `LD → !FRZD`

`frozen_ld_false`:

```lean
theorem frozen_ld_false (cap) (s) (i)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hfzd : i.frzd = false)
    (hland : s.ld = true → i.frzd = true) : (Stream.step cap s i).ld = false
```

and `ld_frozen_hold` (`frz = true`, `s.ld = false` ⇒ the cut's `LD' = false`)
keep `LD` clear along a frozen run: a run starts with `FRZD = 0` (the previous
cycle was unfrozen), so `hland` forces `LD = 0` at its first cycle, and every
later frozen cycle holds `LD`.  The first unfrozen cycle has `FRZD = 1`
(`FRZD` is the previous cycle's `FRZ`, §12.3) with `LD = 0`, so `hfresh` is
vacuous there.  The only other way to have `FRZD = 1` at an unfrozen cycle is
again "the previous cycle was frozen", so `hfresh` holds at every unfrozen
cycle of a trace satisfying `hland`.  This is the only extra hypothesis of the
unfrozen buffer step; it is *not* a divergence, just the read-timing side
condition that the frozen bridge's `hland` encodes.  `StreamWire.landing` is in fact false (§8): without it the unfrozen cycle after a frozen landing has `LD = 1` with `FRZD = 1` and needs the pending-landing bridge noted there.

## 5. Frozen bridges with a flush input

The cut's `Stream.fl` gates the whole flush by `!FRZ` (`Metronome/Stream.lean`
line 287) and the machine gates `flushReq` by `!frozen`
(`Metronome/Machine/Stream.lean` lines 151/154), so a frozen cycle ignores a
flush in both readings.  Four frozen bridges are restated with `flush` free:

```lean
theorem abs_step_frozen_flush (cap) (s) (i)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = false)
    (hland : s.ld = true → i.frzd = true)
    (hside : i.adv = false ∧ i.rxWe = false ∧ i.capPush = false ∧ i.replayLate = false) :
    abs (Stream.step cap s i) =
      Machine.streamNext (cfgOf i) (modeOf cap i) (abs s) (absIn cap s i) true

theorem abs_step_frozen_rewind_flush (cap) (s) (i)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = true)
    (hland : s.ld = true → i.frzd = true)
    (hside : i.adv = false ∧ i.rxWe = false ∧ i.capPush = false ∧ i.replayLate = false)
    (hnv : cap = true ∨ s.nv = false) :
    abs (Stream.step cap s i) =
      Machine.streamNext (cfgOf i) (modeOf cap i) (abs s) (absIn cap s i) true

theorem frozen_rel_flush (cap) (s) (i) (m) (c) (mode)
    (h : AbsRelB cap s m)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = false)
    (hland : s.ld = true → i.frzd = true)
    (hadv : i.adv = false) (hrx : i.rxWe = false)
    (hpush : i.capPush = false) (hlate : i.replayLate = false) :
    AbsRelB cap (Stream.step cap s i) (Machine.streamNext c mode m (absIn cap s i) true)

theorem frozen_rel_rewind_flush (cap) (s) (i) (m) (c) (mode)
    (h : AbsRelB cap s m)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = true)
    (hstart : Machine.Util.bv 11 c.start = i.cfgStart)
    (hland : s.ld = true → i.frzd = true)
    (hadv : i.adv = false) (hrx : i.rxWe = false)
    (hpush : i.capPush = false) (hlate : i.replayLate = false) :
    AbsRelB cap (Stream.step cap s i) (Machine.streamNext c mode m (absIn cap s i) true)
```

The first two are `abs_step_frozen` / `abs_step_frozen_rewind` with the
`flush = false` conjunct removed; the proofs are the same and `hfrz` collapses
`Stream.fl` to `false`.  The last two are the discharge's `frozen_rel` /
`frozen_rel_rewind` with the `hfl : i.flush = false` premise removed (their
starve-event step already carries `hfrz`, and `Stream.fl` is `false` under it).
Because the discharge uses the relational form, these last two are what remove
**`StreamWire.hostctl`** (both the flush and the rewind halves): the flush half
is no longer needed and the rewind half was already covered by
`frozen_rel_rewind`.  `hnv` (witness (b′), AMBIG(14)) is not needed in the
relational forms, exactly as before.

## 6. Plugging into the assembler

* Keep `AbsRelB` for the scalar registers and add `BufRelX` for the buffer
  (or define `AbsRelX cap s m := AbsRelB cap s m ∧ BufRelX cap s m`; the
  buffer part is independent of the scalar part in every statement here).
  `BufRel` remains derivable: `BufRelX.toBufRel` given `¬ (RQ ∧ LD)`, which the
  current `ChipRel` supplies through `AbsRelB` and the chip supplies through
  `stream_mode_quiet` at the next state.
* Reset: `bufRelX_reset` / `bufRelX_abs_reset` (both reset states are the zero
  record).
* Unfrozen cycle: `bufRelX_step_unfrozen`, with `hreset`, `hfrz = false`,
  `AbsRelB`, `BufRelX` and `hfresh` (§4).
* Frozen cycle (with or without a host rewind, any flush): `bufRelX_step_frozen`,
  with `hreset`, `hfrz = true`, `AbsRelB`, `BufRelX` and `hland` — the
  scalar part use `frozen_rel_flush` / `frozen_rel_rewind_flush` in place of
  `frozen_rel` / `frozen_rel_rewind`, which drops **`StreamWire.hostctl`**
  entirely (§5).  For the landing exception (§8) use
  `frozen_rel_landing_flush` / `frozen_rel_landing_rewind_flush` with
  `ldModeInv` and `ShapeOK`; then `StreamWire.landing` is dropped too.
* `WIRE_CORECOMB_NOTES.md` §8: the ad-hoc `hwb` premise of
  `contents_open_req_wb` (`PV → machine WB = cut WB`) is
  `BufRelX.capture_wb`, a projection of the relation, so that hypothesis can be
  dropped once `ChipRel` carries `BufRelX`.
* `ASSEMBLY_NOTES.md` row `dbgHwb`: the first replay slot is no longer only
  `WV`-guarded — `BufRelX.wb_eq` gives the word equality unconditionally, so
  the remaining `DbgWire.hwb` obligation is the DBG wiring, not the buffer
  relation.

## 7. Limitations

* Lean-checked implications between the cut spec and the machine spec, not
  RTL-vs-machine: no co-simulation is involved, and the witnesses are proofs
  about the two specifications on concrete traces.
* `StreamWire.landing` is **false**; §8 replaces it with `ldModeInv` (a trace
  result) and `ShapeOK`.  The one sub-case that genuinely diverges (a frozen
  landing into an empty replay head with a valid second slot) is witnessed and
  excluded by `ShapeOK`; a relation carrying the pending word instead of the
  slot would be needed to drop that, and the witness shows slot equality cannot.
  The unfrozen cycle immediately after a frozen landing needs the companion
  pending-landing bridge noted in §8 if `StreamWire.bufrel` is to be
  discharged there.
* The step lemmas take `AbsRelB` and `BufRelX` separately and conclude
  `BufRelX`; the combined `AbsRelB ∧ BufRelX` invariant is assembled by the
  discharge from `abs_step_unfrozen` / `frozen_rel_flush` /
  `frozen_rel_rewind_flush` on the scalar side and these lemmas on the buffer
  side.  The one clause not re-established here is the read-handshake clause
  `¬ (RQ ∧ LD)` (`stream_mode_quiet`), which `BufRelX.toBufRel` therefore takes
  as a hypothesis.

## 8. The landing exception (§12.3): `LD = 1` with `FRZD = 0`

The assembler proved `StreamWire.landing` (`LD → FRZD`) **false**
(`streamWire_landing_false`): `LD` is held through a frozen cycle, so a host
freeze one cycle after a served read gives `LD = 1, FRZD = 0` and the machine's
frozen branch captures the RAM output (`Machine/Stream.lean` 154-157).  The
lemmas below cover that cycle, so `landing` can be dropped.

The post-state equations (proved for every state, mode and inputs):

| theorem | value |
|---|---|
| `wb_frozen_landing` | `WB' = txMode && LD && !FRZD ? rdata : WB` |
| `nb_frozen_landing` | `NB' = RPL && LD && !FRZD ? rdata : NB` |
| `mach_frozen_landing` | the machine's frozen post record: `WB`/`NB` take `rdata` in the slot selected by `mode == 3 && WV`, `starved := STARVED && !CTL[7]`, all else held |
| `mach_frozen_rewind_landing` | the same, then the rewind override (`POS/BIDX/CUR/CV/WV/RQ/LD/PV/NV = 0`, `BA = START`, `WB`/`NB`/`PEND` as above) |
| `modeOf_eq_three` | `(modeOf cap i == 3) = rpl cap i` |
| `ld_frozen_eq` / `rq_frozen_hold` / `nv_frozen_hold` | `LD`/`RQ`/`NV` hold in a frozen cycle with no rewind |
| `starved_frozen` | `STARVED' = STARVED && !CTL[7]` with no move input |

The bridges:

```lean
theorem abs_step_frozen_landing (cap) (s) (i)
    (hreset : i.resetN = true) (hfrz : i.frz = true) (hrew : i.rewind = false)
    (hslot : s.ld = true → i.frzd = true ∨ txMode cap i = true ∨
      (rpl cap i = true ∧ s.wv = true))
    (hside : i.adv = false ∧ i.rxWe = false ∧ i.capPush = false ∧ i.replayLate = false) :
    abs (Stream.step cap s i) = streamNext (cfgOf i) (modeOf cap i) (abs s) (absIn cap s i) true

theorem bufRelX_step_frozen_landing [and _rewind] (cap) (s) (i) (m) (c)
    (h : AbsRelB cap s m) (hb : BufRelX cap s m)
    (hreset) (hfrz) (hrew) (hslot) :
    BufRelX cap (Stream.step cap s i) (streamNext c (modeOf cap i) m (absIn cap s i) true)

theorem frozen_rel_landing_flush [and _rewind_flush] (cap) (s) (i) (m) (c)
    (h : AbsRelB cap s m)
    (hreset) (hfrz) (hrew)
    (hldmode : s.ld = true → txMode cap i = true ∨ rpl cap i = true)
    (hshape : ShapeOK s)               -- ShapeOK s := s.wv = false → s.nv = false
    (hadv) (hrx) (hpush) (hlate) :
    AbsRelB cap (Stream.step cap s i) (streamNext c (modeOf cap i) m (absIn cap s i) true)
```

`hslot` is exactly the "both readings write the same slot" condition:
`FRZD = 1` (no landing), transmit (`WB`), or replay with an occupied first slot
(`NB`).  `hldmode` is the chip's `ldModeInv` (`LD → mode ∈ {0, 3}`, proved along
traces from `stream_mode_quiet`); `hshape` is the replay-buffer well-formedness
"an empty first slot implies an empty second".

Which frozen landings agree:

| case | cut | machine | outcome |
|---|---|---|---|
| transmit (mode 0) | `WB := rdata` | `WB := ramOut` | same slot: **exact equality** (`abs_step_frozen_landing`, `bufRelX_step_frozen_landing`) |
| replay, `WV = 1` | `NB := rdata` | `NB := ramOut` | same slot: **exact equality** |
| replay, `WV = 0`, `NV = 0` | `NB := rdata` | `WB := ramOut` | raw slots differ (AMBIG 11), guarded `BufRel` still needs `WV = 0`/`NV = 0` only: `frozen_rel_landing_*` |
| replay, `WV = 0`, `NV = 1` | `NB := rdata` (clobbers the valid second slot) | `WB := ramOut` | **genuine divergence**, witnessed |
| receive/capture with `LD = 1` | holds `WB` | `WB := ramOut` | excluded by `hldmode` (LD only in transmit/replay) |
| with a host rewind | `WV`/`NV` cleared on both sides | same | `BufRel` is reflexive; the exact-state form needs `hnv` for `CAP = 0` as before, the relational forms do not |

The divergent state needs an empty first slot with a valid second one, which a
replay stream never produces; it is reachable only through a mode excursion
into transmit that consumes a word while `NV` is set, and §9a.13 leaves a
`MODE` change without a rewind unspecified.  Witness:

```lean
def wS4 : Stream.State := { wS with nv := true }
theorem wS4_not_shape : ¬ ShapeOK wS4
theorem frozen_landing_invalid_nv_disagrees :
    BufRel true wS4 (abs wS4) ∧
    ¬ BufRel true (Stream.step true wS4 wI2)
        (streamNext (cfgOf wI2) (modeOf true wI2) (abs wS4) (absIn true wS4 wI2) true)
```

(`wS`/`wI2` are the replay witness state and inputs of `Bridge.Stream`.)  The
older `frozen_landing_witness` / `frozen_landing_bufrelX_fails` (a three-cycle
trace from reset) shows the same corner for `BufRelX` with `NV = 0`.

Consequence for the discharge: `StreamWire.landing` can be dropped from
`premise_streams`; the frozen cycle is covered by
`frozen_rel_landing_flush` / `frozen_rel_landing_rewind_flush` (relational
`AbsRelB`, which is what `premise_streams` concludes), under `StreamWire.mode`
(for `modeOf`), `ldModeInv` (already a trace result) and a `ShapeOK` premise.
The previous round's `bufRelX_step_unfrozen` still excludes `LD = 1` with
`FRZD = 1` (`hfresh`), so the *unfrozen* cycle immediately after a frozen
landing, if the capstone wants to discharge `StreamWire.bufrel` there instead
of assuming it, needs a companion "pending landing" bridge: with `FRZD = 1` the
cut lands from `NB` and the machine from its `if WV then NB else WB` slot, and
the pending word agrees after the frozen landing
(`s.nb = if s.wv then m.nb else m.wb`).  That is not needed for
`premise_streams` (which takes the next-state `BufRel` as the `bufrel` field),
and is recorded here as the next item.

## 9. `ShapeOK` as an invariant

The chip-level premise `stream_mode_quiet` is strengthened (decision of
2026-11-22b) to "a stream's effective mode changes only while
`LD = RQ = WV = NV = 0`" — stricter than SPEC and recorded as a limitation.  At
the stream level the invariant is mode-indexed by the *previous* cycle's mode:

```lean
def ShapeModeOK (mode : Nat) (s : Stream.State) : Prop :=
  ShapeOK s ∧ (s.nv = true → mode = 3)

theorem shapeModeOK_reset (mode) : ShapeModeOK mode Stream.resetState
theorem shapeOK_step (s) (i) (pmode) (h : ShapeModeOK pmode s)
    (hchange : modeOf true i = pmode ∨ (s.wv = false ∧ s.nv = false)) :
    ShapeOK (Stream.step true s i)
theorem shapeModeOK_step (s) (i) (pmode) (h : ShapeModeOK pmode s) (hchange) :
    ShapeModeOK (modeOf true i) (Stream.step true s i)
```

`hchange` is exactly the mode-change discipline: the mode is unchanged, or the
stream had `WV = NV = false` when it changed.  Supporting facts:
`nv_step_true_or` (`NV' = 1` needs a valid second slot or a replay landing) and
`rpl_nv_wv` (in replay `NV' = 1 ⇒ WV' = 1`, using `ShapeOK`), both by exhaustive
case analysis of `nvNext`/`wvNext`.  For `CAP = 0`, `nv_step_cap_false` (its
`NV` never changes) gives `shapeOK_step_cap_false` from `NV = false`.

The hypothesis is necessary: `shapeOK_break_witness` is a transmit cycle from
`WV = NV = 1` (a state that the strengthened quietness excludes at a mode
change) that consumes `WV` at lane 3 while `NV` stays set, so `ShapeOK` fails.

## 10. The pending landing and the packaged cycle step

`HeldLanding s m := (s.wv = false → s.nb = m.wb) ∧ (s.wv = true → s.nb = m.nb)`:
after a replay frozen landing the cut's `NB` holds exactly the word the machine
parked in its free slot.  `HeldOK cap s i m := i.frzd = false ∨
(txMode ∧ s.wb = m.wb) ∨ (rpl ∧ HeldLanding s m)` is the held-landing condition
of the following unfrozen cycle.

```lean
theorem heldLanding_frozen_landing ...        -- the frozen landing establishes HeldLanding
theorem wb_frozen_tx_landing ...              -- and the transmit fact for HeldOK
theorem wv_step_unfrozen_ab / nv_step_unfrozen_ab   -- WV/NV equality from AbsRelB
theorem wb_step_unfrozen_guarded (h : AbsRelB) (hok : s.ld → HeldOK cap s i m)
    (hwv' : (Stream.step cap s i).wv = true) :
    (Stream.step cap s i).wb = (streamNext (cfgOf i) ... false).wb
theorem nb_step_unfrozen_guarded ...          -- the NV' → NB' clause
theorem wb_nb_unfrozen_capF / no_overlap_step -- CAP = 0 slots and ¬(RQ ∧ LD)
theorem bufRel_step_unfrozen_guarded (h : AbsRelB) (hok) (hreset) (hfrz) :
    BufRel cap (Stream.step cap s i) (streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) false)
```

Packaged, covering unfrozen (fresh **and** held landing), frozen (with or
without a host rewind), any flush and all modes:

```lean
theorem buf_step (cap) (s) (i) (m) (h : AbsRelB cap s m) (hreset)
    (hshape : ShapeOK s)
    (hldmode : s.ld = true → Stream.txMode cap i = true ∨ Stream.rpl cap i = true)
    (hok : s.ld = true → HeldOK cap s i m)
    (hside : i.adv = false ∧ i.rxWe = false ∧ i.capPush = false ∧ i.replayLate = false) :
    AbsRelB cap (Stream.step cap s i)
      (Machine.streamNext (cfgOf i) (modeOf cap i) m (absIn cap s i) i.frz)

theorem bufRelX_step (h) (hb : BufRelX) (hreset) (hslot) (hfresh) :
    BufRelX cap (Stream.step cap s i) (streamNext (cfgOf i) ... i.frz)
theorem bufRelX_step_abs ... : BufRelX ... ∧ AbsRelB ...
```

So `AbsRelB` — hence the guarded `BufRel` — is preserved on **every** cycle,
including the one right after a frozen landing (the `HeldLanding` companion).
`BufRelX` is kept in the same-slot cases (`hslot`: transmit, or replay with
`WV = 1`) plus the `hfresh` cycles; it cannot be preserved unconditionally — a
frozen landing with `WV = 0` swaps the raw slots (`frozen_landing_bufrelX_fails`)
and the consumed pending word leaves a stale `NB` until the next fresh landing.

Remaining named hypotheses: the strengthened mode quietness (chip premise,
§9); `hldmode` (the discharge's `ldModeInv`); `hok` (discharged at a frozen
landing by `heldLanding_frozen_landing` / `wb_frozen_tx_landing`); and for the
`BufRelX` variant `hslot` and `hfresh`, plus the read-handshake clause
`¬ (RQ ∧ LD)` for `BufRelX.toBufRel` (preserved by `no_overlap_step` from the
previous cycle's clause).

## 11. The write-buffer facts: `CapRel` and the guarded `dbgHwb`

**Consumer check.**  `mhcModesReq_abs_wb` (`CoreCombWire`) feeds `hwb` to
`streamReq_congr`; mode 1 writes `PEND` (`wrByte`), modes 0/3 are reads, and
only mode 2 (capture) writes `WB` (`wrWord … s.wb`).  So the capture-mode case
is the only one needed.  On the debug side, `rlv_value_of`/`apply_bridge` use
`WB` only in the `apply` branch, and `Debug.Ctrl.apply = replay && !frz &&
valid && …` (`Metronome/Debug.lean` 319) with `valid` the cut's `replayValid =
RPL && WV`, so `WV = 1` there.

**(1) `CapRel`.**  The strongest mode-free form of the capture clause is

```lean
def CapRel (cap : Bool) (s : Stream.State) (m : Machine.StreamSt) : Prop :=
  cap = true → s.pv = true → s.wb = m.wb
```

It is **not preserved**, even alongside `AbsRelB`: the one-step witness

```lean
theorem capRel_step_witness :
    AbsRelB true capS2 capM2 ∧ CapRel true capS2 capM2 ∧
    (Stream.step true capS2 capI2).pv = true ∧
    ¬ CapRel true (Stream.step true capS2 capI2)
      (Machine.streamNext (cfgOf capI2) (modeOf true capI2) capM2 (absIn true capS2 capI2) false)
```

with `capS2` a replay state (`WV = 1`, `NV = 0`, `PV = 1`) whose stale `NB`s
differ (`capM2 = { abs capS2 with nb := 9 }`): an `apply` publishes them into
`WB`.  The capture-relevant instance is *reachable*, on a five-cycle trace from
reset (a served replay read, a frozen landing with a host rewind — the AMBIG(11)
corner, which now also clears `WV`/`NV` — a receive completion setting `PV`, then
a capture cycle):

```lean
theorem capWb_reachable_witness :
    (capCut 5).pv = true ∧ (capM 5).pv = true ∧ (capM 5).wb ≠ (capCut 5).wb ∧
    modeOf true capV5 = 2
```

so the mode-2 `wrWord` request would differ (`streamReq 2` reads `s.wb` while
`PV`).  Hence `contentsWb` cannot be derived from `AbsRelB`/`BufRel` (or from any
state relation that holds on the reachable set); it stays a named hypothesis,
as the assembler anticipated.  Even adding `PV = 0` to the mode-change
discipline does not help: receive → capture with a byte completed in the same
cycle sets `PV' = 1` while `WB` is held (and may be stale).  What would fix it is
a chip-level guarantee that `WB` agrees at every capture entry, or a spec
alignment of the stale-slot conventions (AMBIG(11)).

**(2) `dbgHwb`.**  The guarded form is the one the consumers use, and it is a
projection of the buffer relation:

```lean
theorem dbgHwb_of_wv (cap) (s) (m) (h : AbsRelB cap s m) (hwv : s.wv = true) :
    m.wb = s.wb
theorem dbgHwb_of_replayValid (cap) (s) (i) (m) (h : AbsRelB cap s m)
    (hrv : Stream.replayValid cap s i = true) : m.wb = s.wb
```

The unguarded form is **false** at a reachable state:

```lean
theorem dbgHwb_unguarded_false : wM3.wb ≠ (Stream.step true wS2 wV3).wb
```

(the three-cycle frozen-landing trace of `frozen_landing_witness`, where `WV = 0`
— `frozen_landing_ld`).  The assembler can restate `dbgHwb` as
`wv = true → …` (or `replayValid = true → …`) without loss to
`apply_bridge`/`rlv_value_of`.

## 12. The mode-indexed capture invariant (`CapModeOK`)

Decision of 2026-11-22d: `stream_mode_quiet` is extended once more — on a cycle
where stream `k`'s mode changes, `PV = 0` in **both** the current and the next
state, in addition to `LD = RQ = WV = NV = 0` ("change a stream's mode only
while it is completely idle"; stricter than SPEC, recorded).  This closes the
§11 corner (a receive → capture change with pending data).

The invariant is mode-indexed by the mode of the cycle that produced the state
(the `ShapeModeOK` pattern):

```lean
def CapModeOK (mode : Nat) (s : Stream.State) (m : Machine.StreamSt) : Prop :=
  (mode = 2 → s.ld = false) ∧ (mode = 2 → s.pv = true → s.wb = m.wb)

theorem capModeOK_reset (mode) :
    CapModeOK mode Stream.resetState (default : Machine.StreamSt)

theorem capModeOK_step (cap) (s) (i) (m) (c) (pmode)
    (h : AbsRelB cap s m) (hcap : CapModeOK pmode s m) (hreset : i.resetN = true)
    (hcfg : Machine.streamEnd c m = Machine.streamEnd (cfgOf i) m)
    (hchange : modeOf cap i = pmode ∨
      (s.pv = false ∧ (Stream.step cap s i).pv = false ∧ s.ld = false ∧ s.rq = false)) :
    CapModeOK (modeOf cap i) (Stream.step cap s i)
      (Machine.streamNext c (modeOf cap i) m (absIn cap s i) i.frz)
```

`hcfg` is the usual config agreement (rfl for `c = cfgOf i`).  The `LD = false`
conjunct is what makes the capture clause robust: it rules out the frozen/mode
2 landing (a capture stream has no read in flight), and it is preserved at a
mode change from `s.ld = false`.  The `PV` clause is preserved per capture case:
a push writes the same record into `WB` on both sides; otherwise `PV' = PV` and
the previous invariant gives `s.wb = m.wb`.  In the changed-mode case both `PV`
and `PV'` are false, so the clause is vacuous.

Consumer form, in the shape `contents_open_req_wb` needs:

```lean
theorem contentsWb_of_capModeOK (cap) (s) (i) (m) (pmode) (h : CapModeOK pmode s m)
    (hchange : modeOf cap i = pmode ∨ s.pv = false)
    (hm2 : modeOf cap i = 2) (hpv : s.pv = true) : m.wb = s.wb
```

The discharge supplies `hchange` from the step that produced `s`: either the
mode is unchanged, or the producing step was a change with `PV = 0` (so
`hpv` fails).  Hence `contentsWb` can be restated as
`CapModeOK (prevMode) (streamAt s k) m.streams[k]` and discharged on traces.

The §11 reachable witness is excluded by the new premise:

```lean
theorem capWb_hchange_excluded :
    ¬ (modeOf true capV5 = modeOf true capV4 ∨
        ((capCut 5).pv = false ∧ (Stream.step true (capCut 5) capV5).pv = false ∧
          (capCut 5).ld = false ∧ (capCut 5).rq = false))
```

— the last (capture) cycle changes receive (1) → capture (2) with
`(capCut 5).pv = true`, so no branch of `hchange` holds.  With the extended
discipline the §11 capture state is unreachable through a mode change; the only
`PV = 1` states in capture are pushes, where `WB` agrees by construction.

## 13. Evidence and commands

`data/raw/lean_bridge_streambuf_v4_20261122/commands.log` records exit codes and
wall times: `lake build Metronome.Bridge.StreamBuf` exit 0 in 192 s (23 jobs,
`-DwarningAsError=true`, no warnings); the axiom dump exit 0 with 72
`#print axioms` declarations, all `[propext, Classical.choice, Quot.sound]` or
fewer, none `sorryAx`; a source scan finds no `sorry`/`native_decide`/`admit`;
`git diff --quiet HEAD -- src` exits 0.  Reproduce:

```powershell
cd lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.Bridge.StreamBuf
lake env lean ../data/raw/lean_bridge_streambuf_v4_20261122/axioms.lean
cd ..
git diff --quiet HEAD -- src
```
