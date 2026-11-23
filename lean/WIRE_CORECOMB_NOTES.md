# W4 (rounds c-g): core combinational outputs, `pauseDisp`, and the RAM interface

File: `lean/Metronome/ChipCut/Discharge/CoreCombWire.lean`
(namespace `Metronome.ChipCut.Discharge`).  Lean 4.35.0, core libraries only,
`lake build` with `-DwarningAsError=true` (only `linter.unusedVariables` and
`linter.deprecated` disabled).  No `sorry`, no `native_decide`, no `admit`.

Round c starts from the orchestrator's `Wire.lean` fix
`streamReq := Stream.out (k == 0) …` (so no `CAP`-side hypothesis is left) and
closes the one-step preservation of `ExecInv`, which makes `WireAgree.pauseDisp`
unconditional along the cut trace.  Round d adds the canonical-abstraction
argument for the contents congruence: `contents_open_served` is discharged and
`contents_open_req` modulo one named capture-buffer invariant (§5).

---

## 1. Result table

| target | status | theorem / blocker |
|---|---|---|
| `WireAgree.dispatch` | **discharged** | `ccw_dispatch` |
| `WireAgree.pause` | **discharged** | `ccw_pause` |
| `WireAgree.pauseDisp` | **discharged, unconditionally** | `ccw_pauseDisp_cut` (from `ExecInv` alone: no `ChipRel`, no `Inv`, no `CoreInputBus`, no `hJGTab`); `ccw_pauseDisp_trace_cut` at any trace cycle. The `ChipRel`-based form `ccw_pauseDisp` is kept, and `ccw_pauseDisp_trace` is its trace-level corollary |
| `ExecInv` at reset / along the trace | **discharged** | `execInv_reset`, `execInv_step`, `execInv_trace` |
| per-core comb bundle vs `Core.out_bridge`/`fetch_bridge` | **discharged** | `coreDisp_eq`, `corePse_eq`, `coreDispThread_eq`, `coreNpc_eq`, `coreFetchEn_eq`, `coreFetchAddr_eq`, `coreXt_eq`, `coreXl_eq` |
| `p0_open_served` (and `mhcServed` form) | **discharged** | `p0_open_served`, `ccw_served` |
| `hostReq_open_served` | **discharged** | `hostReq_open_served` |
| `StreamWire.input.served` | **discharged** | `stream_served` |
| `p0_open_land` | **discharged from `LandingRel`** | `p0_open_land` |
| `p0_open_lane` | **discharged, guarded** | `p0_open_lane` (under `LandingRel` + `p0.land`); unguarded form is false (§3) |
| `StreamWire.input.landNow`/`ramOwner` | **discharged from `LandingRel`** | `stream_landNow` |
| `LandingRel` reset | **proved** | `landingRel_reset` |
| `LandingRel` P0 clause (`p0_open_land`) | **discharged on every trace cycle** | `LandingP0`, `landingP0_reset`, `landingP0_step`, `landingP0_trace`, `p0_open_land_trace` (§9) |
| `LandingRel` stream clause (`stream_landNow`) | **discharged in the LD-gated form**, on every trace cycle | `LandingStream` (`ld -> (ramOwner == k+1) = !FRZD`), `landingStream_reset/_step/_trace`, `stream_landNow_ld`, `stream_landNow_ld_trace`, under `stream_mode_quiet` (§11) every cycle (§13). The unguarded form is false (§9) |
| `p0_open_lane` | **discharged, `!FRZD`-guarded, on every trace cycle** | `laneInv`, `laneInv_reset`, `laneInv_step`, `laneInv_trace`, `p0_open_lane_trace`; `mhcLaneN_abs`, `lane_bv` (§12) |
| `stream_mode_quiet` | **defined** (§11) | one clause over `stateMode`: a mode change only while `ld = rq = 0`; host rewinds during a transfer are **not** excluded |
| `ldModeInv` (§11) | **discharged** | `LD -> mode in {0,3}`: `ldModeInv_reset`, `ldModeInv_step`, `ldModeInv_trace` |
| `pv → wv` (`hwv`) | **false** (§8) | `streamInv_pv_wv_false`: one capture push from reset gives `PV = 1, WV = 0` |
| `ld → mode ∈ {0,3}` | **false** (§8) | `streamInv_ld_mode_false`: a served transmit read followed by a receive cycle |
| `contents_open_req_wb` | **discharged** | the same congruence with the sharp `WB` premise, strictly stronger than the `hwv` form (§8) |
| `hmode` vs `StreamWire.mode` | **identical** (§10) | `ccw_served_of_wire`, `contents_open_served_of_wire` |
| `contents_open_served` | **discharged** | `contents_open_served` (`mhcServed m pin = mhcServed (absChip s) pin`): `mhcServed = machServed` (`mhcServed_eq_machServed`), `ccw_served` at `m` and `machServed_abs` at `absChip s` |
| `contents_open_req` | discharged modulo a **false** hypothesis (superseded, §8) | `contents_open_req` (`mhcReq m pin = mhcReq (absChip s) pin`) from `contents_open_served` + entry equalities (`mhcModesReq_abs0/1`, `p0Req_congr`, `hostReq_congr`); the one extra hypothesis is the capture-window invariant `hwv : ∀ k, (streamAt s k).pv = true → (streamAt s k).wv = true`, needed to read the `BufRel`-guarded `WB` slot of the mode-2 `wrWord` |
| `contents_open_cbs` | **open** (§8) | the `Machine.coreComb` congruence between `m` and `absChip s`: it has to reproduce the whole `moves`/`npc`/`fetch` bundle field by field (guard and source vector congruence, `IR` under `XV`, thread file, `cfg`); `mhcCbs_eq_machCbs` reduces it to `machCbs m = machCbs (absChip s)` |
| `StreamWire.record`/`apply`/`late` | **open** (§6) | reduce to `Bridge.Debug.cev_bridge`/`apply_bridge`/`late_bridge` + `BufRel` slot |
| `CoreInputBus` | hypothesis (W2 owns it) | — |

Axioms: `propext`, `Classical.choice`, `Quot.sound`.  `p0_open_served`,
`hostReq_open_served`, `stream_served` add only the **pre-existing**
`Mem.grants_exclusive` `bv_decide` certificates.  The `ExecInv` chain
(`execInv_*`, `pause_*`, `disp_*`, `xvrv_of_step`) is certificate-free; the two
`decide` lemmas `selIdx_bit`, `bitOf_winOf` are kernel reductions (no
`native_decide`, no extra axioms).

## 2. `execInv_step`: what is proved and how

```lean
structure ExecInv (s : State) : Prop where
  xtLt    : ∀ c : Fin 2, (s.cores[c.val].xt).toNat < 6
  ready   : ∀ c, (xv || rv = true) → (threadAt s (xt c).toNat).ready = false
  running : ∀ c, (xv || rv = true) → (threadAt s (xt c).toNat).running = true
  sep     : ∀ c c', c ≠ c' → (xv || rv = true) → (xv' || rv' = true) → xt c ≠ xt c'
```

*The reset branch* of `step` is the reset product (`resetChip`), where `XV = RV =
false` at both cores, so all four fields are vacuous (`simp [resetChip,
resetState]`).

*The active branch*, frozen (`s.freeze.frz = true`): `Core.frz_holds` keeps
`XV`/`RV`/`XT` (`activeStep_core_{xv,rv,xt}_frz`), and `Core.frz_no_fetch` plus
the `!FRZ` gates in `Step.threadIn` make `disp`, `pause` and `trig` false for
every thread (`threadIn_frz`).  Hence `READY`/`RUNNING` are unchanged
(`thread_step_frz_ready`/`_running`) and the invariant is the old one.

*The active branch, unfrozen*, for core `c` with `cs = s.cores[c]`,
`i = coreIn s pin c`, `cb = (c.val == 1)`:

* `XT' = if disp then dispE else cs.xt` (`activeStep_core_xt`), and
  `dispE.toNat < 6` unconditionally (`Core.dispE_toNat_le_five`), so `xtLt`
  follows by cases on `disp`;
* **dispatch**: `XT' = dispE`.  The dispatched thread is `READY`
  (`disp_ready_cut`, from `cand = tReady &&& mine &&& runG`, the one-hot chain
  and `packBools`), so the thread step clears `READY` and sets `RUNNING`; a pause
  of the same thread is impossible because a paused executing thread is *not*
  `READY` (`pause_not_ready`, from `pause_pse` + `ExecInv.ready`) while a
  dispatched one is;
* **no dispatch**: `XT' = cs.xt`, and `XV' ‖ RV'` forces `XV ‖ RV`
  (`xvrv_of_step`: `XV' = load` needs `RV`, `RV' = jmp ‖ load` and `jmp` needs
  `XV`).  `ExecInv.ready`/`running` give the thread's state, `accept` is blocked
  by `RUNNING`, and a pause of that thread is excluded: from its own core `pse`
  kills `load`/`jmp` (contradicting `XV' ‖ RV'`), from the other core `sep`
  applies (`not_pause_exec`);
* **`sep`**: two dispatching cores pick different threads because the candidate
  bit of a dispatch is a `mine` bit (`cand_mine_bit`) and `mine cb = if cb then
  CORE else ~~~CORE` (`mine_bit_cb`, `disp_core_bit`, `dispE_sep`,
  `fin2_eq_of_beq_eq`); a dispatching and a non-dispatching core would share a
  thread that is both `READY` (dispatch) and not (`ExecInv.ready`).

`execInv_step` therefore has **no** wiring hypothesis and `execInv_trace` is
unconditional.  Moreover the field itself is a purely cut-level fact once
`ExecInv` holds: a paused thread is the pausing core's executing thread
(`pause_pse`) and hence not `READY`, while a dispatched thread is `READY` from
the candidate mask alone (`threadIn_disp_ready` + `disp_ready_cut`), so

```lean
theorem ccw_pauseDisp_cut (s : State) (pin : Machine.PinIn) (hinv : ExecInv s) :
    ∀ t : Fin 6, Not ((threadIn s pin t.val).pause = true ∧ (threadIn s pin t.val).disp = true)
theorem ccw_pauseDisp_trace_cut (pins) (cont) (n) (pin) : ∀ t : Fin 6, …   -- at cutStateAt
```

discharge `WireAgree.pauseDisp` with **no** `ChipRel`, `Inv`, `CoreInputBus` or
`hJGTab` hypothesis.  `ccw_pauseDisp` (the `ChipRel`-based round-a form) and its
trace corollary `ccw_pauseDisp_trace` are kept for the consumers that already
carry those hypotheses.

Two proof-side notes, in case a later refactor trips on them: `Vector` Nat
indexing is `v[i]'h`, so projections after a step must be stated with `[c.val]`
(not the `Fin` index); and `Bool.and_eq_true` is an equality of propositions in
core (use `Bool.and_eq_true_iff` when `.mp` is wanted).

## 3. The one-cycle landing lag

```lean
def LandingRel (s : State) : Prop :=
  ((s.cont.ramOwner == 3) = (s.p0.land && !s.freeze.frzd)) ∧
  (s.p0.land = true → s.cont.ramLane = s.p0.landLane) ∧
  (∀ k < 2, (s.cont.ramOwner == k + 1) = ((streamAt s k).ld && !s.freeze.frzd))
```

**Finding (unconditional `p0_open_lane` is false).**  The machine's `ramLane'`
is the **served read's** lane (`runStep`: `owner' = match req with | .rd _ l =>
(served, l) | _ => (0,0)`), so a served *stream* read overwrites it with the
stream's lane, while `Mem.landLaneNext` latches `lane PTR` on **every unfrozen
cycle** (`Mem.lean`).  After a stream read with `PTR ≠` the stream address the
two registers differ; the guarded form (`p0.land = true → ramLane = landLane`) is
what `p0Next` actually needs, and that is what is proved.

`landingRel_reset` needed `Mem.resetState`/`CoreCtl.freezeReset`/`Stream.resetState`
added to `simp` and a case split on `k` for `streamAt`: `streamAt` is defined by
pattern matching on `Nat`, so it does not reduce at a variable index.

## 4. `landingRel_step` (open)

The served side is now available: `contents_open_served`/`contents_open_req`
(§5) give `mhcOwner m pin = mhcOwner (absChip s) pin`, so
`(Machine.step m pin).ramOwner = mhcOwner (absChip s) pin` through
`MemHostCfg.step_ram`.  The remaining steps of the recipe are:

* `mhcOwner = 3` iff the served request is P0's `.rd`, i.e. `Mem.fetching s.p0`
  (`Bridge.Mem.p0_fetch_req`, `fetchOf_absP0`, `Inv.reqNeThree`);
* for the streams, `mhcOwner = k+1` iff the stream's request is a `.rd` (mode
  transmit/replay) and the cut's `ldNext` is `rq && gnt` in exactly those modes,
  plus the cut invariant `ld k → mode k ∈ {0,3}` (needed because `MODE` is read
  live — AMBIG 15);
* `Mem.landNext = if !frz then grantP0 && fetching else land` and
  `CoreCtl.freezeStep` (`frzd' = if resetN then frz else false`) then close both
  sides.

Not attempted this round.

## 5. The contents congruence: `contents_open_served` and `contents_open_req`

`premise_contents` compares the machine's memory/config path at `m` with the same
path at the canonical abstraction `absChip s` (`contentsNext` is
`runStep (absChip s)`).  Both `mhcServed` and `mhcReq` are `rfl`-reductions of
`machServed`/the stream requests (`mhcServed_eq_machServed`, `mhcCbs_eq_machCbs`),
so the arbiter argument of `ccw_served` can be replayed at `absChip s` with the
`absChip` readings in place of `ChipRel` clauses:

* `absMode_eq` — `machMode (absChip s) k = modeOf (k == 0) (streamIn s pin k)`:
  `absChip`'s `cfg`/`dbg` are the cut's, `streamIn`'s mode bit is
  `(cfgView s.cont.cfg).streams[k].rx` (`streamIn_cfgMode`), and
  `capEn = cen && !replay` makes the second branch irrelevant while `replay`;
* `has_p0_abs`, `has_host_abs`, `has_sreq_zero_abs`, `has_sreq_one_abs` — the
  four presence bits at `absChip` (the `has_*` lemmas replayed with
  `(absChip s).p0.req = reqOf s.p0`, `(absChip s).host.req = absSlot s.p0` and
  `AbsRelB` reflexivity);
* `machServed_abs : machServed (absChip s) = servedIndex s.p0 (memIn s pin)`,
  the `ccw_served` proof verbatim with those four facts.

`contents_open_served` then chains
`mhcServed m pin = machServed m = servedIndex … = machServed (absChip s) =
mhcServed (absChip s) pin`, with `ccw_served` at `m` (so it keeps `hrel`,
`hinv` and the stream-mode wiring `hmode`) and `machServed_abs` at `absChip s`.

`contents_open_req` needs the four entries of `mhcReqs` to agree:

* `p0Req_congr` / `hostReq_congr` are exact (`P0Rel.req`/`.ptr`,
  `ChipRel.hostReq`);
* `streamReq_congr` reduces `Machine.streamReq` to `(ba, rq, pv, pend)` and,
  for mode 2 (`wrWord`), `wb`.  `mhcModesReq_abs0/1` feeds it `AbsRelB`'s
  projections and `BufRel.wb_of_wv`; the latter needs
  `hwv : (streamAt s k).pv = true → (streamAt s k).wv = true`, a cut-side
  invariant of the capture buffer that is *not* in `Inv` — this is the only
  extra hypothesis of the theorem.  (Mode 1 needs `pend`, mode 0/3 need `rq`,
  and `ba`; all are pinned by `AbsRelB`.)

`contents_open_req` is then `mhcReq`'s `getD` at `served - 1 < 4`
(`servedIndex_le_four`) with the shared served index.

## 6. `contents_open_cbs` (open)

`mhcCbs_eq_machCbs` reduces the target to `machCbs m = machCbs (absChip s)`,
i.e. a `Machine.coreComb` congruence between the two machine states.  Both are
related to the *same* cut state, but `coreComb` reads several clauses of
`ChipRel` that are guarded rather than equal: `IR` only while `XV`, the replay
buffer `WB` only under `BufRel` guards, the bank image only through `BankRel`.
The bundle also has to be compared field by field (`moves : List Move` needs
`srcVal` congruence over the whole guard/source vector, `npc`/`taken` need
`guardVal`, `dispAddr` needs the watcher address, plus `threads[xt].armed`).
That is the `CoreUnits.core_next_congr`-style case split lifted from
`coreNext` to `coreComb`; it was not attempted this round.


## 7. `StreamWire` `record`/`apply`/`late` (open)

Not attempted.  Remaining obligations: `real` (unfrozen), the `DC` relation
(`DbgRel.dc`), the first replay slot `(vget m.streams 0).wb` (only `BufRel`-
guarded), and the pin level (`Bridge.Debug.level_toNat`).  With those,
`Bridge.Debug.apply_bridge`/`late_bridge` give `apply`/`late`, and `cev_bridge`
gives `record`'s event and `{DC, PIN}`.

## 8. The stream invariants (both false) and the sharpened request congruence

The two cut-level stream facts the contents congruence pointed at are **not**
invariants of the design.  They are refuted at the `Stream` cut, i.e. by the
transition system that `ChipCut.streamIn` feeds:

* `pv -> wv`: `Stream.push` (`cen && capPush && !END`) sets `PV` in `pvNext`,
  while capture mode leaves `WV` alone (`wvNext`'s last branch is `s.wv`).  One
  push from `Stream.resetState` suffices: `streamInv_pv_wv_false`.  (In capture
  mode `PV` means "`WB` waits for its write", not "the window holds a word";
  `WV` is the transmit/replay validity.)
* `ld -> mode in {0,3}`: `LD` is set on a served read in transmit/replay and is
  *held* in the receive and capture branches of `Stream.ldNext`, while the mode
  is live (config byte plus `CEN`/`RPL`).  A transmit cycle with a granted read
  followed by a receive cycle gives `LD = 1` with mode 1:
  `streamInv_ld_mode_false` (two cycles from `Stream.resetState`, `ldSeq`).
  The same held `LD` is what breaks `LandingRel`'s stream clause (§9).

What the mode-2 (`capture`) `wrWord` request actually reads is `WB`, and
`BufRel` relates `WB` only while `WV` (and `WV` is false in capture mode, as
above).  So the sound statement takes the unguarded `WB` agreement:

```lean
theorem contents_open_req_wb (s m pin) (hrel : ChipRel s m) (hinv : Inv s)
    (hmode : forall k, machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val))
    (hwb : forall k, (streamAt s k.val).pv = true -> m.streams[k].wb = (streamAt s k.val).wb) :
    mhcReq m pin = mhcReq (absChip s) pin
```

with `mhcModesReq_abs_wb` (+ `_wb0`/`_wb1`) as the entry-level form.  This is
strictly stronger than the round-d `contents_open_req` (which derives `hwb`
from `hwv` + `BufRel.wb_of_wv`, hence rests on a false premise).  Closing the
gap properly means extending `Bridge.StreamB.BufRel`'s capture branch with the
`PV -> WB` clause (or proving `WB` agreement for all reachable related pairs);
that is a bridge change, not a ChipCut change.

## 9. `LandingRel`: the P0 half is an invariant, the stream half is not

`LandingP0 s : (s.cont.ramOwner == 3) = (s.p0.land && !s.freeze.frzd)` is proved
at reset (`landingP0_reset`), after every active cycle (`landingP0_active`,
frozen included), after every product step (`landingP0_step`) and along the
trace (`landingP0_trace`, using `Proof.inv_trace`), hence `p0_open_land_trace`:

```lean
theorem p0_open_land_trace (pins cont) (h0 : cont.ramOwner = 0) (n) (m) (pin)
    (hrel : ChipRel (cutStateAt pins (resetState cont) n) m) :
    (m.ramOwner == 3) = ((cutStateAt pins (resetState cont) n).p0.land &&
      !(cutStateAt pins (resetState cont) n).freeze.frzd)
```

The proof is `mhcOwner_three` (owner 3 iff the served entry is a read, with
`arbiter_le_four`), `p0_open_served_abs` (`served == 3` iff `grantP0` at
`absChip s`), `p0Req_fetch_iff` (`p0Req (absP0 s.p0)` is a read iff
`Mem.fetching`), `landingP0_abs` (`grantP0 && fetching`), and the
`Mem.landNext`/`CoreCtl.freezeStep` algebra.

**The stream clause is not preserved.**  `(ramOwner' == k+1)` records the
*served* `.rd` of the cycle, while `ld'` is the `LD` register, which the receive
and capture branches of `Stream.ldNext` hold.  A cycle whose mode switches from
transmit to receive (config write) leaves `ld' = 1` with `mode = 1`, so
`ramOwner' != k+1` while `ld' && !frzd` is true - the equality fails.  That is
exactly `streamInv_ld_mode_false` (§8), so no chip-level proof of
`stream_landNow`'s step exists.  The P0 lane clause (`p0_open_lane`) is *not*
refuted; its step only needs the lane arithmetic
`bv 2 (ptr.toNat % 4) = truncate 2 ptr` (a `decide`-able `BitVec` identity) and
`Mem.landLaneNext`; it was left for a later round.

## 10. `hmode` is `StreamWire.mode`

The `hmode` hypothesis of `ccw_served`/`contents_open_served` is *literally*
`StreamDbg.StreamWire`'s first field:

```lean
-- StreamDbg.StreamWire:
mode : forall k : Fin 2, machMode m k = Bridge.StreamB.modeOf (k.val == 0) (streamIn s pin k.val)
```

so it is not an extra assumption beyond the stream wiring hypothesis.  The two
wrappers `ccw_served_of_wire` and `contents_open_served_of_wire` take the whole
`StreamWire` and pass `hwire.mode`, and `StreamWire.mode`/`.input` are what
`premise_streams` already consumes.  At `absChip s` it is a theorem
(`absMode_eq`), not a hypothesis, which is why `contents_open_served` has no
mode hypothesis on the abstraction side.

## 11. The stream mode-quiet premise and the `LD`-mode invariant

`LandingRel`'s stream clause needs `LD` to be set only in transmit (0) or replay
(3) cycles.  The raw cut does not satisfy that (§8), and the SPEC's escape clause
(§9a.13; §12.4) is a contract, so it is one named premise:

```lean
def stream_mode_quiet (s : State) (pin : Machine.PinIn) : Prop :=
  forall k : Fin 2,
    stateMode (step s pin) k != stateMode s k ->
      (streamAt s k.val).ld = false ∧ (streamAt s k.val).rq = false
```

* **`stateMode`** is the cut-side effective mode as a pure state function (config
  `RX` plus the debug `CEN`/`RPL` registers).  `stateMode_eq : stateMode s k =
  machMode (absChip s) k` is proved through the `rfl` projections
  `absChip_cfg`/`absChip_dbg_val`, so no proof unfolds `absChip` on a stepped
  state; `stateMode_branch` rewrites it into the `Stream` branch chain
  (`rpl -> 3`, `cen -> 2`, `txMode -> 0`, else 1).
* The clause says: **no mode change while a read is outstanding or pending**
  (`ld` and `rq` both clear).  A host rewind during a transfer is *not* excluded
  and must not be: the machine reads `i.landNow` only under the stream's own
  `s.ld` (`Machine/Stream.lean` 86/129/155) and `Stream.ldNext` clears `LD` on a
  rewind, so such a landing is unobservable and is handled by the `LD`-gated
  clause (§13).
* Proved: `ldNext_true`/`ldNext_mode` (the branch algebra: a true `LD` transition
  is a held `LD` or a served read in a transmit/replay branch, and under the
  premise the next mode stays out of {1,2}), and the invariant

```lean
def ldModeInv (s : State) : Prop :=
  forall k : Fin 2, (streamAt s k.val).ld = true -> stateMode s k != 1 ∧ stateMode s k != 2
```

  at reset (`ldModeInv_reset`), after every cycle (`ldModeInv_step`, both the
  active and the reset branch) and along `cutStateAt` (`ldModeInv_trace`, with
  `stream_mode_quiet` at every cycle).

## 12. The P0 landing lane

`p0_open_lane`'s *unguarded* statement (`land = true -> ramLane = landLane`) is
not an invariant: in a frozen cycle `Mem.landNext` holds `land`, `Mem.landLaneNext`
holds `landLane`, but `contentsNext` overwrites `ramLane` with the frozen cycle's
served read (the host's `.rd`).  The guard `!FRZD` is what the consumer has
(`p0Next` reads the lane only when `ramOwner == 3`, and `ramOwner == 3` implies
`grantP0`, hence `!FRZ`), so the invariant carries it:

```lean
def laneInv (s : State) : Prop :=
  s.p0.land = true -> s.freeze.frzd = false -> s.cont.ramLane = s.p0.landLane
```

| theorem | statement |
|---|---|
| `lane_bv` | `bv 2 (x.toNat % 4) = BitVec.truncate 2 x` (`x : BitVec 11`, by `decide`) |
| `mhcLaneN_abs` | `grantP0 -> fetching -> mhcLaneN (absChip s) pin = s.p0.ptr.toNat % 4` |
| `laneInv_reset` / `laneInv_active` / `laneInv_step` | reset, active (frozen + unfrozen), both branches |
| `laneInv_trace` | `forall n, laneInv (cutStateAt pins (resetState cont) n)` |
| `p0_open_lane_trace` | guarded `p0_open_lane` at every trace cycle (`ChipRel.ramLane`) |

## 13. The LD-gated stream clause of `LandingRel`

The raw clause `(ramOwner == k+1) = (ld && !FRZD)` fails for two reasons (§8,
§9): a rewind clears `LD` while the machine still records the served `.rd`,
and a mode switch holds `LD` into a receive/capture cycle.  The machine consumes
`i.landNow` only under the stream's own `s.ld`, so the clause is stated with that
gate:

```lean
def LandingStream (s : State) : Prop :=
  forall k : Fin 2, (streamAt s k.val).ld = true ->
    ((s.cont.ramOwner == k.val + 1) = !s.freeze.frzd)

theorem stream_landNow_ld (s m pin) (hrel : ChipRel s m) (hland : LandingStream s)
    (k : Fin 2) (hld : (streamAt s k.val).ld = true) :
    (m.ramOwner == k.val + 1) = !(memIn s pin).frzd
```

| theorem | statement |
|---|---|
| `mhcOwner_eq` | `(mhcOwner m pin == k+1) = (mhcServed m pin == k+1 && isRd (entry k))` |
| `servedIndex_gnt` | `(servedIndex == k+1) = streamGnt s pin k` |
| `machSreq_isRd` | a machine stream request is a read iff the mode is not 1/2 and `RQ` is up |
| `ldNext_frz`, `ldNext_cen`, `ldNext_rx`, `ldNext_rpl`, `ldNext_tx` | the five `Stream.ldNext` projections (hold / set) |
| `landingStream_active`, `landingStream_step`, `landingStream_trace` | the clause at reset, after every cycle, along `cutStateAt` |
| `stream_landNow_ld`, `stream_landNow_ld_trace` | the restated `stream_landNow` at a state / on every trace cycle |

The proof of `landingStream_active` splits on the `ldNext` branch: a granted read
in transmit/replay makes the served entry stream `k` with a `.rd` (so owner
`k+1` and `!FRZD`); a frozen hold gives owner `!= k+1` because `grantS0`/`grantS1`
carry `!FRZ`; and the receive/capture hold branches are impossible by
`ldModeInv` (the mode would be 1 or 2 with `LD` up).  The rewind case needs no
assumption: `ldNext` is `false` there, so the gate is vacuous.

## 14. Reproduce

```powershell
cd lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.CoreCombWire          # -DwarningAsError=true
lake env lean ..\..\..\data\raw\lean_chipcut_wire_corecomb_v4_20261121\axioms.lean
cd ..
git diff --quiet HEAD -- src
```
