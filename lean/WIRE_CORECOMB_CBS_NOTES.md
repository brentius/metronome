# `contents_open_cbs` and the stream `record`/`apply`/`late` sub-fields

File: `lean/Metronome/ChipCut/Discharge/CoreCombCbs.lean`
(namespace `Metronome.ChipCut.Discharge`).  Lean 4.35.0, core libraries only,
`lake build Metronome.ChipCut.Discharge.CoreCombCbs` with `-DwarningAsError=true`
(from `lakefile.toml`; only `linter.unusedVariables`/`linter.deprecated`/
`linter.unusedSimpArgs` disabled).  No `sorry`, no `native_decide`, no `admit`.
Evidence: `data/raw/lean_chipcut_wire_corecomb_cbs_v4_20261122/`.

This closes the two wiring items left open in `WIRE_CORECOMB_NOTES.md` §6/§7.
One of them (`contents_open_cbs`, the whole-bundle equality) turns out to be
**false**; the useful projection of it is proved instead.

---

## 1. Result table

| field | status | theorem / counterexample |
|---|---|---|
| `memhostcfg.contents_open_cbs` (whole `CoreComb` equality) | **false** | `contents_open_cbs_counterexample` (`ChipRel`/`Inv`/`runRst` state triple, `taken` is `1` vs `0`) |
| the five fields `coreNext` reads (`load`, `jmp`, `disp`, `dispThread` under `disp`, `fetch`) | **discharged** from `Inv` + `AbsInv` (round 2) | `contents_open_proj_abs` |
| the same, with the canonical-abstraction relation named | **discharged** modulo `hrelA` | `contents_open_proj` |
| `ContentsEq.mout` from `fetch` alone | **discharged** modulo the `fetch` congruence | `contents_mout_of_fetch` |
| cut-side reachable invariant `AbsInv` | **discharged** (reset, step, trace) | `absInv_reset`, `absInv_step`, `absInv_trace` |
| `Inv s → AbsInv s → ChipRel s (absChip s)` | **false as stated** (bank) | `chipRel_absChip_needs_bank`; the true forms are `chipRel_absChip` (bank from `ChipRel.bank`) and `chipRel_absChip_of_bank` |
| `StreamWire.record` | **discharged, unconditional** | `stream_record_eq` (`captureRecord_bridge`) |
| `StreamWire.cev` (the gated capture edge) | **discharged, unconditional** | `stream_cev_eq` (`machCev_bridge`) |
| `StreamWire.apply` | **discharged, unconditional** | `stream_apply_eq` (`machApplyLate_bridge`) |
| `StreamWire.late` | **discharged, unconditional** | `stream_late_eq` (`machApplyLate_bridge`) |

Axioms: `propext`, `Classical.choice`, `Quot.sound`; `contents_open_proj`
additionally inherits `GuardSrc`'s existing `bv_decide` certificates (see
`commands.log`).  The two kernel `decide` lemmas (`taken_irBroken`,
`taken_absChip`) add no axiom: they are plain reductions.

### The exact `StreamWire` statements

`StreamDbg.StreamWire` bundles the stream input as one `input` field
(`machStreamIn m k = absInOf k …`).  The three sub-fields this task asked for are
the `record`/`apply`/`late` projections of that record, with

```lean
absInOf k s i = Bridge.StreamB.absIn (k.val == 0) s (gatedIn k i)
```

which sets `record := i.capRec.toNat`, `apply := (k==0) && i.replayApply`,
`late := (k==0) && i.replayLate`:

```lean
theorem stream_record_eq (s m pin) (hrel : ChipRel s m) (k : Fin 2) :
    (machStreamIn m k).record = (absInOf k (streamAt s k.val) (streamIn s pin k.val)).record
theorem stream_apply_eq  … : (machStreamIn m k).apply  = (absInOf …).apply
theorem stream_late_eq   … : (machStreamIn m k).late   = (absInOf …).late
theorem stream_cev_eq    … : (machStreamIn m k).cev    = (absInOf …).cev
```

assembled as `streamWire_record_apply_late : (∀k, …record) ∧ (∀k, …apply) ∧ (∀k, …late)`.

---

## 2. Why the whole-bundle equality is false

`Machine.CoreComb` has eleven fields.  `taken` and `npc` decode `IR`
**unconditionally**:

```lean
let jm := insnField ir FIELD_jmode
let taken := jm == JMODE_always || (jm == JMODE_if && jc) || (jm == JMODE_ifnot && !jc)
let npc := if taken then imm else cs.fpc.toNat
```

while `ChipRel.CoreRegsRel` pins `IR` only while `XV` (the cut captures the
program-memory output in every unfrozen cycle, the machine only on `load`, see
`Rel.lean` and `Core.lean`'s "IR capture").  So in an `XV = 0` cycle the two
`IR` registers are genuinely free, and `taken`/`npc` read them.

Witness (`contents_open_cbs_counterexample`):

* `s := cbsWitnessState Contents.init` — the power-on product with the reset
  flop pair set (`{resetState … with rst := {rstM := true, rstQ := true}}`), i.e.
  the state after two reset cycles; `Inv s` by `inv_reset`'s fields and
  `runRst s cbsWitnessPin = true`.
* `m := irBroken s 0xA` — `absChip s` with core 0's `IR` replaced by `0xA`
  (`JMODE = 1`, `IMM = 1`).  `ChipRel s m` by `chipRel_abs_rst` (the relation at
  the power-on state, transported across the reset flop pair) followed by
  `chipRel_ir_broken` (the weakened `IR` clause is vacuous at `XV = 0`).
* `(mhcCbs m pin)[0].taken = true` (`taken_irBroken`) but
  `(mhcCbs (absChip s) pin)[0].taken = false` (`taken_absChip`), both by kernel
  `decide`; `Bool.noConfusion` closes the refutation.

So `contents_open_cbs` cannot be a hypothesis of `premise_contents`: no
strengthening of the wiring hypotheses that leaves the relation as it stands can
prove it.  (The cut-side `IR` is only observable through `XV`, which is exactly
why the bridges use `sIr` and `core_next_ir_irrel`.)

## 3. What *is* provable: the projection `coreNext` reads

`Machine.coreNext`'s `mout` equation is

```lean
mout := match word with some w => bv 64 w | none => cs.mout
```

with `word = cb.fetch.map (progWord cs)`: it does not read any other bundle
field (`coreNext_mout_congr'`).  The state transition reads `load`, `jmp`,
`disp`, `dispThread` (under `disp`) and `fetch`; those five are congruent
(`contents_open_proj`), by routing **both** machine states through the cut core:

* `coreFetch_cut`/`coreJmp_cut`/`coreLoad_cut`/`coreDisp_cut` instantiate
  `Bridge.Core.fetch_bridge`/`jmp_bridge`/`load_bridge`/`disp_bridge` at `m`
  (through `rel_of_bus`) and rewrite the cut state `sIr s m c` to `s.cores[c]`
  (`core_jmp_sIr`, `core_load_sIr`, `core_disp_sIr`, `core_fetchEn_sIr`,
  `core_fetchAddr_sIr`).  The `sIr` and `s.cores[c]` states differ only in `IR`;
  at `XV = 0` that is unobservable (`core_ir_irrel`), at `XV = 1` the relation
  pins `IR`.  `dispThread` uses `Bridge.Core.dispE_sIr` (an `rfl`) and
  `CoreUnits.coreDispThread_eq`.
* The same four lemmas are re-instantiated at `absChip s`, where
  `sIr s (absChip s) c = s.cores[c]` (`sIr_absChip`), so both sides are the
  *same* cut expression.
* The guard/source buses come from `GuardSrc.coreInputBus` at both states.

`contents_mout_of_fetch` then repeats `premise_contents`' first bullet with
`contents_open_cbs` replaced by its `fetch` component, giving
`ContentsEq.mout` for every core.

### The one remaining hypothesis: `hrelA : ChipRel s (absChip s)` — now discharged

Round 2 defines the cut-side reachable invariant `AbsInv` (§6), proves
`absInv_reset`/`absInv_step`/`absInv_trace` and `chipRel_absChip`, and restates
the projection as `contents_open_proj_abs`, whose hypotheses are exactly
`ChipRel s m`, `Inv s`, `runRst s pin = true`, `AbsInv s` and the global tables
(`hG`, `hS`, `hJGTab`).  The two shape clauses are:

1. **host** (`HostShape s.hostCmd`): the byte state is one of the five encoded
   states; the ignored transaction carries a non-command history byte; and
   `isRd` holds **exactly** for a read command byte (`↔`, because
   `Bridge.Host.LinkRel.isRd` is an iff); plus `HostCmd.Tagged` (`HostCmd.lean`).
   The `↔` direction `cmd = CMD_READ → isRd` needed a new one-step lemma
   (`isRdNext_back`): in `ST_CMD` the two registers only change together at the
   command-byte completion, and `CS_N` high holds both.
2. **streams** (`AbsInv.s0`/`s1`): `¬ (RQ ∧ LD)` for each stream
   (`stream_rqLd_step`: `LD'` is clear whenever `RQ'` is set — `LD'` is `RQ ∧ GNT`
   or cleared in every unfrozen branch, and both hold in the frozen branch).

`ChipRel`'s `bank` clause is *not* part of `AbsInv` (§6.4).

## 4. The stream `record`/`apply`/`late` discharge

* `captureRecord_bridge` — `(machCevRec m).2 = (captureRecord s).toNat`, where
  `captureRecord s = s.dbgCtrl.dc ++ pinLvl s`.  `Machine.captureEvent`'s record
  is `d.dc.toNat * 2 ^ N_IN_PINS + p.lvl`; `N_IN_PINS = 13`, `DbgRel.dc` and
  `pinLvl_toNat` (GuardSrc) close it.  **No freeze hypothesis** — the record is
  not gated.
* `machCev_bridge` — `(machCevRec m).1 = Debug.Ctrl.cev s.dbgCtrl.cen
  s.dbgCtrl.replay s.freeze.frz (riseVec s) (fallVec s) s.dbgCtrl.emask`, via
  `Bridge.Debug.cev_bridge` with the level `pinLvl_toNat` and the new
  previous-level lemma `pinPrev_toNat` (the `Bridge.Debug.previous_toNat`
  analogue, same proof shape as GuardSrc's `pinLvl_toNat`), plus the `DbgRel`
  projections of `cen`/`rpl`/`emask`/`frz`.  Also unconditional.
* `machApplyLate_bridge` — the pair
  `(machApplyLate m).1/.2 = Debug.Ctrl.apply/late s.dbgCtrl.replay
  s.freeze.frz (streamAt s 0).wv s.dbgCtrl.dc (streamAt s 0).wb` from
  `Bridge.Debug.apply_bridge` with `valid := (streamAt s 0).wv` (`BufRel.wv_eq`)
  and the first replay slot as the word.  The slot's `WB` is pinned only
  **while `WV`** (`BufRel.wb_of_wv`); when `WV = 0` both `apply` and `late` are
  `false` on both sides (`replayApply_fst_wv_false`,
  `replayApply_snd_wv_false`, `ctrlApply_valid_false`, `ctrlLate_valid_false`),
  so the guarded `WB` equality is enough.  No extra hypothesis, no unfrozen
  hypothesis: the machine's `!frozen` factor and the cut's `Debug.Ctrl.apply`'s
  `!frz` factor are the same `DbgRel.frz` equality.

The `StreamIn` record then matches slot by slot because `runStep` gates
`cev`/`apply`/`late` on `k == 0` and `gatedIn` applies the same gate; `record`
and `capRec` are ungated on both sides.

## 6. `AbsInv`: the cut-side reachable invariant (round 2)

```lean
def HostShape (t : HostCmd.State) : Prop :=
  (t.phase = ST_CMD ∨ t.phase = ST_AH ∨ t.phase = ST_AL ∨ t.phase = ST_DATA
     ∨ t.phase = ST_IGN)                                        -- phaseNext_mem
  ∧ (t.phase = ST_IGN → t.cmd ≠ CMD_WRITE ∧ t.cmd ≠ CMD_READ)   -- phaseNext_ign
  ∧ ((t.isRd = true) ↔ (t.cmd = CMD_READ))                      -- isRdNext_iff
  ∧ HostCmd.Tagged t

structure AbsInv (s : State) : Prop where
  host : HostShape s.hostCmd
  s0   : ¬ ((streamAt s 0).rq = true ∧ (streamAt s 0).ld = true)   -- stream_rqLd_step
  s1   : ¬ ((streamAt s 1).rq = true ∧ (streamAt s 1).ld = true)   -- stream_rqLd_step
```

### 6.1 Items

* `absInv_reset (cont) : AbsInv (resetState cont)` — `HostCmd.resetState`
  (`phase = ST_CMD`, `isRd = false`, `cmd = 0`, `tagged_resetState`) and
  `Stream.resetState` (`rq = ld = false`).
* `absInv_step (s) (pin) (hinv : Inv s) (h : AbsInv s) : AbsInv (step s pin)` —
  both branches of `ChipCut.step`:
  * active (`runRst = true`): `(activeStep s pin).hostCmd =
    HostCmd.step s.hostCmd (hostCmdIn s pin)` (`rfl`) so `hostShape_step`
    (`phaseNext_mem`, `phaseNext_ign`, `isRdNext_iff`, `HostCmd.tagged_step`);
    streams are `Stream.step (k==0) (streamAt s k) (streamIn s pin k)` by
    `activeStep_streams`, and `stream_rqLd_step` preserves `¬(RQ ∧ LD)`.
  * reset (`runRst = false`): `resetChip` sets `hostCmd = HostCmd.resetState`
    and every stream to `Stream.resetState` (`streamAt_resetChip`).
  `Inv` is carried in the signature as requested; the clause proofs do not
  actually need it.
* `absInv_trace (pins) (cont) : ∀ n, AbsInv (cutStateAt pins (resetState cont) n)`
  — from `inv_trace`.
* `chipRel_absChip_of_bank (hinv) (habs) (hbank : BankRel s.bank s.cont.cfg) :
  ChipRel s (absChip s)` — all non-bank clauses; the host `LinkRel` is at
  `s.hostRead.toHostCmd s.hostCmd.cmd`, rewritten to `s.hostCmd` by
  `HostPins.toHostCmd_agrees` (so `Inv` *is* used here), the `rack` clause is
  `Agrees.rack` and the `isRd` clause is `HostShape`'s iff transported along
  `cmdOf_eq_two`.  `sync` uses `split16` (the 16-bit byte split), `streams` uses
  `absRelB_abs` plus `AbsInv.s0/s1`, and `p0`/`cw`/`units`/`ctrl`/`dbg`/lines/
  threads/cores are reflexive.
* `chipRel_absChip (hrel : ChipRel s m) (hinv) (habs) : ChipRel s (absChip s)` —
  the latch-image contract from `hrel.bank` transported along `hrel.cfg`.
* `coreInputBus_abs` / `contents_open_proj_abs` — the `CoreInputBus` at the
  abstraction and `contents_open_proj` with `hrelA` replaced by `AbsInv`.

### 6.2 The `isRd` clause is an **iff**

`Bridge.Host.LinkRel.isRd` is `(s.isRd = true) ↔ (m.host.cmd = 2)`, so the
`←` direction `cmd = 0x03 → isRd` is needed.  It is a genuine invariant
(`isRdNext_back`): while `CS_N` is high both registers hold; in `ST_CMD` a
completed command byte sets `isRd' = (byteIn == CMD_READ)` and
`cmd' = byteIn` together; otherwise both hold.  Note the shell output of the
`HostCmd` sources can render `↔` as a space — read `LinkRel` in
`Bridge/Host.lean` for the exact statement.

### 6.3 Preservation lemmas and their shape notes

`phaseNext_mem`/`phaseNext_ign`/`isRdNext_imp`/`isRdNext_back` are case
analyses on `Reset`/`CS_N`/`completing`/`phase = ST_CMD`; `phaseNext_ign` takes
the previous state's ignored-transaction fact (the phase does not move in
`ST_IGN`).  `stream_rqLd_step` is one `bv_decide` after unfolding `rqNext`/
`ldNext` (a new `bv_decide` certificate; `bv_decide` is the project's standard
tool, no `native_decide`).

A Lean footgun worth recording: simp normalises `(x == y)` to `x = y#w` (the
`BitVec.ofNat` literal), so `by_cases` conditions compared with `==` should be
stated in the `0#3`/`2#8`/`3#8` literal form when the branch proof uses the
hypothesis against a goal that simp has already normalised.

### 6.4 The `bank` clause: `chipRel_absChip` cannot drop `hrel`

`ChipRel`'s `bank` clause relates the cut's latch bank to the **machine's**
configuration image; `Inv` and `AbsInv` mention neither.  So the
`hrel`-free form `Inv s → AbsInv s → ChipRel s (absChip s)` is **false**:

```lean
theorem chipRel_absChip_needs_bank :
    ∃ s : State, Inv s ∧ AbsInv s ∧ ¬ ChipRel s (absChip s)
```

witness `bankBroken` = the power-on state with a one-byte `0xFF` configuration
image and a fully masked zero latch (the latch reads `0`, the image byte reads
`255`); `Inv`/`AbsInv` are bank-independent (`bankBroken_inv`,
`bankBroken_absInv`) and `bankBroken_not_bankRel` is the clause failure.  This is
the same stated latch-image contract `MemHostCfg.premise_bank` carries as
`bank_open_mask`/`bank_open_cfg`/`bank_open_size`; `chipRel_absChip` takes it
from the related state (`hrel.bank`, `hrel.cfg`), which is available in
`premise_contents`' context, so nothing is lost for the pipeline.

## 7. Reproduce

```powershell
cd lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.CoreCombCbs          # -DwarningAsError=true
lake env lean ..\..\..\data\raw\lean_chipcut_wire_corecomb_cbs_v4_20261122\axioms.lean
cd ..
git diff --quiet HEAD -- src
```
