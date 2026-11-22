# Discharge: the `Glue` premises (`sync`, `ctrl`, `out`, `oen`)

New file: `Metronome/ChipCut/Discharge/Glue.lean` (namespace
`Metronome.ChipCut.Discharge`).  Nothing outside it was edited; `src/` is
unchanged (`git diff --quiet HEAD -- src` exit 0).

Status: `lake build Metronome.ChipCut.Discharge.Glue` exits 0 with the lakefile's
`-DwarningAsError=true` (Lean 4.35.0, core libraries only), fresh elaboration
6-8 s, and `lake build Metronome.ChipCut` still exits 0.  No `sorry`, `admit` or
`native_decide` (the only occurrence of the word is the sentence saying there is
none).  Evidence: `data/raw/lean_chipcut_discharge_glue_v4_20261121/`
(`commands.log`, `axioms.lean`, `axioms.txt`).

## Result

| field | theorem | status |
|---|---|---|
| `sync` | `premise_sync` | **unconditional** |
| `ctrl` | `premise_ctrl` | under the named hypothesis `ctrl_open_move_fabric` (five input-level move-fabric/pointer facts, below) |
| `out` | `premise_out` | **unconditional** |
| `oen` | `premise_oen` | **unconditional** |

`premise_ctrl` breaks into parts that *are* unconditional and are proved here:

* the nine control/mailbox registers (`run`, `irqen`, `inb`, `inv`, `invp`,
  `outb`, `outv`, `db`, `irq`) through `Bridge.Glue.ctrl_bridge`, with its three
  hypotheses proved: `ctrlWr` (`hwByte (hwOf s)` is the cut's byte strobe, from
  `hwByte_hwOf`), `errTerms` (current sticky bits and the four "any" reductions
  of threads/lines/streams, from `ChipRel.ctrl` and `ChipRel.units` and the new
  `packBools` bit lemma) and `ctrlRegsRel`;
* `CONFLICT`/`MEMHAZ` through `Bridge.Moves.ctrl_conflict_bridge` /
  `ctrl_memhaz_bridge`.  Their sticky-clear side condition is now a theorem:
  `STICKY` is a one-byte `CTRL` register, so a located `STICKY` write is byte 0
  (`hostLocate_ctrl_sticky_byte`) and `nbit (hwByte … "STICKY").getD 0 k =
  stickyClear s k` (`sticky_nbit`).  The register map is checked by
  `decide` on `Machine.Tables.hostBlocks` (no `native_decide`);
* `CWOVR` through `cwovr_step`: the machine's sticky bit with the cut's queue
  drop event equals `(CoreQueue.step s.cq (cqIn s pin)).overrun`, because
  `!stickyClear 2` is `!hostClear` (`hostClear_eq`) and the two OR terms are
  commuted.  This replaces `Bridge.CfgWrite.overrun_bridge`, whose hypotheses
  `i.frz = false` and `i.coreIssue = true` hold in only part of the reachable
  cycles (a frozen cycle, or a queued write that the arbiter does not grant, has
  neither), so that bridge cannot be applied to a whole-cycle premise.

`premise_out`/`premise_oen` use `Bridge.Glue.out_bridge` with `Env` built from
the machine state.  `CvRange` is proved from the machine's two-bit `BIND`/`SEL`
decode (`cfgView_out_line/live/sel0/sel1/sel2`, `default` beyond pin 13), the
`Env.hlvl` side condition from `pinView_lvl_lt`, and the cut's packed `OutCfg` is
identified with `Bridge.Glue.outCfgOf` field by field (`outCfg_eq`): the binding
and select bytes by finite case splits on the decoded 2-bit fields
(`bind_eq`/`sel_eq`), the `COMMITTED`/`PIN`/`SEG` packings by `bv_decide`
(`comm_eq`, `pack4_eq`, `seg_eq`, re-stated for the corrected packers, which now
put item 0 in the low bits).
`premise_sync` is `SpiPins.step` against `Machine.syncNext` under
`ChipRel.sync`, i.e. the `{ui_in, uio_in}` byte split of `State.lean:209`.
`Bridge.Glue.pins_bridge` is not needed for these four fields: it states the
driven-pin projection, which `ChipCut.pins_of_rel` (`Rel.lean`) already proves.

## The finding: `ctrl`'s five input leaves are cycle move-fabric facts

`Machine.runStep` builds the control block's input record *inline* (`ctrlInTrue`
in the new file re-derives the projection; `runStep_ctrl` is `rfl`).  Three of
its five leaves are not current-register functions:

* `hostOut`/`hostInRead` — the picked `HOST.OUT` word and the "some enabled move
  reads `HOST.IN`" test, from `Machine.resolveMoves` on the cores' combinational
  move bundles;
* `conflict`/`memhaz` — the sticky *events* (two valid moves with one key; a
  `P0.D` read while `!RDY`, plus the pointer hazard `reqMove && pending &&
  !served` from `p0Next`);
* `cwovr` — the queue drop event `writeData && !accept` of `CoreQueue.step`.

The cut builds the same five from its own fabric leaves (`Glue.hostOutWrite`/
`hostOutData`, `Glue.anyRead rdHin`, `Moves.conflictOf`, `Moves.memhazEvent`,
`CoreQueue.writeData/accept`).  Both sides therefore depend on this cycle's
move fabric, guard/source vectors, pointer hazard and queue state, i.e. on the
wiring obligations of the `cores`, `units`, `p0` and `cw` premises — not on
`ChipRel`, which relates registers only.  They are carried as the named
hypothesis `ctrl_open_move_fabric` (`CtrlMoveFabric`), one equation per leaf.

Two traps worth recording:

* `Bridge.Glue.ErrTerms`' `conflict`/`memhaz` clauses are the *current sticky
  bits* (the RTL glue's `ERR` input, `project.v` 692-694), not the cycle's
  events.  Feeding them to `ctrlNext` through `ctrlInOf` would give
  `(c && !clear) || c`, so `ctrlInOf` is used for the nine registers and the
  `irq` term only, and the events come from the named hypothesis.
* `ctrlNext`'s nine non-sticky fields depend on the input record only through
  `hostOut`/`hostInRead`; `ctrlNext_host_congr` states that, which is what lets
  the `ctrl_bridge` result (stated on `ctrlInOf`) transfer to the machine's
  real input record.

## Axioms

`axioms.txt`: `premise_sync` and `premise_ctrl` depend only on `propext`,
`Classical.choice`, `Quot.sound`; `premise_out`/`premise_oen` add the
kernel-checked `bv_decide` certificates of `comm_eq`, `pack4_eq`, `seg_eq` (and,
through `out_bridge`, the pre-existing `Bridge.Glue.pack4b_*` ones).  No
`sorryAx`.

## Reproduce

```powershell
cd code/tests/lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.Glue        # exit 0, 6.5 s fresh
lake env lean ..\..\..\data\raw\lean_chipcut_discharge_glue_v4_20261121\axioms.lean
cd ../../..
git diff --quiet HEAD -- src                           # exit 0
```

## Remaining work

Discharge `ctrl_open_move_fabric`: `hostOut`/`hostInRead` need the moves bridge
on the cores' outputs (the `cores` premise family), `conflict`/`memhaz` need
that plus the pointer hazard of the `p0` bridge, and `cwovr` needs the picked
`CW` word and the queue drain/`drains` agreement of the `cw` bridge.  Nothing in
this file has to change when those are proved elsewhere: only the hypothesis is
instantiated.

Integration: the helper lemmas live in the shared namespace
`Metronome.ChipCut.Discharge` (only the four `premise_<field>` theorems and
`ctrl_open_move_fabric` are intended as the interface).  A declaration-name
sweep over the five `ChipCut/Discharge/*.lean` files found no duplicates at the
time of writing; if a later helper clashes, renaming this file's helper is
enough.
