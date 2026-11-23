# W1 (move fabric): `Metronome/ChipCut/Discharge/MoveFabric.lean`

Task: the padding/core construction of the machine's six-slot move list, `MoveBus`,
`MoveAgree`/`MoveTable`, **the group pick** (the machine's winner scan is the cut's
`pickWord`), and the consumer hypothesis fields that reduce to it (`UnitInputs`,
`CtrlMoveFabric`, `WireAgree`, `StreamWire.input`, `p0_open_move`).

Toolchain: Lean 4.35.0, core libraries only.  Acceptance: `lake build
Metronome.ChipCut.Discharge.MoveFabric` exits 0 (`-DwarningAsError=true` from
`lakefile.toml`); no `sorry`, no `native_decide`, no `admit`.

Evidence: `data/raw/lean_chipcut_wire_movefabric_v4_20261121/` — `build_final.log`
(exit 0, 13 s module rebuild), `axioms.lean`, `axioms.txt`, `chipcut_regression.log`,
`commands.log`.  `axioms.txt`: no `sorryAx`, no `Lean.trustCompiler`; the only
extra axioms are the pre-existing `bv_decide` certificates of `Bridge/Moves` /
`CoreCtl` plus one for the new `slice_makeWord_0_4`.
`lake build Metronome.ChipCut` exits 0 and `git diff --quiet HEAD -- src` is 0.

---

## 1. What is delivered (all kernel-checked)

Round a (padding / bus / table) is unchanged.  Round b/c add the **group pick** and
two consumer fields.

| group | theorem | statement (informal) |
|---|---|---|
| padding | `stepOn_null`, `resolveAux_null`, `resolveAux_filter_some`, `resolveMoves_filter_some` | a `NULL` move is the identity on the resolver state, anywhere in the list |
| padding | `foldl_filterMap_getD`, `resolveAux_filterMap_getD` | `resolveAux` over `(range 6).filterMap g` = `resolveAux` over the padded `map (getD ∘ pad)` |
| six slots | `coreComb_moves_enum`, `filterMap_six_split`, `mAllMoves_enum` | each core's `moves` list is `(range 3).filterMap (moveAt ·)`; `mAllMoves = (range 6).filterMap machSlot` |
| core | **`resolveMoves_mAllMoves`**, `resolveMoves_mAllMoves_of_chipRel`, `mWs_eq_six` | the machine resolves `mAllMoves` and the padded six slots identically; `mWs = winners of six machMove` |
| bus | **`MoveBus`** (6 fields), `moveBus_of_rel`, **`moveBus_of_chipRel`** | per-slot `en`/`dst`/`dat`/`line`/`thread`/`grp` agreement with the cut's buses |
| agree | `moveAgree_of_bus`, **`moveTable_of_bus`**, **`winners_machMove`** | `MoveAgree`/`MoveTable` for `bundleOf`, and the machine's winners = the cut's `winAt` filter, conflict = `conflictEv` |
| glue | **`ctrlMoveFabric_conflict`**, **`ctrlMoveFabric_conflict_of_chipRel`** | `CtrlIn.conflict` is `conflictOf` (the field, verbatim) |
| **pick** | `range_find?_before`, `hitsMask_eq_zero`, `winAt_of_hits`, `winAt_false_of_later_hit`, `P_hit_true`, `P_hit_false`, `scan_at_hit_T`, `scan_at_no_hit_T` | the lowest contender wins and its scan value is the cut's `Q` of the slot word |
| **pick** | **`pickScan`**, **`pickScan_mWs`** | the machine's `dstOp`-pattern scan over its winners *is* the cut's `pickWord` of the destination's write group |
| glue | **`ctrlMoveFabric_hostOut`** | `CtrlMoveFabric.hostOut` (field, verbatim) |
| units | **`unitInputs_flag_low4`** | `UnitInputs.flag` in the projected (`% 16`) form; see §5 |
| adapters | `findSome?_congr`, `findSome?_snd_map`, `findSome?_map_ext`, `findSome?_pair_ext`, `bitAt_makeWord_14`, `slice_makeWord_8_6`, `slice_makeWord_0_8`, `slice_makeWord_0_4`, `truncate_four_toNat` | scan/projection plumbing for the field statements |
| finding | `sym_data_witness`, `ctl_data_witness`, **`flag_data_witness`** | the three truncated-data fields are too strong as stated (§5) |

The group pick, verbatim:

```lean
theorem pickScan (s : State) (m : Machine.State) (pin : Machine.PinIn)
    (hbus : MoveBus s m pin) {α β : Type} (P : Machine.DstOp → Option α)
    (Q : BitVec 6 → Option α) (T : Nat → β) (G : BitVec 5)
    (hGb : (G == Moves.dgNone) = false)
    (hG0 : (G == Moves.dgLSym) = false) (hG1 : (G == Moves.dgTStop) = false)
    (hPQ : ∀ d, d < 64 → P (Machine.dstOp d) =
      (if (Moves.dgTable (BitVec.ofNat 6 d) == G) then Q (BitVec.ofNat 6 d) else none)) :
    (List.range 6).findSome? (fun q => if Moves.winAt (movBundle s pin) q then
        (P (Machine.dstOp (machMove s m pin q).dst)).map (fun a => (a, T (machMove s m pin q).v))
        else none)
      = (if (Moves.pickWord (Moves.hitsMask (mvEn s pin) (mvGrp s pin) G) (mvDst s pin)
            (mvDat s pin)).we
          then (Q (…pickWord…).dst).map (fun a => (a, T (…pickWord…).data.toNat)) else none)
```

`pickScan_mWs` is the same identity for `mWs`, from `ChipRel` + `Inv` + `hJGTab` +
`CoreInputBus` + `hgrp` + `DstKindTable` (the `premise_cores` hypotheses).

## 2. How the pick is proved

* the first hit of `(range 6).find? (hitAt ·)` (`range_find?_before` gives "all
  earlier slots are not hits"); `hitsMask` is zero when no slot hits
  (`hitsMask_eq_zero`);
* the first hit **wins**: `winAt_of_hits` via `Moves.win_of_first` +
  `contender_eq_valid_group`; every **later** hit does not win
  (`winAt_false_of_later_hit`: same key, `Moves.blocked_spec`), which is where
  `hG0`/`hG1` enter (the keyed groups `L.SYM`/`T.STOP` pick per line/thread and are
  not covered — see §4);
* at the winner `P (dstOp mv.dst) = Q slot.dst` (`P_hit_true`, from `hPQ`,
  `MoveBus.grp` and `machMove_dst`); at every other slot it is `none`
  (`P_hit_false`/`scan_at_no_hit_T`);
* `Moves.pickWord_eq_word` gives `pickWord = ⟨true, dst_k, data_k⟩` for the first
  hit, and `Moves.pickWord_none` the zero word when there is none.

The data projection `T` is a parameter because three fields compare the machine's
full data byte with a truncated cut byte (§5).

## 3. Per target field: status and exact blocker

Legend: **discharged** = the field's statement is a theorem here; **open** = the
move-fabric part is here and only the named fact is missing; **false** = refuted.

| file | field | status |
|---|---|---|
| `Glue` | `CtrlMoveFabric.conflict` | **discharged**: `ctrlMoveFabric_conflict_of_chipRel` (verbatim) |
| `Glue` | `CtrlMoveFabric.hostOut` | **discharged** modulo `hPQ` for codes 57: `ctrlMoveFabric_hostOut` (verbatim statement) |
| `CoreUnits` | `UnitInputs.flag` | **open in the exact form, discharged in the `% 16` form**: `unitInputs_flag_low4`; the exact form is false for data bytes ≥ 16 (`flag_data_witness`) |
| `Glue` | `CtrlMoveFabric.hostInRead` | **open**: needs a `src` field in `MoveBus` (`moves_bridge`'s `mv.src` slice equality) and "enabled ↔ in `mAllMoves`"; the scan itself is `Moves.anyRead (readsOf …)`, no group pick |
| `Glue` | `CtrlMoveFabric.memhaz` | **not this task**: the `P0.D` read term is the same scan shape (`Moves.memhaz_event_bridge`), the pointer hazard is the `p0` bridge's |
| `Glue` | `CtrlMoveFabric.cwovr` | **not this task**: `writeData && !accept` is the `cw`/queue bridge's (`Glue.cwovr_step`) |
| `CoreUnits` | `UnitInputs.acc`, `.reg`, `.sh`, `.shCfg`, `.cnt`, `.lf` | **open**: `pickScan_mWs` with the group's `hPQ`, which is a table over the *parsed* destination names (`R0..R3`, `SH*`, `CNT*`, `LF*`): `Machine.dstOfName` splits on `String.splitOn`, `@[irreducible]` in core, so `dstOp` does not reduce there (§6).  `acc` additionally needs `Units.Acc.opCodeOf`/`opSel` (`accIn_sel` is already in `CoreUnits`) |
| `LineThread` | `WireAgree.sym` | **false as stated** (§5): 8-bit `SymWrite.v` vs the 4-bit `symD`; the `% 16` form is the provable one, and it needs the **per-line keyed** pick (`symMask`), not `pickScan` |
| `LineThread` | `WireAgree.ctl` | **false as stated** (§5): 8-bit data vs `ctlD` (`BitVec.ofNat 3`); `% 8`, per-line keyed pick |
| `LineThread` | `WireAgree.late` | **open**: `allMoves.any (thread = t ∧ ¬armed ∧ lsym)` vs `threadIn.lateSet = slotValid q`; needs the "valid slot" part only (no group pick) plus the `L.SYM` key |
| `LineThread` | `WireAgree.stop` | **open**: `T.STOP` is a *keyed* group (per thread) — outside `pickScan`'s `hG0`/`hG1`; a keyed variant of `winnerGroup_eq_singleton` is needed |
| `StreamDbg` | `StreamWire.input` (adv, rx, ctl) | **open**: `S0`/`S1` are parsed names, so `hPQ` needs the §6 table; `adv`/`rx` are the `strobe` form (`Strobes.opg`), the ctl move is a `gw` pick |
| `MemHostCfg` | `p0_open_move` | **open**: `mhcP0Move` is a scan over `.pAl/.pAh/.pW/.pR` (fixed names, `hPQ` decidable per code) against `Bridge.Mem.mvOf (memIn s pin)`, i.e. `pickScan_mWs` with `G = dgTable 43` plus `Strobes.p0Sel`'s decode |

`hPQ` is the only missing ingredient for `hostOut`-shaped fields whose group's
destinations are the 21 fixed names: for those, `dstOp d` *does* reduce in the
kernel and `hPQ` is a `decide` over 64 codes (with `set_option
exponentiation.threshold 4096`, set at the top of the file, for `Moves.dgTable`).
It is left as a hypothesis only because the *universal* statement also covers the
parsed-name codes, where `dstOp` is stuck (§6).

## 4. The two residual hypotheses of `pickScan`

1. **`hPQ`** — the write-group/payload table of §6.
2. **`hG0`/`hG1`** — the group is neither `L.SYM` nor `T.STOP`, plus `hGb`.  The
   two keyed groups pick *per line* / *per thread*, and the cut's `symWord`/
   `threadIn` use `symMask`/`slotValid` rather than `pickWord`; they need a keyed
   singleton lemma (at most one winner per key, `Moves.winners_unique`).

## 5. Finding: `WireAgree.sym`/`ctl` and `UnitInputs.flag` are too strong

The machine keeps the **whole 8-bit** data byte of a winning move; the cut
truncates at the consumption site:

| field | machine | cut | refutation |
|---|---|---|---|
| `WireAgree.sym` | `{op, v := mv.v}` | `{op, v := (BitVec.truncate 4 …).toNat}` (`Wire.lineIn.symD`) | `sym_data_witness` |
| `WireAgree.ctl` | `some mv.v` | `some (BitVec.ofNat 3 data).toNat` (`Wire.lineIn.ctlD`) | `ctl_data_witness` |
| `UnitInputs.flag` | `some (b, mv.v)` (full byte as the flag index) | `some (v, (slice wFlags 0 4).toNat)` (`Glue.flagsIndex`) | `flag_data_witness` |

These are not RTL/machine disagreements — `Machine.stagedNext` uses `bv 4 v` and
`Machine.lineNext`/`setBit` the low bits — but the *field statements* compare the
full byte with the truncation, so they fail on any cycle whose winning
`L.SYM`/`Lk.CTL`/`FLAGS` data byte has high bits set (the byte comes from a source
port with no mask).  The delivered/provable forms are the projections

```lean
(ltLineIn m l).sym.map (fun w => (w.op, w.v % 16)) = …       -- needs the keyed pick
(mUnitsIn m pin).flag.map (fun p => (p.1, p.2 % 16)) = …     -- unitInputs_flag_low4
```

`hostOut` has no truncation (`hostOutData` is the full byte), so it is discharged
verbatim.

## 6. The parsed destination names (needed by `acc`/`reg`/`sh`/`shCfg`/`cnt`/`lf`,
streams)

`Bridge.Moves.dstOp_eq` rewrites `dstOp d` to `(Tables.dstNames[d]?).map dstOfName`;
`dstOfName` first tries a literal list (21 fixed names: `L.SYM`, `L.DBIT`,
`L.XOR`, `T.STOP`, `FLAGS.SET/CLR`, `ACC.*`, `P0.*`, `HOST.OUT`, `CW.*`) and
otherwise `parsePort` (`String.splitOn`, `@[irreducible]`).  So `dstOp` reduces in
the kernel exactly for those 21 codes, and the payload of `R0..R3`, `SH*`, `CNT*`,
`LF*`, `S*` is opaque.  The cheap closure is a table hypothesis in the
`DstKindTable` style — `∀ d < 64, payload-class (dstOp d) = cut-class d`, checked by
compiled evaluation — or the per-group `hPQ` at the assembly site (what
`hostOut`/`flag` do above).

## 7. Reproduce

```powershell
cd lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.MoveFabric     # exit 0 (13 s after an edit, 2 s cached)
lake env lean -DwarningAsError=true ..\..\..\data\raw\lean_chipcut_wire_movefabric_v4_20261121\axioms.lean
                                                       # exit 0, no sorryAx
lake build Metronome.ChipCut                           # exit 0 (regression)
cd ..
git diff --quiet HEAD -- src                           # exit 0
```

`commands.log` records the commands, exit codes and wall times.  No file outside
`Metronome/ChipCut/Discharge/MoveFabric.lean` and this note was created or edited.

## 8. Build hygiene note

The first build after the resume failed because the parallel `StreamDbg`/
`MemHostCfg` tasks were mid-edit (`Unknown identifier cfgStart_bv`,
`MemHostCfg.lean:1360` application mismatch).  Retried a few minutes later without
touching those files; they compiled and the module builds.

---

# Round b: the payload table

## 8b. **`MoveBus.src` is IN** (for W1b)

`MoveBus` now has a 7th field, added for the keyed/host-read work:

```lean
src : ∀ q, q < 6 → ∀ mv, machSlot m pin q = some mv → mv.src = (Core.slice (mvSrc s pin) (6 * q) 6).toNat
```

It is constructed in `moveBus_of_rel` (and therefore in `moveBus_of_chipRel`) from
`Bridge.Core.moves_bridge`'s `mv.src` conjunct, `mvSrc_slot` (the six-slot split of
`mvSrc s pin`, mirror of `mvDst_slot`) and the new `out_src_congr` (the `mvSrc`
analogue of `out_move_congr`: the `sIr` → cut-core transfer, `XV = 0` making the
`IR` mismatch irrelevant).  So `moveBus_of_chipRel …` gives `MoveBus s m pin` with
`en`/`dst`/`dat`/**`src`**/`line`/`thread`/`grp`; `hostInRead` can be closed by
matching `Glue.anyRead (Moves.readsOf (mvEn) (mvSrc) srcHostIn)` bit-by-bit against
`allMoves.any (srcOp = .hostIn)` (`srcOp 38 = .hostIn` is already kernel-checked,
`Bridge.Moves.srcOp_cut`).

## 9. `DstPayloadTable` (§12 of the file)

One global hypothesis, in the `DstKindTable` style, for the machine's
*destination payload* decode:

```lean
inductive Fam   -- the cut's write-group families
  | acc | flags | reg (k) | sh (k) | shCfg (k) | cnt (k) | lf (k)
  | p0 | stream (k) | lCtl (k) | hostOut
def famIn : Fam → Machine.DstOp → Bool        -- machine membership predicate
def famCode : Fam → Nat                       -- canonical code, fixes the group
def famG (f : Fam) : BitVec 5 := Moves.dgTable (BitVec.ofNat 6 (famCode f))
def PayloadGroup (P) (G) : Prop := ∀ d, d < 64 → (Moves.dgTable d == G) = P (Machine.dstOp d)
def DstPayloadTable : Prop := ∀ f : Fam, PayloadGroup (famIn f) (famG f)
theorem hPQ_of_payload : PayloadGroup P G → (payload agreement on P) → hPQ   -- §10
```

Compiled check: `decode_check_payload.lean` (`lake env lean --run …`, exit 0,
2.6 s, log in the evidence dir) — **23 families × 64 codes, 0 failures**. It also
prints the cut's real group structure, which is the finding of this round: several
write groups hold more than one destination code, so a *single-code* payload
statement (my first attempt) is false and the group-level one is the right shape:

| group | codes | | group | codes |
|---|---|---|---|---|
| 2 `FLAGS` | 5, 6 | | 12/13/14 `CNTk` | 24+k, 27+k, 30+k |
| 3 `ACC` | 7..13 | | 15/16 `LFk` | 33+k, 35+4k+b |
| 4..7 `Rk` | 14+k | | 17 `P0` | 43..46 |
| 8/9 `SHk` | 18+k, 20+k | | 18/19 `Sk` | 47+k, 49+k, 51+k |
| 10/11 `SHk.CFG` | 22+k | | 20..23 `Lk.CTL` | 53+k |
|   |   | | 24 `HOST.OUT` | 57 |

This is why the cut reads such a group's *one* `gw` word and decides the port from
the word's destination code (`shifterSel (strobe 20+k)`, `counterSel`, `lfsrSel`,
`p0Sel`) — and it is what makes `sh`/`cnt`/`lf`/`p0` reachable with a single
`pickScan` instance (the `Q` of the instance may close over the *other* groups'
`gw` words, which are just terms).

## 10. What the table discharges now

* **`CtrlMoveFabric.hostOut`** — `ctrlMoveFabric_hostOut_of_table`: the field's
  statement verbatim, with **no** `hPQ` hypothesis (the table supplies it via
  `hPQ_of_payload`, payload proofs by `cases dstOp d`).  `CtrlMoveFabric.conflict`
  was already de-`hPQ`'d (it never read a payload).
* **the `nonkeyed` component** (round c) — `DstPayloadTable` is now a `structure`
  with `payload` and
  `nonkeyed : ∀ f, (famG f == dgNone) = false ∧ (famG f == dgLSym) = false ∧
  (famG f == dgTStop) = false`; `famG_nonkeyed hT` is its projection, so the three
  `pickScan` side conditions come straight from the table (no per-field `decide`,
  and no `DstKindTable` class reasoning).  `decode_check_payload.lean` checks both
  components (exit 0, 2.4 s, 23 families × 64 codes + nonkeyed, 0 failures).
* **`UnitInputs.reg`** — **discharged**: `unitInputs_reg`, statement verbatim
  (`(mUnitsIn m pin).reg = (Bridge.AccB.absIn (accIn s pin)).reg`), hypotheses
  `ChipRel`, `Inv`, `hJGTab`, `CoreInputBus`, `hgrp`, `DstKindTable`,
  `DstPayloadTable`.  Chain: `Vector.ext`; per `k` one `pickScan_mWs` instance for
  `Fam.reg k` (`W = ·.reg j ↦ if j == k then some ()`, `Q = fun _ => some ()`,
  `T = id`, side conditions from `famG_nonkeyed`); cut side:
  `absIn.reg = absReg` (`rfl`), `absReg = Vector.ofFn …` (`rfl`),
  `packBools_bit`/`packNs_slice` for `rWe`/`rD` (helpers are
  `Discharge.packBools_bit`/`packNs_slice`, `Metronome.Bridge.AccB.rbyte`,
  `Metronome.Units.bitAt`), then one `cases` on the picked word's `we`.  No
  projection: the cut's `absReg` reads the full data byte, like the machine.

## 11. Items 2/3 of round b / round c / round d / round f: exact status and blockers

**Round f (targets: splice `hitsMask_onehot_first`, `unitInputs_acc`,
value-projection lemma + `unitInputs_shCfg_low5`).**

Landed and verified:

* **`hitsMask_onehot_first`** - spliced verbatim from the orchestrator's
  `scratch_onehot_orch.lean` (deleted afterwards):
  `Moves.hitsMask en grp G = (1 : BitVec 6) <<< k` from `hk : k < 6`,
  `hitAt ... k = true` and the earlier-slots-false hypothesis.  Public/reusable.
* **`DstPayloadTable.accRange`** - 4th table component
  (`forall d < 64, forall n, dstOp d = .acc n -> n < 7`).  This is what makes the
  machine's `W = (.acc op => op)` agree with `famIn .acc` (`decide (op < 7)`) in the
  `hPQ_of_payload` `none` branch, i.e. the missing piece for `unitInputs_acc`.
  Checked by the same compiled evaluation (`+ nonkeyed + codeOf + accRange`,
  0 failures, exit 0, 3.5 s).

Still open:

* **`unitInputs_acc`** - **discharged** (round g): `unitInputs_acc`, statement
  verbatim (`(mUnitsIn m pin).acc = (Bridge.AccB.absIn (accIn s pin)).acc`), plus
  the helper `opCodeOf_add` (`(opCodeOf (7+j)).toNat = j` for `j < 7`, seven
  `decide`s).  Chain: one `pickScan_mWs` for `Fam.acc` (`W = .acc op => op`,
  `Q dst = some (opCodeOf dst).toNat`, `T = id`); the two payload facts of
  `hPQ_of_payload` come from `hT.codeOf` (`.acc n -> d = 7+n`) and
  `hT.accRange`; cut side: `absIn_none` (hit = 0 <-> `we = false`) or
  `absIn_slot` + `hitsMask_onehot_first` + `pickWord_eq_word` (pick into the
  bundle), `opSel` via `packNs_slice`, `opData = rfl`, and
  `movBundle_dst`/`movBundle_data` to land on the slices.
* **`unitInputs_shCfg_low5`** - not started; recipe unchanged plus the
  value-projection lemma `(l.findSome? f).map T = l.findSome? (fun x => (f x).map T)`.
  All ingredients exist (`truncate_five_toNat`, `pickWord_we_exists`,
  `pickWord_eq_word`, `PayloadGroup`, `hT.codeOf`'s `.shCfg n -> d = 22+n`,
  `Strobes.opg_eq_pick`).

**Round e (targets: `hitsMask_onehot_first`, `unitInputs_acc`,
`truncate_five_toNat`/`shCfg_data_witness`/`unitInputs_shCfg_low5`).**

Landed and verified:

* **`truncate_five_toNat`** — `(BitVec.truncate 5 d).toNat = d.toNat % 32`
  (`BitVec.truncate_eq_setWidth` + `BitVec.toNat_setWidth`); this is the projection
  `unitInputs_shCfg_low5` will use.
* **`shCfg_data_witness`** — `(1023 : Nat) ≠ (truncate 5 (1023 : BitVec 8)).toNat`
  (kernel `decide`): the *exact* `UnitInputs.shCfg` form is false.

Still open, with the exact remaining steps:

* **`hitsMask_onehot_first`** — the whole remaining difficulty is one bit lemma:
  `bitAt_one_shift (k i) (hk : k < 6) (hi : i < 6) :
  CoreCtl.bitAt ((1 : BitVec 6) <<< k) i = (i == k)` — provable by `rcases` on
  `k`/`i` (6×6) then `decide`; the *complementary* case for `k`/`i` outside `0..5`
  is what the `Strobes.atMostOne_oneHotOrZero` route still needs (`1 <<< m = 0` for
  `m ≥ 6`, or an equivalent "bit set ⇒ m < 6").  With that, the one-hot lemma is:
  `hbitset` from the six `Moves.hitsMask_bit_i` (per `k`, with `hbefore 0..k-1`),
  `hne` from `hbitset`, `atMostOne_oneHotOrZero` ⇒ `hitsMask = 1 <<< m`, then
  `bitAt_one_shift` + `beq_iff_eq` give `m = k`.
* **`unitInputs_acc`** — as in round d, with the one-hot lemma as the only missing
  ingredient (then `absIn_slot`/`winnerSel_eq_slot`/`winnerData_eq_slot`,
  `packNs_slice` for `opSel`/`opData`, `hT.codeOf`'s `.acc n → d = 7+n` and
  `opCodeOf (7+op) = op` in 7 concrete cases).
* **`unitInputs_shCfg_low5`** — one `pickScan_mWs` for `Fam.shCfg k`
  (`W = ·.shCfg j ↦ if j == k then some ()`, `Q = fun _ => some ()`,
  `T = fun v => v % 32`) plus `we → dst == 22+k` from
  `pickWord_we_exists` → `pickWord_eq_word` → `PayloadGroup` → `hT.codeOf`'s
  `.shCfg n → d = 22+n`, then `truncate_five_toNat`.  Needs one extra
  `findSome?` plumbing lemma `(l.findSome? f).map T = l.findSome? (fun x => (f x).map T)`
  (induction on `l`, `cases` on `f a`) because the projection sits on the *value*,
  not inside the pair.

* Added to `DstPayloadTable` (round d): **`codeOf`** —
  `∀ d < 64, ∀ n, (dstOp d = .reg n → d = 14+n) ∧ (dstOp d = .shCfg n → d = 22+n) ∧
  (dstOp d = .acc n → d = 7+n)`, i.e. the payload index fixes the code.  Checked by
  the same compiled evaluation (`decode_check_payload.log`: 23 families × 64 codes
  **+ nonkeyed + codeOf**, 0 failures, exit 0, 2.7 s).  This is what turns the cut's
  *strobe* (`strobe s pin D = (gw s pin D).we && ((gw s pin D).dst == D)`, via
  `Strobes.opg_eq_pick`) into the pick's `we` — needed by `shCfg` (`cfgWe`) and by
  W1c's `sh`/`cnt`/`lf` (`strobe`-gated `we`/`sel`).
* Added (round d, **reusable**, `axioms`: no `sorryAx`): **`pickWord_we_exists`** —
  `(pickWord (hitsMask en grp G) dst dat).we = true → ∃ k, k < 6 ∧ hitAt en grp G k = true ∧
  ∀ j < k, hitAt en grp G j = false`.  This is the extraction every *conditional*
  payload field needs (`shCfg`'s `cfgWe`, `acc`'s one-hot); it is public and named
  for W1b/W1c.
* **`UnitInputs.acc`** — open: with `pickWord_we_exists` + `hT.codeOf` the chain is
  now complete in principle: first hit `k` → `hitsMask = 1 <<< k` (the one-hot lemma
  `hitsMask_onehot_first` is *not yet written*; recipe: `BitVec.eq_of_getLsbD_eq` +
  the six `Moves.hitsMask_bit_i` lemmas, three cases per bit: `j = k` (true), `j < k`
  (`hbefore`), `j > k` (the `!` of the OR that includes `hitAt k`)) →
  `Bridge.AccB.absIn_slot` + `winnerSel_eq_slot`/`winnerData_eq_slot` →
  `opSel i k = opCodeOf (slice mvDst 6k)` (`packNs_slice`) and
  `opData i k = slice mvDat 8k` (`packNs_slice`), `hT.codeOf` giving
  `d = 7 + op` and `opCodeOf (7+op) = op` (7 concrete cases).
* **`UnitInputs.shCfg` (projected `% 32`)** — open: one `pickScan_mWs` for
  `Fam.shCfg k` with `W = ·.shCfg j ↦ if j == k then some ()`, `Q = fun _ => some ()`,
  `T = fun v => v % 32`; cut side `absCfg` gives
  `if cfgWe then some (truncate 5 data).toNat` with
  `cfgWe = strobe s pin (22+k) = we && (dst == 22+k)` (`Strobes.opg_eq_pick`), and
  `we → dst == 22+k` from `pickWord_we_exists` + `pickWord_eq_word` + `PayloadGroup` +
  `hT.codeOf` (the `.shCfg n → d = 22+n` clause).  Projection: `truncate_five_toNat`
  (`(truncate 5 d).toNat = d.toNat % 32`) — not yet added; witness for the exact form:
  `1023 ≠ (truncate 5 1023).toNat`.
* **`UnitInputs.reg`** — **discharged** (round c), see §10.

* **`UnitInputs.reg`** — *open*, two named obligations: (i) the machine side is one
  `pickScan_mWs` for `Fam.reg k` with `W = (·.reg j => if j == k then some ())`,
  `Q = fun _ => some ()`, `T = id` (the cut keeps the whole data byte, so **no**
  projection is needed — unlike `flag`); (ii) the cut side needs
  `Units.bitAt (accIn …).rWe k = (gw … (14+k)).we` and
  `rbyte (accIn …).rD k = (gw … (14+k)).data`, i.e. `packBools_bit`/`packNs_slice`
  (`Metronome.ChipCut.Discharge.packBools_bit`, not `CoreUnits.*`) applied to the
  `accIn` definitions; the `rbyte`/`bitAt` helpers live in
  `Metronome.Bridge.AccB`, not `Metronome.Units.Acc`.  (I verified the two
  `absIn.reg = absReg` and `absReg.get = if …` unfoldings are `rfl`, then ran out
  of budget before the pack lemmas were wired.)
* **`UnitInputs.reg`** — **discharged** (round c), see §10.
* **`UnitInputs.acc`** — *open*: needs the one-hot form of the picked word
  (`hitsMask = 1 <<< k` at the first hit, from `hitsMask_bit_*` + the first-hit
  facts) plus `Bridge.AccB.absIn_slot` and `opSel`/`opData` as `packNs` slices;
  then one `pickScan_mWs` with
  `W = (·.acc op => some op)`, `Q = (fun dst => some (Units.Acc.opCodeOf dst))`,
  which is exactly the payload the table carries (`Fam.acc`).  The only syntactic
  bridge left is `famG .acc = Moves.dgTable 7` vs `accIn`'s `Moves.dgTable 7`
  (`BitVec.ofNat 6 7` vs the `OfNat` literal — `rfl`/`show`).
* **`UnitInputs.sh`/`shCfg`/`cnt`/`lf`** — *open*, same shape; each cut record
  reads one group's word (`Fam.sh`/`shCfg`/`cnt`/`lf`) and decodes the port from
  the word's destination code (`shifterSel`/`counterSel`/`lfsrSel`), with
  `cfgD`/`nibble` truncations (`truncate 5`, `1 <<< sel`) that are projections.
  `sh` additionally gates `we` by the `SHk.CFG` strobe (`Fam.shCfg`'s word) — the
  `Q` closes over that word, so still one instance.
* **`StreamWire.input` (adv/rx/ctl)** — *open*: `adv`/`rx` are `Strobes.opg` tests,
  i.e. `gw s pin (47+k)`'s `we && dst == 47+k` (`Strobes.opg_eq_pick`), so they are
  a `pickScan_mWs` instance for `Fam.stream k` with `W = (·.sAdv j => if j==k …)`
  and `Q = fun dst => some (dst == 47+k)`; the ctl move is the same word's
  `streamCtlOf` fields.
* **`MemHostCfg.p0_open_move`** — *open*: one instance for `Fam.p0` with
  `W = (pAl↦0, pAh↦1, pW↦2, pR↦3)`, `Q = fun dst => some (Strobes.p0Sel dst).toNat`,
  then `Bridge.Mem.mvOf` is `if pWe then some ⟨pSel.toNat, pData.toNat⟩` with
  `pWe = (gw 43).we`, `pSel = p0Sel (gw 43).dst`, `pData = (gw 43).data`; the only
  adapter is the `P0Move` record vs the pair (`funext` + `cases`).
* **`CtrlMoveFabric.hostInRead`** — *open*: needs a `src` field in `MoveBus`
  (`Bridge.Core.moves_bridge`'s `mv.src` slice equality, `slice (mvSrc s pin) (6q) 6`
  against `mv.src`) and then `Glue.anyRead (Moves.readsOf en src srcHostIn) =
  allMoves.any (srcOp = .hostIn)` by the six `readsOf` bits vs `and6`; no group
  pick and no payload.
* **Keyed picks (`WireAgree.sym`/`ctl`/`stop`, thread `late`)** — *open*: the
  per-line/per-thread key means the cut's `symMask`/`slotValid` are not `pickWord`
  of a group; the recipe is a keyed analogue of `pickScan`:
  `hit q := validAt (b.get q) && (group == G) && (key q == K)` with
  `Moves.sameKey` ⇒ same key (`Moves.same_key`/`winners_unique`,
  `Metronome.Moves.winners_unique`) giving both the "first hit wins" and the
  "later hit loses" steps, then `hitOr` on the one-hot `symMask`
  (`Strobes.hitsMask_atMostOne` for the group case; a `symMask` one-hot lemma is
  needed).  `late` is the cheapest of the four: `slotValid` is
  `validBits` bit `q`, i.e. the *valid* (not winning) mask, and the machine's scan
  is over `mAllMoves` (no resolution), so it needs `MoveBus.en`/`dst` only.
  Projected statements to be proved (and to be restated by the assembler):

  ```lean
  (ltLineIn m l).sym.map (fun w => (w.op, w.v % 16)) =
    (Bridge.Line.absIn (lineIn s pin l)).sym.map (fun w => (w.op, w.v))
  (ltLineIn m l).ctlMove.map (fun v => v % 8) =
    (Bridge.Line.absIn (lineIn s pin l)).ctlMove.map (fun v => v)
  (ltThreadIn m t).stop = (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).stop
  (ltThreadIn m t).late = (Bridge.Thread.absInput (threadAt s t.val) (threadIn s pin t.val)).late
  ```

  (`late`/`stop` are single `Bool`s, so no projection is needed there; only
  `sym`/`ctl` compare truncated data.)
* **`memhaz`/`cwovr`** — not this task.  `CtrlMoveFabric.memhaz`'s move-fabric
  term is `Moves.memhazEvent (mvEn) (mvSrc) (Mem.haz s.p0 (memIn s pin)) s.p0.rdy`
  (`Bridge.Moves.memhaz_event_bridge` is the machine-side reduction), and the
  pointer-hazard half (`p_haz`) belongs to the `p0` bridge (`MemHostCfg`,
  `p0_open_*`); `cwovr` is `writeData && !accept`, closed by the `cw`/queue bridge
  (`Glue.cwovr_step`, `Bridge.Glue`'s `CoreQueue.writeData/accept`).

