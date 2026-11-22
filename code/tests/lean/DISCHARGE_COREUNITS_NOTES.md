# Discharge notes: `Premises.cores` and `Premises.units` (round c)

Files:
* `code/tests/lean/Metronome/ChipCut/Discharge/CoreUnits.lean` (1114 lines)
* `code/tests/lean/Metronome/ChipCut/Discharge/MoveFabric.lean` (82 lines, new)

Evidence: `data/raw/lean_chipcut_discharge_coreunits_v4_20261121c/`
(`build.log`, `axioms.lean`, `axioms.txt`, `commands.log`).

Acceptance: `lake build Metronome.ChipCut Metronome.ChipCut.Discharge.CoreUnits
Metronome.ChipCut.Discharge.MoveFabric` exits 0 with `-DwarningAsError=true`
(Lean 4.35.0, core libs only; clean module rebuild 14.7 s); axioms driver exit 0
(2.7 s); `premise_cores` = `[propext, Classical.choice, Quot.sound]`,
`premise_units` adds only the pre-existing bridge `bv_decide` certificates; no
`sorryAx`, no `native_decide`/`admit`; `git diff --quiet HEAD -- src` = 0.

---

## 1. The thread `CORE` bit (done)

`Wire.lean` now builds `tCore := packBools 6 fun t => (…).threads[t]!.core == 1`
(the raw `CORE` bit, `project.v` 553).  The file therefore:

* deletes `coreOf_inverted` (the disagreement is gone);
* **keeps `mine_false_bit`** (`bitOf (mine false i) e = !bitOf i.tCore e`): it is
  true for every `tCore` and is exactly what the `coreOf` proof needs;
* proves `rel_coreOf` (`Bridge.Core.Rel`'s `CORE` slot) from `ChipRel`:
  `thread_core_lt` (the `CORE` field is one bit), `beq_zero_of_lt_two`
  (`x = 0` ↔ `x ≠ 1` on one bit), `mine_false_bit` for core 0 and `mine true =
  tCore` for core 1.

`CoreInputBus` is now **two** fields: `guards` and `srcs`.

## 2. The guard/source vector (infrastructure proved; leaf wiring open)

Proved in the file (all kernel-checked, no `bv_decide`):

* **bit plumbing** — `bitOf_setBit_same`, `bitOf_setBit_ne`,
  `getLsbD_lowMask`/`bitOf_lowMask_lt`/`bitOf_lowMask_ge` (via
  `BitVec.getLsbD_{and,or,not,shiftLeft,allOnes,twoPow}`);
* **the cut's effective guard vector** — `guardVec_bit`:
  `bitOf (Core.guardVec g gl ln) k` is `true` for `k = 0`, the `g_line` bundle bit
  `k-27` for `27 ≤ k ≤ 31`, `bitOf g k` for other `k < 62`, and `false` for
  `k ≥ 62` (for `k < 64`; `k ≥ 64` is false on both sides);
* **the 64-slot table dispatch** — `guardV_global` (`GuardTable` ⟹
  `guardV e k = guardAt k (guardsOf e)` for `k < 64`, `k ∉ 27..31`, by 64 kernel
  cases through `Bridge.Glue.guard_slot_k`) and `srcV_global` (`SrcTable` ⟹
  `srcV e k = srcAt k (sourcesOf e)` for `k < 64`, `k ∉ 1..3`).

Remaining for `CoreInputBus` to disappear (three layers):

1. the **leaf equalities** `guardsOf s = Glue.guardsOf (env …)`,
   `lineGuardsOf s = Glue.lineGuardsOf (env …)`,
   `sourcesOf s = Glue.sourcesOf (env …)` and `env.hlvl` (pin vector < 2^13).
   The leaves are: flags/shifter/counter/LFSR/acc `Bridge.Units` outputs, the
   `Bridge.Stream` `end`/`mark`/`byte`/`bit` outputs (with
   `AbsRelB` ⟹ `abs = m.streams[k]` and `cfgOf (streamViewIn s k) =
   (cfgView …).streams[k]`), the `Bridge.Line` `run`/`sp`/`inSym`/`cap` fields,
   `ctrl.inv/outv`, `p0.rdy`, and the pin vector (`Debug.Pins.pinVec` vs
   `Machine.Util.protoPins` with the `RPL`/`EMASK`/`RLV` overlay).  The 2/3/4-bit
   packings (`bv 2/3/4 (b2n … * 2^k + …)`) are decided case-by-case on the
   Booleans.
2. the **`g_line`** bytes: `bitOf (lineSlot gLine ln) j = bitAt (lineGuard ln
   (lineGuardsOf s)) j` from `gLine := packBools 20 (…)` (`packBools_bit`);
   `lineGuard_bridge` then gives the machine's 27..31 slots.
3. the **`srcVec`** substitutions: `withSlot`/`lowMask 512 (8*39)` byte lemmas,
   and slots 0..3 matching `srcVal`'s `ZERO`/`imm`/`L_IN`/`L_CAP`
   (`src_slot_0..3`).

Order of assembly (once 1-3 are done): `guardVec_bit` + `packBools_bit` +
`guardV_global`/`lineGuard_bridge`/`guardAt_beyond` gives `Rel.guards`; the
`srcVec` byte lemma + `srcV_global`/`src_slot_1..3` + `SrcTable` gives `Rel.srcs`.

## 3. The move fabric (`MoveFabric.lean`)

Proved (the padding half of `resolveMoves_pick`'s `MoveTable (six m)` hypothesis):

* `resolveAux_null` — a list of `NULL` moves is the identity on the resolver
  state (`stepOn_none`);
* `resolveAux_filter_some` — dropping the `NULL` moves **anywhere** in the list
  leaves `resolveAux` unchanged (the machine's `runStep` list is a `filterMap`);
* `resolveMoves_filter_some` — the same for `Machine.resolveMoves` (winners and
  conflict flag), via `Bridge.Moves.resolveMoves_eq`;
* `six_length`.

Still needed for `UnitInputs` (and the other move-pick consumers):

* `machMove : State → PinIn → Nat → Machine.Move` — slot `q` is the machine's
  `moveVal` when enabled and a `NULL` (`dst = 0`) move otherwise, from
  `Bridge.Core.coreComb_moves` applied to both cores
  (`mAllMoves = (range 6).filterMap (if enabled then some (machMove q) else none)`);
* `resolveMoves allMoves = resolveMoves (six machMove)` (this file's filter lemma
  plus `six_length`);
* `MoveAgree (bundleOf (mvEn …) (mvGrp …) (mvDst …) (mvDat …) (mvXl …) (mvXt …))
  machMove` and hence `MoveTable` (`Bridge.Moves.moveTable_of_agree`, needs
  `DstKindTable`);
* `resolveMoves_pick` then gives, per group, `machWs`'s `findSome?`, closing the
  seven `UnitInputs` fields (the six-slot padded list is where this file's
  padding lemma enters).

## 4. Reproduce

```powershell
cd code/tests/lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut Metronome.ChipCut.Discharge.CoreUnits Metronome.ChipCut.Discharge.MoveFabric
lake env lean ..\..\..\data\raw\lean_chipcut_discharge_coreunits_v4_20261121c\axioms.lean
cd ../../..
git diff --quiet HEAD -- src
```
