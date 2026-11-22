# W2 wiring notes: the core guard and source vectors (`CoreInputBus.guards`, `CoreInputBus.srcs`)

File: `code/tests/lean/Metronome/ChipCut/Discharge/GuardSrc.lean` (1182 lines; imports
`Metronome.ChipCut.Discharge.CoreUnits`, edits nothing else).
Evidence: `data/raw/lean_chipcut_wire_guardsrc_v4_20261121/`
(`axioms.lean`, `axioms.txt`, `commands.log`).

Acceptance: `lake build Metronome.ChipCut.Discharge.GuardSrc` exits **0** with
`-DwarningAsError=true` (Lean 4.35.0, core libraries only; module rebuild 4.7-5.0 s
wall once the `ChipCut`/`Discharge` dependencies are up to date). Axioms driver exits 0
(3.7 s); `src/` untouched (`git diff --quiet HEAD -- src` = 0).

**Outcome: both target fields are discharged under the named hypotheses.**
This is round **b**, after the `Wire.lean` fix found in round a: `sourcesOf.sBit`,
`guardsOf.sBit` and `streamReq` now use `Stream.bitOut (k == 0)` (only S0 has
capture/replay, `md2_stream #(.CAP(k == 0 ? 1 : 0))`).  The round-a refutations
(`guards_false` / `srcs_false` and their witnesses, failing at guard 44 / source 35,
i.e. S1's `BIT`) are **obsolete and have been removed**; the corrected leaves are
proved equal to the machine's slot-1 stream bit/value below.

---

## 1. Per target field

The field statements are quoted verbatim from `CoreUnits.lean` 516-526
(`structure CoreInputBus (s m pin c) (x : Core.State)`), instantiated at
`x := sIr s m c` and `c.val`.

| target field | status | theorem |
|---|---|---|
| `CoreInputBus.guards` | **discharged** | `coreInputBus_guards` |
| `CoreInputBus.srcs` | **discharged** | `coreInputBus_srcs` |
| both at once | **discharged** | `coreInputBus` (structure witness) |
| `Premises.cores` with no `CoreInputBus` hypothesis | adapter | `premise_cores_of` |

```lean
theorem coreInputBus_guards (hG : Bridge.Glue.GuardTable) (s : State) (m : Machine.State)
    (pin : Machine.PinIn) (c : Fin 2) (hrel : ChipRel s m) (hinv : Inv s)
    (hact : runRst s pin = true) :
    ∀ (ln : Nat), ln < 4 → ∀ k : Nat,
      Core.bitOf (Core.guardVec (coreIn s pin c.val).guards (coreIn s pin c.val).gLine
        (BitVec.ofNat 2 ln)) k =
      Machine.guardVal m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg) ln
        (Machine.guardOp k)

theorem coreInputBus_srcs (hS : Bridge.Glue.SrcTable) (s : State) (m : Machine.State)
    (pin : Machine.PinIn) (c : Fin 2) (hrel : ChipRel s m) (hinv : Inv s)
    (hact : runRst s pin = true) :
    ∀ k : Nat,
      (Core.slice (Core.srcVec (sIr s m c) (coreIn s pin c.val)) (8 * k) 8).toNat =
      Machine.srcVal m (Machine.cfgView m.cfg) (Machine.pinView m.sync m.dbg)
        (sIr s m c).xl.toNat (Machine.insnField (sIr s m c).ir Machine.Tables.FIELD_imm)
        (Machine.srcOp k)
```

`hinv`/`hact` are not read by either field (the equalities depend only on `ChipRel`);
the binders are kept so the signature is uniform with the other `CoreInputBus`
consumers and `premise_cores`.  No hypothesis of any other kind appears: the only
extra inputs are the global string tables `GuardTable`/`SrcTable`, which the existing
`guardV_global`/`srcV_global` already require (the `Array` literals are built by
`String`-parsing and do not reduce in the kernel).

## 2. Layers (as recorded in `DISCHARGE_COREUNITS_NOTES.md` §2)

### 2.1 Leaf equalities (§2 layer 1)

* `sourcesOf_eq`, `sourcesOf_envS`, `guardsOf_eq`, `lineGuardsOf_eq`:
  `sourcesOf s = Bridge.Glue.sourcesOf (env …)`, etc., for the `Env` built from the
  related machine state (`envG` at a line, `envS` at the core's line/immediate).
  Assembled field-by-field with the `*_ext` lemmas from `ChipRel`; the leaves:
  * units: `shDone_eq`, `shOut_eq`, `cntZ_eq`, `accR_eq`, `shD_eq`, `shO_eq`,
    `cnV_eq`, `lfS_eq`; flags/ctrl: `ctrl_inv`, `ctrl_outv`, `ctrl_inb`, `p0.rdy`;
  * streams: `cfgOf_streamViewIn`, `stream_fields`, `streamEnd_eq`, `streamMark_eq`,
    `streamAtByte_eq`, `streamByte_eq`, and the two bits
    **`streamBit_1_eq` (S1, `CAP = 0`)** / **`streamBit_0_eq` (S0, `CAP = 1`)** —
    the round-b replacements for the refuted hard-coded `CAP = 1` leaves;
  * lines: `lineInSym_eq`, `lineSp_eq`, `lineRun_eq`, `linePinA_eq`, `linePinB_eq`;
  * pins: `pinLvl_toNat` (`Debug.Pins.pinVec` vs `Machine.Util.protoPins`),
    `pinView_abs` (`absChip`'s `ui2/uio2/RPL/EMASK/RLV` overlay), `pinLvl_bv`,
    `pinLvl_lt` (`Env.hlvl`).
  The `2`/`3`/`4`-bit packings are decided case-by-case on the Booleans
  (`b1_eq`…`b4_eq`, `b4x2_eq`), never by native evaluation.

### 2.2 The `g_line` byte step (§2 layer 2)

`lineSlot_bit`: `bitOf (Core.lineSlot (coreIn s pin c).gLine (ofNat 2 ln)) j =
Glue.bitAt (Glue.lineGuard ln (lineGuardsOf s)) j` for `ln < 4`, `j < 5`, from
`gLine := packBools 20 …` through `packBools_bit`, `lineSlot_index`, `bitOf_slice`.
With `Bridge.Glue.lineGuard_bridge` this closes the machine's slots 27..31.

### 2.3 The `srcVec` substitutions (§2 layer 3)

`withSlot_slice_same`/`withSlot_slice_ne` and the `lowMask 512 (8 * 39)` mask lemmas
(`mask_slice_lt`/`mask_slice_ge`, via `lowMask_getLsbD_{lt,ge}`,
`getLsbD_shiftLeft_{lt,ge}`), giving `srcVec_slice_0..3` (cut-local `ZERO`/`IMM`/
`L.IN`/`L.CAP`) and `srcVec_slice_ne`/`srcVec_slice_ge` (bus slots, and cleared slots
≥ 39).  The core-local slots match `srcVal`'s `SRC_ZERO`/`SRC_IMM`/`SRC_L_IN`/
`SRC_L_CAP` through `i_imm_toNat`, `lIn_slot`, `lCap_slot`.

### 2.4 Assembly (§2 "order")

`guardVec_bit` + `lineSlot_bit` + `guardsOf_eq`/`lineGuardsOf_eq` +
`guardV_global`/`lineGuard_bridge`/`guardOp_ge` give `guards`; the `srcVec` byte
lemma + `sourcesOf_envS` + `srcV_global` + `SrcTable` + `srcOp_ge` give `srcs`.
No `ChipCut`/`Bridge`/`Machine` file was modified by this task.

## 3. Axioms

`axioms.txt` (from `axioms.lean`, `#print axioms` on the two fields, the bundle, the
adapter, and 20 layer theorems):

* every theorem depends only on `propext`, `Classical.choice`, `Quot.sound`, plus
  `bv_decide` certificate axioms — the same trusted certificates the rest of
  `Discharge` already uses (`Bridge.Glue.slice48_*`, `slice64_*`,
  `Bridge.Line.and_one_bne_zero_32`, `Glue.lineGuard_at`), and five introduced here
  by `bv_decide` in `accR_pack`, `and80_ne`, `and01_ne` (3 lemmas, 5 certificates);
* no `sorryAx`, no `native_decide`, no `admit`; `src/` untouched;
* `lineSlot_bit`, all seven `srcVec_slice_*` lemmas, `pinLvl_toNat`, `pinView_abs`,
  `streamBit_*_eq`, `streamByte_eq` depend on **no** `bv_decide` certificate
  (`[propext, Classical.choice, Quot.sound]`).

## 4. Revisions the result is anchored to

| file | SHA-256 (2026-11-21, at this build) |
|---|---|
| `Metronome/ChipCut/Wire.lean` | `ACF68EAD3A986E2AF57D2BF62EA270A77609CE812A48B57793B7A3F4AB954C84` |
| `Metronome/ChipCut/Discharge/GuardSrc.lean` | `BD966C43A72154100CDFDDE9BCACABD37E9329B5C5D9567E6E3FDD8E19B860B6` |
| `Metronome/ChipCut/Discharge/CoreUnits.lean` | `74FFFE7AC7D7FE92D103DB39E7A40A83D0855D67359C827455598462FF9E29ED` |
| `Metronome/ChipCut/Rel.lean` | `4E8BCE427E40837FE87C3638F3FAE3E5EB710634075510BA65E382D873970996` |

If the S1/S0 `CAP` convention in `Wire.lean` changes again, `streamBit_1_eq` /
`streamBit_0_eq` (and `sourcesOf_eq`/`guardsOf_eq`) are the tripwires.

## 5. Reproduce

```powershell
cd code/tests/lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.GuardSrc                  # exit 0, 5.0 s wall
lake env lean ..\..\..\data\raw\lean_chipcut_wire_guardsrc_v4_20261121\axioms.lean   # exit 0, 3.7 s
cd ../../..
git diff --quiet HEAD -- src                                     # exit 0
```

`commands.log` in the evidence directory records each command, exit code and wall time,
including the five failed intermediate builds that fixed the three tactic/statement
errors left by the interrupted predecessor (a `simpa` that needed `guardV` unfolded,
a `lineAt`/`hrel.lines` rewrite order, a core-only `set` tactic, a missing
`setWidth8_toNat2`, and `envS` `imm` mismatch).
