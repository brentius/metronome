# W-LM (line move wiring, projected): `Metronome/ChipCut/Discharge/LineMoveWire.lean`

Task: the two `WireAgree` fields that compare the machine's line-move records with the
cut's `Bridge.Line.absIn` — `sym` (`L.SYM`) and `ctl` (`Lk.CTL`).

Toolchain: Lean 4.35.0, core libraries only.  Acceptance: `lake build
Metronome.ChipCut.Discharge.LineMoveWire` exits 0 with the lakefile's
`-DwarningAsError=true`; no `sorry`, no `admit`, no `native_decide`.

Evidence: `data/raw/lean_chipcut_wire_linemove_v4_20261122/` — `axioms.lean`,
`axioms.txt`, `build_module.log`, `elaborate_module.log`, `chipcut_regression.log`,
`commands.log`.  `axioms.txt` has no `sorryAx` and no `Lean.trustCompiler`; the only
non-core axioms are `bv_decide` certificates of pre-existing lemmas
(`Moves.hitsMask_bit_*`, `Strobes.dsteqMask_pick`, `CoreCtl.makeWord_we/dst`,
`Moves.symMask_bit`, `MoveFabricKeyed.bits6_bit`, `Strobes.atMostOne_cases`, …) plus
**two new ones** from `truncate_four_makeWord` (§7).

Nothing outside this module, this note and the evidence directory was written.

---

## 1. What is delivered (all kernel-checked)

| field | theorem | form |
|---|---|---|
| `WireAgree.ctl` (`Lk.CTL`, group `20+l`) | **`wireAgree_ctl_low3`** | projected `% 8` |
| `WireAgree.sym` (`L.SYM`, group `0`, keyed by line) | **`wireAgree_sym_low4`** | projected `% 16` |

Statements, verbatim as proved (over `(s m pin) (l : Fin 4)` with the premise
hypotheses `ChipRel`, `Inv`, `hJGTab : JGTable`, `hbus : ∀ c, CoreInputBus …`,
`hgrp : GrpPacked`, `DstKindTable`, plus the extra table named on the line):

```lean
theorem wireAgree_ctl_low3 ... (hkind : Bridge.Moves.DstKindTable)
    (hT : DstPayloadTable) (l : Fin 4) :
    (ltLineIn m l).ctlMove.map (fun v => v % 8) =
      (Bridge.Line.absIn (lineIn s pin l.val)).ctlMove

theorem wireAgree_sym_low4 ... (hkind : Bridge.Moves.DstKindTable)
    (hC : DstStreamLineTable) (l : Fin 4) :
    (ltLineIn m l).sym.map (fun w => (w.op, w.v % 16)) =
      (Bridge.Line.absIn (lineIn s pin l.val)).sym.map (fun w => (w.op, w.v))
```

`hact : runRst s pin = true` is not needed by either (they read only the
combinational input records, not `Machine.step`).

## 2. The exact `WireAgree` forms are false

`LineThread.lean` states

```lean
sym : ∀ l : Fin 4, (ltLineIn m l).sym = (Bridge.Line.absIn (lineIn s pin l.val)).sym
ctl : ∀ l : Fin 4, (ltLineIn m l).ctlMove = (Bridge.Line.absIn (lineIn s pin l.val)).ctlMove
```

The machine keeps the winning move's whole 8-bit data byte (`Machine.Move.v`, a `Nat`),
while the cut truncates *at the consumption site*:

| cut field | definition |
|---|---|
| `Wire.lineIn.symD` | `BitVec.truncate 4 (symWord s pin l)` |
| `Bridge.Line.absIn.sym` | `if i.symWe then some ⟨absSymOp i.symOp, i.symD.toNat⟩ else none` |
| `Wire.lineIn.ctlD` | `BitVec.ofNat 3 (gw s pin (53+l)).data.toNat` |
| `Bridge.Line.absIn.ctlMove` | `if i.ctlWe then some i.ctlD.toNat else none` |

so the exact `Option`-valued forms fail as soon as a winning `L.SYM`/`Lk.CTL` data byte
has bits above 3 set: witnesses `MoveFabric.sym_data_witness`
(`255 ≠ (truncate 4 255).toNat`) and `MoveFabric.ctl_data_witness`
(`255 ≠ (ofNat 3 255).toNat`).  This is not an RTL/machine disagreement
(`Machine.stagedNext` uses `bv 4 v`, `Machine.lineNext`/`setBit` the low bits).

**Restatement for the assembler.**  The two `WireAgree` fields should be stated as

```lean
  /-- the `L.SYM` pick, data byte projected to the cut's nibble -/
  sym : ∀ l : Fin 4, (ltLineIn m l).sym.map (fun w => (w.op, w.v % 16)) =
    (Bridge.Line.absIn (lineIn s pin l.val)).sym.map (fun w => (w.op, w.v))
  /-- the `Lk.CTL` pick, data byte projected to the cut's 3-bit value -/
  ctl : ∀ l : Fin 4, (ltLineIn m l).ctlMove.map (fun v => v % 8) =
    (Bridge.Line.absIn (lineIn s pin l.val)).ctlMove
```

(the `fun w => (w.op, w.v)` map on the cut side is needed only to put both sides in
`Option (Nat × Nat)`; the cut's value is already `(absSymOp symOp, symD.toNat)` with
`symD` the truncated nibble, i.e. it *is* the `% 16` projection of the machine's word.)
`wireAgree_ctl_low3`/`wireAgree_sym_low4` are the `∀ l` fields' pointwise versions, so
the assembler can fill the two structure fields by `fun l => wireAgree_ctl_low3 … l`
(resp. `…_sym_low4`).

## 3. `ctl`: a non-keyed group pick plus a single-code group

`Lk.CTL` is group `20+k` (code `53+k`), not keyed, so this is one
`MoveFabric.pickScan_mWs` instance, in the shape of `unitInputs_shCfg_low5`:

1. **Payload table** gives the machine side: `hPQ` from
   `hPQ_of_payload (famIn (.lCtl l)) W (fun _ => some ()) (famG (.lCtl l))` with
   `W = fun o => match o with | .lCtl j => if j == l.val then some () else none | _ => none`
   — `famIn (.lCtl k)` is `fun o => match o with | .lCtl j => j == k | _ => false`, so
   both `ht`/`hf` are `cases dstOp d <;> simp_all [famIn]`.
2. **The single-code group**: `dgTable_lctl_code` proves
   `∀ d < 64, (dgTable (ofNat 6 d) == dgTable (ofNat 6 (53+l))) = true → d = 53+l`, a
   `4 × 64` `decide` over the literal table (`List.range 4` of `List.range 64`, no
   variables).  This turns the pick's winner group into `gw.dst == 53+l`, so the cut's
   strobe `ctlWe = strobe s pin (53+l) = gw.we && (gw.dst == 53+l)` collapses to `gw.we`
   (`hstr`, `Strobes.opg_eq_pick` + `pickWord_we_exists` + `pickWord_eq_word` + `hgrp`).
3. `pickScan_mWs` with `P = W`, `Q = fun _ => some ()`, `T = fun v => v % 8` gives
   `(mWs).findSome? … = if gw.we then some (gw.data.toNat % 8) else none`; the machine
   side is `(ltLineIn m l).ctlMove.map (· % 8)` via `findSome?_map_value` +
   `ltWs = mWs` + a per-slot `cases dstOp <;> simp` (`hstep`).
4. Cut side: `ctlD.toNat = gw.data.toNat % 8` is `ofNat3_toNat`
   (`BitVec.toNat_ofNat` + `2^3 = 8`).

No `DstStreamLineTable` row is needed (the task's prediction held: group membership
alone pins the code), and no `hact`.

## 4. `sym`: the line-keyed `hitOr` mask against the winner scan

The cut's word is `Wire.symWord s pin l = Moves.hitOr M (mvDst) (mvDat)` with the
per-line winner mask `M = Moves.symMask (mvWin s pin) (mvGrp s pin) (mvXl s) (ofNat 2 l)`.
The machine scans its winners for `.lsym op` with `mv.line == l`.

1. **One-hot** (`MoveFabricKeyed.symMask_atMostOne`): `Moves.atMostOne M = true`, so `M`
   is `0` or `1 <<< q`.
2. **`hitOr` of one-hot** (`MoveFabricKeyed.hitOr_onehot`): `M = 1 <<< q` makes the cut's
   word `makeWord true (slice mvDst 6q 6) (slice mvDat 8q 8)`, hence
   `symWe = bit 14 = true` (`bitAt_makeWord_14`), `symOp = lineSop (slice mvDst 6q 6)`
   (`slice_makeWord_8_6`) and `symD.toNat = (slice mvDat 8q 8).toNat % 16`
   (`truncate_four_makeWord` + `truncate_four_toNat`).
3. **The recode** `absSymOp_lineSop`: on the `DG_L_SYM` group (codes 1/2/3)
   `absSymOp (lineSop code) = code` — a 64-code `List.all` `decide` behind a Bool
   implication, instantiated at `ofNat 6 code`.
4. **The two scans agree slot by slot** (`symSlot`): at a winner `q`,
   `bitAt M q = match dstOp (machMove q).dst with | .lsym _ => (mv.line == l) | _ => false`.
   The three ingredients are `winBits_bit` + `winAt_arbBundle` (the cut's `mvWin` uses
   `arbBundle`, the machine's winners `bundleOf`: `winAt` reads no destination/data,
   `winAt_bundleOf`), `isLsym_eq_group` (`DstKindTable`) for the group conjunct, and
   `beq_ofNat2_toNat` + `hbus.line` for the line conjunct.
5. **`symScan_eq_none_iff`** turns that into "the scan is `none` iff the mask bit is
   clear", which drives the two cases:
   * scan `none` → every mask bit clear → `M = 0` (`bits6_eq_zero`) → `symWord = 0`
     (`hitOr_zero`) → `symWe = false` → the cut's `sym` is `none`;
   * scan `some v` → the found slot `q` (`List.findSome?_eq_some_iff`) has `bitAt M q`
     set, so `M = 1 <<< q` (`eq_shift_of_atMostOne`: at-most-one-hot plus a set bit);
     the machine's value at `q` is `((slice mvDst 6q 6).toNat, (slice mvDat 8q 8).toNat % 16)`
     (`machMove_dst`/`machMove_data` + the `DstStreamLineTable.lsym` row
     `dstOp d = .lsym n → n = d` identifying the op with the destination code), which is
     exactly the cut's projected pair.

The machine's winner list is converted to the `range 6` scan with
`MoveFabric.scan_rewrite` (no new list plumbing), and `ltWs = mWs` is the usual
`mAllMoves_ltAllMoves` rewrite.

Residual hypotheses: `DstStreamLineTable` (for the `lsym` row) and `DstKindTable`;
`DstPayloadTable` is **not** needed.  No `hact`.

## 5. Per-field status

| field | status |
|---|---|
| `WireAgree.ctl` | **discharged in the `% 8` form** (`wireAgree_ctl_low3`); exact form **false** (`ctl_data_witness`) |
| `WireAgree.sym` | **discharged in the `% 16` form** (`wireAgree_sym_low4`); exact form **false** (`sym_data_witness`) |

## 6. Findings

1. **`sym` needs no "first keyed hit wins" argument.**  `MoveFabricKeyed` supplies the
   keyed pick for `T.STOP` (`winAt_of_keyed_first_stop`), but `L.SYM`'s cut side does
   *not* scan the valid bits: it reads the one-hot winner mask through `hitOr`.  The
   missing step is only "the mask is one-hot, so the machine's findSome? over the
   winner list can only hit the mask's slot" — no `Moves.winners_unique` reasoning at
   the scan level.
2. **The op recode is a table fact, not arithmetic.**  `absSymOp ∘ lineSop` is the
   identity on the `L.SYM` group; the proof is a 64-code `decide` (cheap, and it also
   gives the "only 1/2/3 are `L.SYM`" direction).
3. **`ctl` needs no stream/line code table.**  Group `20+k` holds exactly one code, so
   the 4 × 64 `dgTable` check pins `dst == 53+l` under `we`, and the payload table
   supplies the machine's `.lCtl` decode.  This is the cheapest non-keyed pick in the
   file (compare `shCfg`, which needs `DstPayloadTable.codeOf`).
4. **Beware `Core.slice` vs `CoreCtl.slice`** (identical bodies, distinct constants):
   `MoveBus`/`movBundle_*` are stated with `Metronome.Core.slice`, `hitOr_onehot`/
   `CoreCtl.makeWord_*` with `CoreCtl.slice`.  They are definitionally equal, so
   `exact`/`rfl` bridges them, but `rw` does not match across the two names.

## 7. Axiom budget

`truncate_four_makeWord` (`truncate 4 (makeWord we d da) = truncate 4 da`) is proved by
`cases we <;> unfold CoreCtl.makeWord <;> bv_decide`, adding two `bv_decide`
certificates of the same class as the pre-existing `slice_makeWord_0_4` in
`MoveFabric`.  Everything else is `decide`-only or core.

## 8. Reproduce

```powershell
cd lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.LineMoveWire        # exit 0, ~5 s fresh, 0.4 s cached
lake env lean -DwarningAsError=true Metronome/ChipCut/Discharge/LineMoveWire.lean
                                                           # exit 0, 4.5 s, no warnings
lake env lean -DwarningAsError=true ..\..\..\data\raw\lean_chipcut_wire_linemove_v4_20261122\axioms.lean
                                                           # exit 0, 2.1 s, no sorryAx
lake build Metronome.ChipCut                               # exit 0 (regression)
cd ..
git diff --quiet HEAD -- src                               # exit 0
```

`commands.log` records the commands, exit codes and wall times.

## 9. Build hygiene

No `lake clean`, no deleted `.olean`s, and no file outside this module, this note and
the evidence directory was touched.  `MoveFabricKeyed.lean` is owned by another agent
and was edited concurrently; the import chain compiled cleanly at every build here.
