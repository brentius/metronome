# W2 (move fabric, unit inputs): `Metronome/ChipCut/Discharge/MoveFabricUnits.lean`

Task: close the three remaining multi-code-group `UnitInputs` fields — `cnt`, `lf`
and `sh` — against the machine's move fabric, on top of W1's
`Discharge/MoveFabric.lean` (`pickScan_mWs`, `DstPayloadTable`, `unitInputs_reg`).

Toolchain: Lean 4.35.0, core libraries only.  Acceptance: `lake build
Metronome.ChipCut.Discharge.MoveFabricUnits` exits 0 (`-DwarningAsError=true` from
`lakefile.toml`); no `sorry`, no `native_decide`.

Evidence: `data/raw/lean_chipcut_wire_movefabric_units_v4_20261122/` —
`commands.log` (commands, exit codes, wall times, rounds 1 and 2),
`build_final.log`, `lean_module.log`, `decode_check_ports.lean` + `.log`,
`axioms.lean`/`axioms.txt`.  `axioms.txt`: no `sorryAx`, no
`Lean.trustCompiler`; the only non-logical axioms are the pre-existing
`bv_decide` certificates (`Strobes.dsteqMask_pick`, `Strobes.hitsMask_atMostOne`,
`Moves.hitsMask_bit_*`, `Moves.beq_comm_5`) that `Strobes.opg_eq_pick` /
`Moves.hitsMask` already carried.  `git diff --quiet HEAD -- src` exits 0.

---

## 1. Status: all three fields discharged, statements verbatim

| field | theorem | statement |
|---|---|---|
| `UnitInputs.cnt` | `unitInputs_cnt` | `∀ k : Fin 3, (mUnitsIn m pin).cnt[k] = Bridge.CounterB.absIn (cntIn s pin k.val)` |
| `UnitInputs.lf` | `unitInputs_lf` | `∀ k : Fin 2, (mUnitsIn m pin).lf[k] = Bridge.LfsrB.absIn (lfIn s pin k.val)` |
| `UnitInputs.sh` | `unitInputs_sh` | `∀ k : Fin 2, (mUnitsIn m pin).sh[k] = Bridge.ShifterB.absOp (shIn s pin k.val)` |

Hypotheses: `ChipRel`, `Inv`, `hJGTab`, `CoreInputBus`, `hgrp`, `DstKindTable`,
`DstPayloadTable` (the `unitInputs_reg` set) **plus `DstPortTable`** (§2).  No
data projection is needed in any of the three: the cut keeps the whole data byte
(unlike `flag`, and unlike `shCfg`, which would need `% 32`).

**Round 2 change.**  Round 1's `sh` came out *projected*: with `Wire.lean`'s old
`shIn.we = (gw 18+k).we && !strobe 22+k` the verbatim field was refutable (on a
cycle winning both `SHk` and `SHk.CFG` the cut's record was `none`, the machine's
`some`; the shifter *state* diverged too, since `Machine.shNext` takes the data
and CFG options independently).  That gate is a ChipCut wiring bug: RTL
`project.v` 396 passes `.we(w[14])` of the *`SHk` group word* and the units cut /
README top-wiring row agree (`we == g_sh[k].w[14]`).  `Wire.lean:610` now reads
`we := (gw s pin (BitVec.ofNat 6 (18 + k))).we`; `sh_word`/`sh_absOp` dropped the
gate and `unitInputs_sh` is the field verbatim.  `unitInputs_sh_gated`,
`unitInputs_sh_of_noCfg` and the refutation `unitInputs_sh_exact_refuted` were
deleted (the first is now false, the second is subsumed); the old wiring and the
refutation are recorded in `unitInputs_sh`'s docstring and in §4 below.

## 2. The one new hypothesis: `DstPortTable`

`DstPayloadTable` decides *which write group* a code belongs to.  A **port**
decode additionally needs *which port* a code is, and the group does not
determine it: group `8+k` holds both `SHk.LD` (`18+k`) and `SHk.SH` (`20+k`)
(same for `CNTk` = `LO`/`HI`/`DEC`, `LFk` = `ST`/`B0..B3`).  `DstKindTable`
constrains only `NULL`/`L.SYM`/`T.STOP`/other, and the kernel cannot reduce
`Machine.Util.dstOfName` on the generated table's parsed names (`String.splitOnAux`
is `@[irreducible]` in Lean 4.35.0 core) — the same obstruction that forced
`unitInputs_flag_low4` to carry an `hPQ`.  So the code→port map is a table:

```lean
structure DstPortTable : Prop where
  shLd  : ∀ k, k < 2 → Machine.dstOp (18 + k) = .shLd k
  shSh  : ∀ k, k < 2 → Machine.dstOp (20 + k) = .shSh k
  cntLo : ∀ k, k < 3 → Machine.dstOp (24 + k) = .cntLo k
  cntHi : ∀ k, k < 3 → Machine.dstOp (27 + k) = .cntHi k
  cntDec: ∀ k, k < 3 → Machine.dstOp (30 + k) = .cntDec k
  lfSt  : ∀ k, k < 2 → Machine.dstOp (33 + k) = .lfSt k
  lfB0  : ∀ k, k < 2 → Machine.dstOp (35 + 4*k) = .lfB k 0
  lfB1  : ∀ k, k < 2 → Machine.dstOp (36 + 4*k) = .lfB k 1
  lfB2  : ∀ k, k < 2 → Machine.dstOp (37 + 4*k) = .lfB k 2
  lfB3  : ∀ k, k < 2 → Machine.dstOp (38 + 4*k) = .lfB k 3
```

Checked by **compiled** evaluation of the machine's own `dstOp` in
`decode_check_ports.lean` (`lake env lean --run …`, exit 0, 20 `(family, code)`
pairs, 0 failures); it also prints the group code lists, which are exactly the
inputs of the enumeration lemmas:

```
sh 0: group 8, codes [18,20]      cnt 0: group 12, codes [24,27,30]
sh 1: group 9, codes [19,21]      cnt 1: 13, [25,28,31]   cnt 2: 14, [26,29,32]
lf 0: group 15, codes [33,35,36,37,38]    lf 1: 16, [34,39,40,41,42]
```

## 3. How each field is proved

For every `k` the cut's record is one group word with a port decoded from its
destination code, so each field is one `pickScan_mWs` instance for `Fam.cnt k` /
`Fam.lf k` / `Fam.sh k` (`Q` = the port decode, `T = id`).

Per field the chain is:

1. `…_hPQ` — the payload table `hPQ`, from `DstPayloadTable.payload` (group
   membership) + `DstPortTable` (which port at which code) + the code-list
   enumeration (`cnt_codes`/`lf_codes`/`sh_codes`, `decide` over `List.range 64`):
   group matches → the code is one of the group's codes → the port table names the
   payload and `Q` computes to it; group does not match → `famIn (dstOp d) = false`
   → both sides `none` (`cases Machine.dstOp d <;> simp_all [famIn]`, legal on an
   *opaque* term).
2. `…_machine` — `pickScan_mWs` + `findSome?_congr` for `(mUnitsIn m pin).…[k]`
   (same proof shape as `unitInputs_reg`).
3. `…_absIn` / `sh_absOp` — the cut side: one group pick (`gw`), the port from the
   word's code.  The strobes of the group's other codes are rewritten to the same
   word by `strobe_eq` + `gw_congr` (group equality `decide`d per code), and the
   record is rebuilt as an explicit structure literal (`hrec`).
4. The field theorem is `rw [machine, cut]`.

The port decode is a pure `Bool` computation (`cnt_word`/`lf_word`/`sh_word`,
`cases … <;> simp`): the cut's `sel` is the `selOf` priority mux of the group's
strobes, and the machine's payload is the same mux over the destination code.
`lf`'s fourth `B` code is the mux's fallback (`sel = 4`), which is why `lfIn`
tests only three of the four `Bb` strobes.

**Proof-engineering note** (worth reusing in the other discharge files): `rw`
under an `if` whose `Decidable` instance mentions the rewritten term is
pathologically slow here (2 M heartbeats, minutes, in `cnt_absIn`'s first
attempt — the strobes occur in `sel = SEL_LO` inside `ite`).  Rewriting the
record's plain `Bool` fields (`strobe_eq`, `gw_congr`) and then rebuilding the
*structure literal* (`hrec : cntIn s pin k = ⟨…⟩`, closed by `simp only`) plus a
`rfl` lemma that unfolds `absIn` on a literal (`cnt_absIn_fields`) takes
milliseconds.

## 4. Historical: the `SHk.CFG` gate in `shIn.we` (round 1, now fixed)

Round 1 found `UnitInputs.sh` refutable and shipped a gated form.  The chain was:

* `dg_shSh` : `dgTable (20+k) = dgTable (18+k)` — group `8+k` holds `LD` and `SH`;
* `dg_shCfg_ne` : `dgTable (22+k) = 10+k ≠ 8+k` — `SHk.CFG` is a *different* write
  group, so the conflict arbiter does not prevent a cycle winning both;
* with the old `we = (gw 18+k).we && !strobe 22+k` the cut's record was `none` on
  such a cycle while `mUnitsIn.sh[k]` was `some`, and (since `Machine.shNext`
  applies the data and CFG options independently while the cut held `D`) the
  shifter state diverged as well — a real modelling disagreement, not a proof
  artefact;
* the RTL (`project.v` 396, `.we(w[14])` of the `SHk` group word) and the units
  cut / README top-wiring row (`we == g_sh[k].w[14]`) have no such gate, so the
  `Wire.lean` gate was the bug; it has been removed (`Wire.lean:610`).

`dg_shSh` and `dg_shCfg_ne` are kept (still true and still the reason the two
`SHk` moves compose independently); the round-1 gated/no-CFG/refutation theorems
are gone.

## 5. What is still open elsewhere

* `UnitInputs.acc`, `.reg` (`reg` is W1's), `.shCfg`, `.flag` — not this file.
  `shCfg` needs the same `% 32` projection as `flag` (`absCfg` reads
  `cfgD = truncate 5 data`, the machine the whole byte: then `bv 4 v` /
  `nbit v 4`), and `Fam.shCfg k`'s `hPQ` is gate-free, so the recipe here applies
  once the projection is chosen.
* The other `Fam` groups (`p0`, `stream`, `lCtl`, `hostOut`, `acc`) can reuse
  `DstPortTable`-style tables; `p0`'s four codes and `stream`'s three are the same
  multi-code shape as `cnt`/`lf`.

## 6. Reproduce

```powershell
cd code/tests/lean
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
lake build Metronome.ChipCut.Discharge.MoveFabricUnits        # exit 0
lake env lean --run ../../../data/raw/lean_chipcut_wire_movefabric_units_v4_20261122/decode_check_ports.lean
                                                             # exit 0, "DstPortTable: OK"
lake env lean -DwarningAsError=true ../../../data/raw/lean_chipcut_wire_movefabric_units_v4_20261122/axioms.lean
                                                             # exit 0, no sorryAx
lake build Metronome.ChipCut                                  # exit 0 (regression)
cd ../../..
git diff --quiet HEAD -- src                                  # exit 0
```

Timings in `commands.log`.  No file outside
`Metronome/ChipCut/Discharge/MoveFabricUnits.lean`, this note and the evidence
directory was created or edited.
