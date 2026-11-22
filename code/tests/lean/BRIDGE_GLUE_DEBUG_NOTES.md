# Bridge notes: the glue and debug cuts vs the whole-chip machine (item 4L)

Evidence dir: `data/raw/lean_bridge_glue_debug_v4_20261121/` (`axioms.txt`,
`commands.log`, `build*.log`, `Axioms.lean`, `glue_names.txt`, `debug_names.txt`).
Files: `Metronome/Bridge/Glue.lean` (new), `Metronome/Bridge/Debug.lean` (new).

Status: `lake build Metronome.Bridge.Glue` (with `-DwarningAsError=true` from
`lakefile.toml`) exits 0 with 265 theorems (163 from 4L, 58 from the first 4N pass, 44
from the second), no `sorry`, no `native_decide`; `#print axioms` reports only
`propext`, `Classical.choice`, `Quot.sound` (and no axioms at all for five lemmas) —
see `axioms.txt`.  `git diff --quiet HEAD -- src` is true (the RTL was not touched).
`Metronome.Bridge.Debug` was **not** rebuilt in this pass (it is another agent's
in-progress file; its working-tree version does not currently compile at
`Debug.lean:814`), so the debug half of the numbers above is unchanged from the 4L pass.

The cut → RTL direction is the existing `glue_check.py`/`debug_check.py` generated
proofs; this note supplies the cut → `Machine.*` direction, so RTL = cut = machine
for the components listed.  The machine modules are **read/import only**.

---

## 1. Glue (`Metronome.Glue` vs `Machine.ctrlNext`/`unitsNext`/`outNext`/`srcVal`/`guardVal`)

### Abstraction map

`Env` bundles the machine view of one cycle: the `State`, the decoded `CfgView`, the
§2 `PinView`, the reading line `l`, the immediate `imm`, and `hlvl : p.lvl < 2^13`
(the §2 range fact for `pinView`; it is an explicit interface hypothesis here — the
machine's `pinView` masks the raw pins to 13 bits, but that arithmetic is not proved
in this file, see the gaps).

| cut leaf | machine |
|---|---|
| `Sources` | `sourcesOf e`: `fl := units.f`, `pins := bv 13 p.lvl`, `accA := units.a`, `accR := ((r3++r2)++r1)++r0`, `shD := sh1.d ++ sh0.d`, `shO := {SH1.O, SH0.O}`, `cnV := (cnt2++cnt1)++cnt0`, `lfS := lf1 ++ lf0`, `pDat := p0.d`, `sBit/sByte` from `streamBit`/`streamByte`, `inB := ctrl.inb` |
| `Guards` | `guardsOf e`: `fl`, `shDone`/`shOut`/`cntZ` packed from the units, `accZ/C/N`, `lfS`, `inv/outv/pRdy`, `sEnd/sMark/sByte/sBit` from the streams, `pins`, `lRun` |
| `LineGuards` | `lineGuardsOf e`: `inn` packs `inSym` of the four lines, `sp`, `pina`, `pinb` |
| index tables | `srcOpOf`/`guardOpOf` (constructor tables) and the hypotheses `SrcTable`/`GuardTable`: `∀ i, srcOp i = srcOpOf i`, `guardOp i = guardOpOf i` |

Values cross the map as `BitVec.toNat` (machine) vs the cut's `BitVec` (machine
`bv n x.toNat` is the identity, `bv_toNat`).  The machine's source/guard decoders
are built from string tables; `String.splitOnAux` is `@[irreducible]` in Lean
4.35.0, so the kernel cannot evaluate the `parsePort` names.  The fixed-list names
(11 sources, 12 guards) are kernel-checked (`srcOp_fixed`, `guardOp_fixed`); the
rest are the one global hypothesis each, checked by compiled evaluation in
`decode_check.lean`.

### Bridge theorems (one line each)

* **Plumbing.** `bitAt_eq_nbit` (cut bit = machine `nbit`), `slice_toNat` (cut slice
  = machine `nbits`), `bitByte_toNat`, `bv_toNat`, `b2n_lt`, `bit_eq_nbit`,
  `b2n_nbit`, `bit_two`/`bit_three`/`bit_four` (packed-vector bit reads),
  `bv_two_toNat`/`bv_three_toNat`/`bv_four_toNat`, `slice64_*` (8), `slice48_*`
  (6), `slice_bytes_*` (4), `slice16_*` (2) (byte/word slices of the glued
  vectors), `nbits_low`/`nbits_high` (chunk extraction, `Nat`).
* **Tables.** `srcOp_eq`, `guardOp_eq` (decoder → name-table lookup),
  `srcOp_fixed`, `guardOp_fixed` (kernel-checked fixed entries).
* **Sources.** `src_slot_0` … `src_slot_63`: the machine's `srcVal` of the slot's
  source port is the cut's `srcAt` slot value (for slots 4..38), the machine's
  core-local value for slots 1..3 (the cut's global vector is 0 there by design),
  and both zero for 39..63.
* **Guards.** `guard_slot_0` … `guard_slot_63` (all but 27..31): the machine's
  `guardVal` on line `l` is the cut's global `guardAt` value.

### Side conditions

* `h : SrcTable`/`h : GuardTable` on every slot theorem (the decode table, above).
* `Envelope.hlvl : p.lvl < 2^13` for the `PINS.LO/HI` source slots and the `PINk`
  guards (a range fact of `pinView`, not a cut disagreement).
* No other hypothesis: every slot is proved for all machine states, configurations
  and pin views.

### Disagreements

* **None found** in the sources and guards.  The four core-local source slots are a
  *representation* difference only: the cut's global vector leaves `ZERO`, `IMM`,
  `L.IN`, `L.CAP` at 0 because each core substitutes its own value
  (`Metronome.Core`); the machine reads the core-local value.  The bridge states
  the machine's value for those slots (`src_slot_1/2/3`) instead of pretending the
  global slot is the machine's.
* **Line-relative guards (27..31)** are *not* a disagreement: the cut's global
  vector is 0 there and the chip top supplies `g_line` per line; the machine
  evaluates the same five conditions on the reading line.  Bridging the bundle
  (`lineGuardsOf`/`lineGuard`) is a **gap** (below).

### Gaps (glue)

1. **Line-relative guard bundle — closed in item 4N** (`lineGuard_bridge` below).
2. **Control registers and mailbox — closed in item 4N** (`ctrl_bridge`).  **Output
   pins — closed in the second 4N pass** (`out_bridge`, `pins_bridge`; see the 4N
   subsection).
3. **Table decode.**  The 28 source and 50 guard entries that go through
   `parsePort` are the hypothesis, not kernel-checked (see above); the compiled
   check is planned in the evidence dir.

### 4N: control, flags, mailbox and `g_line`

Evidence: `data/raw/lean_bridge_glue_v4_20261121b/` (`axioms.txt`, `commands.log`,
`Axioms.lean`, `glue_names.txt`, `build_glue_fresh.log`).  All 58 new theorems are in
`Metronome/Bridge/Glue.lean`; both specs are untouched (`git diff --quiet HEAD -- src`
and no edits under `Metronome/Machine/`, `Metronome/Glue.lean`).

**Abstraction map (new).**

| cut | machine |
|---|---|
| `GlueInput` control strobes | `ctrlInOf`: `hostOut := if hostOutWrite then some hostOutData.toNat else none`, `hostInRead := anyRead rdHin`, `conflict/memhaz/cwovr` |
| `GlueInput.wFlags` | `unitsInOf`: `flag := if flagsWrite then some (flagsValue, flagsIndex.toNat) else none` |
| `GlueState` registers | `CtrlRegs`: `runG/irqEn/inB/inv/invp/outB/outv/db/irq` = `ctrl.*`, `fl/flp` = `units.f/fp` |
| ERR leaves | `ErrTerms`: the three sticky bits, and `any6 tLate/any6 tOvr/any4 lTapmiss/any2 sStarved` = the machine's thread/line/stream reductions |
| `lineGuardsOf` | new `symOf` (line `IN`), `sp`, `pinA`, `pinB` per line |

**Theorems (58).**

* Bits/flags toolbox: `bitAt_eq_nbit'`, `bit_eq_nbit'`, `nbit_eq_testBit`,
  `getLsbD_eq_testBit`, `bitAt_eq_getLsbD`, `bv_toNat_slice` (`bv n x.toNat` is the
  cut's low slice), `testBit_succ_of_even`, `testBit_add_two_pow`,
  `testBit_sub_two_pow` (`Nat` bit facts), `setBit_getLsbD`, `setFlag_getLsbD`,
  **`setBit_eq_setFlag`** (the machine's `Util.setBit` on 16 flags is the cut's
  `setFlag`, via `BitVec.eq_of_getLsbD_eq`), `list_any_or`.
* Control: **`err_bridge`** (`Glue.err` = `Machine.errAny`), one lemma per register
  field — `ctrl_run`, `ctrl_irqen`, `ctrl_irq`, `ctrl_db`, `ctrl_inb`, `ctrl_inv`,
  `ctrl_invp`, `ctrl_outb`, `ctrl_outv`, `flags_f`, `flags_fp` — and the assembled
  **`ctrl_bridge`**: `CtrlRegs ms s → CtrlRegs (ctrlStep hw i ms) (Glue.step s i)`,
  where `ctrlStep` is `ms` with `ctrl := ctrlNext …` and
  `units := unitsNext …`.  Every field is proved for all states; there is no sticky
  register in the cut (`CtrlRegs` does not mention `conflict/memhaz/cwovr`).
* `g_line`: `nbit_quad_low`, `nbit_quad_shift` (base-4 extraction: bits `0,1` of
  `a + 4b` are `a`'s for `a < 4`; bits `2+i` are `b`'s), `symOf_lt`, `inn_bit`,
  `sp_bit`, `pinA_bit`, `pinB_bit` (one per packed `LineGuards` field), `line_guard_0
  … line_guard_4`, and the assembled **`lineGuard_bridge`**:
  `guardV e (27 + j) = bitAt (Glue.lineGuard e.l (lineGuardsOf e)) j` for `j < 5`.
* Output packing stage: `bitVec1`, `pack4b`, `bindPack`, `selPack`, `segPack`,
  `commPack` and their extraction lemmas (`bindPack_line/bound/live0/live1`,
  `selPack_0..2`, `segPack_0..3`, `commPack_0..3`, `pack4b_0..3`), all by `bv_decide`
  on symbolic `BitVec`/`Bool` (no `native_decide`).

**Side conditions (new).**

* `GuardTable`, `Env.hlvl` as before; `lineGuard_bridge` also needs `e.l < 4` (a line
  index range fact, not a cut disagreement).
* `CtrlWr hw i`: the five `CTRL` bytes the cut decodes are the machine's `hwByte`s,
  present exactly when the cut's strobe is high, with the cut's data byte.  This is
  the host-map decode, already proved from the cut's side by `hostmap_check.py`.
* `ErrTerms ms i`: the cut's `ERR` leaves are the machine's sticky/thread/line/stream
  reductions (the `any6/any4/any2` bitmask reductions are the RTL's, so this is one
  hypothesis; `err_bridge` combines the thread `LATE`/`OVR` pair with `list_any_or`).
* `CtrlRegs ms s`: the registers currently agree (the induction hypothesis).

**Disagreements.** None found in the three groups.  The cut and the machine agree on
`RUN/IRQEN/IRQ/DB` (including the frozen-cycle hold `DB' = written | DB`), the mailbox
(`OUTB/OUTV` with the host-write priority, `INB/INV` with the read clear and the
`HOSTIN` priority, `INVP`), the flags (`F`/`FP`, including `FP` frozen), and the five
line-relative guards.  `AMBIGUITIES.md` entries 16 (`ERR` includes `CWOVR`) and 17 are
consistent with the cut; no new AMBIG entry was needed.

**Remaining gaps (output pins) — closed in the second 4N pass.**  The output-pin group
is now bridged (`outIdx_bridge`, `out_reg`, `oe_reg`, `out_bridge`, `pins_bridge`,
44 theorems, evidence `data/raw/lean_bridge_glue_v4_20261121c/`):

* **Abstraction.**  `ocOf e o` is the machine's decoded `OutCfg`; `outCfgOf e o` builds
  the cut's `Glue.OutCfg` from it, with the packed bytes as concatenations
  (`bindPack`/`selPack`/`segPack`/`commPack`/`pack4b`), and `idxNat e o` is the
  machine's `outIdx` written in the cut's shape (ms with a `LIVE`/`BOUND` `if`).
* **Decode, one lemma per field.**  `out_line`, `out_bound`, `out_live0`, `out_live1`,
  `out_sel0/1/2`, `out_comm`, `out_seg`, `out_pinA`, `out_pinB`, then `out_b0/b1/b2`
  (`b0 = COMMITTED[SEL0]`, `b1`/`b2` with the §12.1 `LIVE` substitutions) and
  `outIdx_machine`/`outIdx_cut`/`outIdx_bridge`.  `pack5_toNat` turns the cut's
  five-bit OR-packed index into the machine's `SEG*8 + b2*4 + b1*2 + b0` (via
  `or_shift`, i.e. `Nat.shiftLeft_add_eq_or_of_lt` on disjoint fields).
* **Table read.**  `readBit_bv`: `readBit (bv 32 v) k = nbit v k` for `k < 32` (the
  cut's `readBit` is the machine's `nbit`); `getLsbD_bv`/`nbit_bv` move between
  `getLsbD`, `nbit` and `testBit`.
* **Registers.**  `out_reg`/`oe_reg`: machine `OUT[o] = LUT[idx]`, `OEN[o] = OE[idx]`
  (`o < 14` / `o < 8`), both held in a frozen cycle and 0 out of reset, are the cut's
  per-pin `outNext`/`oeNext`.
* **Folds.**  `packBits_testBit`, `packBits_map_testBit`, `zip_self_map`, `outsOf_eq`,
  `outsOf_oe`, `oensOf_eq`, `take_range`, `packBits_lt`, then **`out_bridge`**:
  `(Machine.outNext …).1 = bv 14 (packBits (cut OUT))` and
  `(Machine.outNext …).2 = bv 8 (packBits (cut OEN))`, proved per bit with
  `BitVec.eq_of_getLsbD_eq`.
* **Pin buses.**  **`pins_bridge`**: `Machine.pinsOut` is the cut's `Glue.pins`, i.e.
  `uo_out = {OUT[13:8], IRQ, MISO}` with `MISO = TX[7]`, `uio_out = OUT[7:0]`,
  `uio_oe = OEN` (`BitVec.toNat_or` + `or_shift`).

**Side condition (new).**  `CvRange e`: `LINE`, `SEL0`, `SEL1`, `SEL2` of every output's
decoded configuration are below 4.  `Env.cv` is an arbitrary decoded `CfgView`, so this
is an interface hypothesis like `hlvl`; it holds for every `Machine.cfgView c`, whose
fields are `Machine.Util.nbits bytes 0 2`.  `SEG` needs no hypothesis (`seg = popcount
% 4 < 4` is proved).  No other side conditions beyond `GuardTable`/`CtrlWr`/`ErrTerms`/
`CtrlRegs` from the first pass.

**Disagreements.**  None.  In particular the unbound-pin case agrees: both readings use
`idx = 0` and so drive `LUT[0]`/`OE[0]` (the machine's `outIdx` returns 0, the cut's
`outIdx` is 0 and its `readBit … 0` is the entry) — the surprising-but-literal §8
reading recorded in `AMBIGUITIES.md` ("an unbound pin drives `LUT[0]`, not 0").



---

## 2. Debug (`Metronome.Debug` vs `Machine.Pins`/`misrNext`/`replayApply`/`captureEvent`/`dbgNext`/`resetStep`/`Pmem`)

Evidence dir (this pass): `data/raw/lean_bridge_debug_v4_20261121b/` (`Axioms.lean`,
`axioms.txt`, `debug_names.txt`, `commands.log`, `build_fresh.log`).  File extended:
`Metronome/Bridge/Debug.lean` (84 theorems, all prior names and statements kept).  Both
specs are untouched: `git diff --quiet HEAD -- src` exits 0 and nothing under
`Metronome/Machine/` or `Metronome/Debug.lean` was edited.  `lake build
Metronome.Bridge.Debug` (with `-DwarningAsError=true` from `lakefile.toml`) exits 0,
15.4 s for the module after deleting its olean (3-4 s incremental); `#print axioms` for all 84 theorems reports only
`propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`, no `native_decide` axiom
(the `slice_rise_fall` bit identity is a `Nat.testBit` proof, not a `bv_decide` one).
No `sorry` and no `native_decide` anywhere in the file.

### Abstraction map

Same `BitVec`↔`Nat` convention.  `Pins.level`/`previous` are stated at the `Nat`
level (`level_toNat`/`previous_toNat`), because the machine's `pinView` is `Nat`;
the machine's `lvl`/`prev` are the same `(x &&& ~mask) ||| (RLV &&& mask)` with
`mask = EMASK & {13{RPL}}` (`mask_toNat`).  A value that folds through `BitVec` and
`Nat` is bridged as `(cut).toNat = (machine value)` (`bv_toNat'`, `bv_self`) or as a
`BitVec` equality after `BitVec.toNat_eq`.

**The Option↔strobe abstraction (new).**  The machine carries the host link's write
and the drained core write (`cwRt`) as `Option HostWr` values (`hwByte`/`hwAt` in
`Machine/Host.lean`); the cut carries, per register byte, a combined strobe, a
host-source select and the two bytes.

| cut leaf | machine |
|---|---|
| `Port` (`strobe`, `host`, `hWd`, `cwData`) | one register byte's write |
| `Port.ok` | the winning byte: host byte if `strobe && host`, drained core byte otherwise, `none` without a strobe (§13.1) |
| `Port.hostAt k` / `Port.coreAt k` | the machine's host / drained-core `hwAt` option at byte index `k` |
| `pickByte hw cw r` | `dbgNext`'s local `pick`: host byte else core byte of register `r` |
| `byteWOf hw cw x r` | `dbgNext`'s local `byteW` (core write then host write, §13.1) |
| `writeBytes x p0 p1` | the cut's two-byte `hi ++ lo` write of a 13-bit register |
| `setByte13 x k v` | the cut's per-byte write on a 13-bit word (byte 1 is five bits wide) |

`emaskPort0/1`, `rlvPort0/1` are the cut's byte ports; `hostOpt2`/`coreOpt2` are the
machine's single host / single core option implied by a two-byte register's ports.  The
13-bit `setByte` correspondence is `bv13_setByte` (one write), `bv13_setByte_pair` (two
writes), on top of `setByte16_0_gen`/`setByte16_1_gen` and `nat_setByte0_13`/
`nat_setByte1_13` (the 16-bit → 13-bit truncation), and the assembled
**`byteW2_bridge`**: the machine's `Option` pair and the cut's two ports write the same
register.

### Bridge theorems

* Plumbing: `bitAt_eq_nbit`, `slice_toNat`, `nbit_eq_testBit`, `testBit_xor`,
  `nbit_getLsbD`, `nbit_xor`, `append8_toNat`, `bv_toNat'`, `bv_self`, `bv13_toNat`,
  `and_mod`, `and_nbits13`, `nbits_zero_pow`, `slice_ite`, `bne_zero`.
* §2 pins: `mask_toNat`, `level_toNat`, `previous_toNat`, `lvl_toNat`;
  **`rise_bit`/`fall_bit`** (the cut's `RISE`/`FALL` bit `k` is `PinView.rise`/`fall`
  of pin `k`, all `k`); `nbit_and_not`/`nbit_not_and` (`l & ~p`, `~l & p` bit reads).
* §13.2 replay levels: `replayLevels_toNat`; `and_nbits13` (the machine's
  `WB &&& EMASK` sees `WB[12:0]`).
* §1 reset: `reset_bridge` (the cut's `Reset.step` flop pair is `resetStep`'s
  `r1`/`rq`).
* §5/§9/9a.8 program memory: `we_exclusive`, `port_host`, `port_fetch`, `be_ne_zero`.
* §12.2 digest: `dataVec_toNat`, `shiftLeft_one_toNat`, `cut_misr_toNat`,
  `machine_misr_toNat`, `dbgNext_misr`/`dbgNext_men` (lifted `rfl` views),
  `mctl_clear`, **`misr_bridge`** (`MISR'` is the 32-bit shift/xor with poly
  `0x04C11DB7`, clear, `MEN && !FRZ`, same data vector) and **`men_bridge`**.
* §12.4/§13.1 capture/replay registers: `dbgNext_cen`/`rlp`/`emask`/`rlv`/`rlvp`/`dc`
  (lifted `rfl` views), `port_bit`, **`ectl_bridge`** (`RPL`, `CEN`), **`emask_bridge`**,
  **`rlv_bridge`**, **`dc_bridge`** (`dc_inc`, `bv_dc_inc_toNat`: the cut's 19-bit wrap
  check is the machine's saturating `min (DC+1) (2^19-1)`).
* §13.2 replay apply/late: `tick_toNat`, `interval_toNat`, `ge_eq`, `gt_eq`,
  `decide_le_of_lt`, **`apply_bridge`** and **`late_bridge`**: the cut's
  `RPL && !FRZ && WV && DC+1 ≥ WB.DC` and `DC+1 > WB.DC` are `replayApply`'s pair.
* §12.4 edge event: `foldl_bits` (the machine's `List.range n` fold is `x % 2^n`),
  `rise_fall_bit`, `edges_bridge` (the fold is the changed pins `l ^^^ p`),
  `rise_toNat`, `fall_toNat`, `xor_or_toNat`, `slice_rise_fall`, **`cev_bridge`**:
  `captureEvent`'s first component is `Ctrl.cev`.
* Assembled: **`dbg_step_bridge`** — one step of the debug block agrees field by field
  (`CEN`, `RPL`, `EMASK`, `RLV`, `DC`, `MEN`, `MISR`, and `RLVP` under `frozen = false`).
* One disagreement kept with witnesses: `rlvp_frozen_cut`, `rlvp_agree`,
  `rlvp_frozen_witness` (see below).

### Side conditions

* `hSH`/`hSC` on `emask_bridge`/`rlv_bridge`/`byteW2_bridge`: two host-selected (or two
  core-selected) byte strobes in one cycle.  The host link writes one register byte per
  cycle (§9) and the core drain carries one byte (§13.1), so the machine's two
  `Option`s cannot express two writes from the same source.  This is a statement about
  which cut inputs the machine can produce, not a cut/machine disagreement.
* Interface equalities only: the current `DbgSt` registers (`ms.dbg.rpl/cen/emask/rlv/dc/
  men/misr/frz`), `ms.out`/`ms.oen` = the digest input's `oOut`/`oEe`, the `MCTL`/
  `ECTL`/`EMASK`/`RLV` host bytes and `hwAt` options, `ms.streams[0].wb` = the record
  word, `cev`/`apply`/`frozen` equal to the cut's sampled flags.  Every field theorem is
  proved for symbolic states given those.

### Disagreements (with witnesses)

1. **`RLV`'s previous level in a frozen cycle — §12.3 vs the machine.**
   The cut holds `RLVP` while frozen (`rlvp_frozen_cut`), as §12.3's "the registers
   hold" says.  The machine's `dbgNext` sets `rlvp := d.rlv` unconditionally.
   Witness `rlvp_frozen_witness`: with `RLV = 0x0AA`, `RLVP = 0x155`, a frozen
   cycle with an `RLV` byte write leaves the cut at `0x155` while the machine's
   `rlvp` becomes `0x0AA` (the old `RLV`), and the machine's `pinView` then uses
   that value for the masked pins' previous level.  The agreeing fragment is
   `rlvp_agree` (an unfrozen cycle: both are `RLV`), and `dbg_step_bridge` states the
   `RLVP` field only under `i.frz = false`.  `AMBIGUITIES.md` has no entry for this; it
   is an RTL/machine reading difference on the machine side (the RTL holds `rlv_prev`
   with `if (!frz)`, as the debug cut's README records).
2. **Replay `late` — withdrawn (2026-11-21, orchestrator), and now proved.**  An
   earlier version of this note claimed `Machine.replayApply` uses `DC + 1 = WB.DC`.
   It does not: `Machine/Stream.lean` is `d.dc.toNat + 1 ≥ wbdc` and
   `late = ap && DC + 1 > WB.DC`, exactly §13.2 and the RTL (`replay_tick >=
   replay_interval`, `>`).  `apply_bridge`/`late_bridge` now prove the agreement;
   `cut_late_witness` remains as the cut-side witness.
3. No other disagreement was found in the fields bridged here.

### Gaps (debug)

1. **Same-source two-byte writes.**  A cycle with two host-selected (or two
   core-selected) byte strobes of the same 13-bit register is excluded (`hSH`/`hSC`).
   These cut inputs are not machine-representable (one host byte, one drained byte per
   cycle); if a future machine revision could source two, `byteW2_bridge` would need a
   second `Option` pair.
2. **Program-memory contents.**  The cut's `portAddr`/`be`/`wordAddr` are bridged
   as *addresses and strobes*; the memory word's content is the SRAM macro's
   contract in both readings (§9a.8), so nothing is claimed about a same-cycle
   fetch word.
3. **`PinView.lvl` range.**  `Env.hlvl : p.lvl < 2^13` (glue file) is an interface
   hypothesis (true for `Machine.pinView`, not proved here); the debug bridges take
   the `pinView` level/previous values as hypotheses (`rise_bit` etc.).
4. **`captureEvent`'s record.**  Only the `cev` component is bridged; the record
   `{DC[18:0], PIN[12:0]}` is a stream-side value (`recordToStream` bridge lives in
   `Bridge/Stream.lean`).
5. **Freeze/`FRZD`.**  `dbgNext`'s `freeze`/`frz`/`frzd` fields are not bridged here
   (the cut's `Ctrl` has no `FREEZE` register; `FRZ` enters as the sampled `frz`).

### Reproduce (this pass)

```text
cd code/tests/lean
lake build Metronome.Bridge.Debug        # 15.4 s fresh (olean deleted), 3-4 s incremental; exit 0 (-DwarningAsError=true)
lake env lean <this evidence>/Axioms.lean  # 1.8 s, exit 0, 84 `#print axioms`
git diff --quiet HEAD -- src             # exit 0
```

`commands.log` records the exact commands, exit codes and wall times; `axioms.txt` is
the `#print axioms` output (only `propext`, `Classical.choice`, `Quot.sound`).

---

## 3. Reproduce

```text
cd code/tests/lean
lake build Metronome.Bridge.Glue        # 37.9 s from scratch (olean deleted), exit 0 (-DwarningAsError=true)
lake env lean <evidence>/Axioms.lean    # 2.2 s, exit 0 (265 `#print axioms` lines)
git diff --quiet HEAD -- src            # exit 0
```

`commands.log` records the exact commands, exit codes and wall times;
`axioms.txt` is the `#print axioms` output for all 265 glue theorems.
