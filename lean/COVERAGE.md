# Coverage and closure inventory for the Lean cut suite

Status: generated inventory for Metronome v4 (item 4M), 2026-11-21.
Tool: [`lean/coverage_check.py`](coverage_check.py).
Evidence: `data/raw/lean_coverage_v4_20261121/` (`coverage.json`,
`uncovered.txt`, `closure.txt`, `summary.txt`, `tools.log`).

This file answers two questions about the existing proofs, not new ones:

1. **Coverage** — which elaborated cells does each cut's extracted cone read,
   and which cells of the used instance tree does no cut read?
2. **Closure** — for every net a cut leaves free, where does that net come
   from, and is its source itself proved?

It is an inventory, not a gate: the CLI exits 0 whenever the run completes.
`--strict` turns the inventory into a gate (exit 1 for any UNCLOSED leaf or any
uncovered non-black-box cell) for a future checkpoint.

## Reproduce

```powershell
$cad = "$env:USERPROFILE/tools/oss-cad-suite"
$env:PATH = "$env:USERPROFILE/.elan/bin;$cad/bin;$cad/lib;$env:PATH"
python lean/coverage_check.py `
  --artifacts-dir data/raw/lean_coverage_v4_20261121
```

Use `%USERPROFILE%/.elan/bin` (not `.lean`) on this machine. The artifacts
directory must not exist. Yosys runs with a timeout (`--timeout`, default
300 s). No Lean proof is run; the run takes about two minutes on a 10-core
i5-1245U.

This evidence run:

```text
python lean/coverage_check.py --artifacts-dir data/raw/lean_coverage_v4_20261121
exit 0, 130.1 s wall clock
```

Tool versions are in `tools.log`: Python 3.12.10, Yosys 0.70+190
(git 485b63564), Windows 11.

## Method

### Elaboration

One Yosys elaboration supplies both the cuts and the cell universe:

```text
read_verilog -I src -D USE_IHP_SRAM <src/*.v>
hierarchy -check -top tt_um_brentius_metronome
proc; opt_clean; write_json design.json
```

`-D USE_IHP_SRAM` is the recipe `mem_check.py` and `debug_check.py` use and the
hardened configuration in `src/config.json` selects. The other checkers
elaborate without it; the only difference is that `md2_pmem`/`md2_dmem` contain
the IHP macro instance and its three wrapper gates instead of the behavioural
array. Their extraction reads chip-top logic and the arbiter/wrapper, which is
identical in both elaborations, so one design is used for the inventory.
`USE_IHP_CELLS` is not defined: the latch bank keeps its behavioural
`cfg_lgcp_beh`/`cfg_dlhrq_beh` cell models, exactly as the bank cut sees it.

### How the per-cut sets were obtained

No checker is re-implemented. `coverage_check.py` imports the 16 checker
modules and calls their own extraction entry points against the elaborated
`modules` dictionary:

| cut | entry points called |
|---|---|
| `verify/config` | `verify.lean_transition` (arbiter + write stage) |
| `verify/host` | `verify.lean_host` (`wr`/`bitc`) |
| `verify/decode` | `verify.lean_decode` (host/core configuration decode) |
| `verify/corequeue` | `verify.lean_core_queue` (pending-write queue) |
| `bank` | `bank_check.extract_bank` (includes `verify.check_bank_mask`) |
| `hostcmd` | `hostcmd_check.extract_host` |
| `corectl` | `corectl_check.extract_pick/freeze/strobe/extract_sticky_bit` |
| `hostmap` | `hostmap_check.extract_all` |
| `hostread` | `hostread_check.extract_read/rdval/rdval_dontcare/miso` |
| `spipins` | `spipins_check.extract_pins` |
| `mem` | `mem_check.check_mem_top/check_dmem/extract_mem` |
| `thread` | `thread_check.extract_thread_module/extract_thread_inputs` |
| `stream` | `stream_check.extract_stream` (CAP=1 and CAP=0) |
| `units` | `units_check.extract_counter/shifter/lfsr/acc/sel/acc_sel` |
| `moves` | `moves_check.extract_moves/extract_sticky` |
| `line` | `line_check.extract_line` |
| `core` | `core_check.extract_core` (C=0 and C=1) |
| `debug` | `debug_check.extract_all` |
| `glue` | `glue_check.extract` |
| `hostpins` | `spipins` + `hostcmd` + `hostread` + `hostpins_check.extract_read_noaddr` |

Only the extraction runs; the Lean emission and proof steps are skipped.

The binding methods of the shared adapter are wrapped before extraction:
`expression`, `_bit_bool` and `bool_of` (a cone root — the thread and glue cuts
use the one-bit forms), `free`/`leaf`/`input`/`opaque`/`bind_bits`/`leaf_bits`/
`overwrite` (free leaves, including whole-bus `overwrite`s), `register` (owned
state) and `alias` (a definitional alias, not a new assumption). The wrapper
also wraps each concrete cone subclass in the checkers, so overrides such as
`$pmux`, `$logic_not`, `$reduce_or` and the line cut's layered `expression` are
not missed. It records only after the original call succeeds, so a failing
extraction adds nothing, and it never changes a binding.

Each cone object gets a stable identity. `id(cone)` is **not** used: the line
and thread cuts build one cone per layer/pin, and CPython reuses an `id` after
garbage collection, which would merge unrelated cones. Roots and leaves are
therefore grouped per cone object, not per module. A net that is a root of one
cone may be a leaf of another (the line cut's layers, the glue cut's output
index); grouping by module would stop the walk at the wrong net and understate
coverage.

A cut's **covered cells** are then a read-only walk: from every recorded root
bus, follow Yosys drivers backwards, stop at a bound leaf, at any register
output, at a submodule output pin and at constants, and collect the visited
combinational cells. The register cells whose inputs were roots are added as
owned cells. A module-level cut (bank, host, thread, stream, line, core, mem,
counter/shifter/LFSR/accumulator) applies to every chip-top instance of that
elaborated module, because the proof is about the parameterised module.

The structural credits are added because the checkers verify these cells
without a cone:

* `bank_check.extract_bank`/`verify.check_bank_mask` check every bank clock
  gate and latch, so the `cfg_lgcp_beh`/`cfg_dlhrq_beh` instances in the bank
  are marked covered by the bank cut.
* `mem_check.check_dmem` and `debug_check._pm_macro_check` check the SRAM
  wrapper gates (`A_MEN = ren | we`, `A_REN = ren & ~we`) and every macro pin
  connection, so the wrapper cells of `md2_pmem`/`md2_dmem` are marked covered.
* `glue_check.emit_outputs` binds each `o_out`/`o_oe` register's Q bus as `cur`
  and proves its reset-released D cone (`find_register` is a structural lookup,
  not `cone.register`), so those register cells are credited to `glue`.
* `debug_check.extract_reset` reads `rst_m`/`rst_q` through `_adff` and proves
  both next states, so those two registers are credited to `debug`.
* `verify.check_core_queue_top` expands the arbiter `core_valid` net to
  `cw_pending & ~frz & cw_is_cfg` and requires the `$not` on `frz`; that gate
  tree is credited to `verify/corequeue`.

### The cell universe

`instance_tree()` walks from the chip top through every non-black-box submodule
instance and counts every cell occurrence, including instance shells and the
three SRAM macro instances. Cell models of the two library cells
(`cfg_lgcp_beh`, `cfg_dlhrq_beh`) and the SRAM macro modules are boundaries:
the tree does not descend into them and they are counted with their contract.
Coverage is by cell occurrence, not by bit: a cell read by at least one cut
cone (any bit of its output) counts as covered. Two cuts reading the same cell
both get the credit, and overlaps are listed in `coverage.json`.

A cell is **covered** if it is in a cut cone, in a structural check above, or
is an instance shell of a module some cut covers. It is a **black box** if it
is an SRAM macro (stated contract, counted separately). Everything else is
**uncovered**. Uncovered cells are grouped by module and by the Yosys `src`
attribute (`file:line`), with counts.

### Closure classification

Every recorded free leaf is classified per bit, recursively through
hierarchy, by the ultimate source of the driving net:

| category | meaning |
|---|---|
| `pin` | top-level input pin (`ui_in`, `uio_in`, `rst_n`, `ena`, `clk`) |
| `owned_register` | output of a register whose next state some cut extracts |
| `covered_cone` | output of a combinational cell in a cut's cone, or of a cell credited by a named structural check |
| `bank_latch` | latch or clock-gate output inside the configuration bank (bank cut, structural check) |
| `macro` | output pin of an SRAM macro black box (stated contract) |
| `module_input` | module port resolved through the chip-top instance (fallback; no leaf needed it) |
| `constant` | tie-off (`0`/`1`) |
| `UNCLOSED` | driven by a cell no cut covers, an unowned register, or undriven |

A leaf bus is UNCLOSED if any of its bits is unclosed. A bus that mixes
categories (a `cfg` slice with latch bits and mask-zero tie-offs) is shown as
`bank_latch+constant`; the per-bit count is in `coverage.json`. The detail
names the owning cut and cell.

## Result

```text
22 elaborated modules, 8962 cell occurrences in the used instance tree
8129 cells covered by a cut cone or a named structural check
   3 cells are SRAM macro black boxes (stated contract)
 830 cells uncovered
coverage = 90.74 %
```

```text
597 free leaves (6824 leaf bits) across the 20 cuts
 35 UNCLOSED leaves (49 bits)
```

All non-top modules are fully covered: `md2_line` 249/249 per instance,
`md2_thread` 38/38, the cores 212/212 and 211/211 (C=0 and C=1),
the streams 171/171 and 282/282, the units, the host, the arbiter/stage, the
data-RAM arbiter, the bank and the SRAM wrappers. The 830 uncovered cells are
all in the chip top.

### Per cut

`cells` is the number of distinct cells read per module type; a module-level
cut applies to every chip-top instance of that module. `cones` is the number of
adapter instances (one per layer, byte, register or field).

| cut | modules | cones | cells | registers | leaves |
|---|---|---:|---:|---:|---:|
| `verify/config` | `md2_cfg_arb`, `md2_cfg_stage` | 2 | 23 | 6 | 12 |
| `verify/host` | `md2_host` | 1 | 19 | 2 | 6 |
| `verify/decode` | top | 3 | 72 | 0 | 2 |
| `verify/corequeue` | top | 1 | 41 | 5 | 7 |
| `bank` | `md2_cfg_cells` | 284 | 568 | 0 (latches structural) | 2 |
| `hostcmd` | `md2_host` | 1 | 77 | 9 | 7 |
| `corectl` | top | 4 | 57 | 3 | 9 |
| `hostmap` | top | 72 | 167 | 6 | 17 |
| `hostread` | `md2_host`, top | 4 | 217 | 11 | 59 |
| `spipins` | top | 1 | 6 | 3 | 3 |
| `mem` | `md2_mem` | 2 | 121 | 15 | 17 |
| `thread` | `md2_thread`, top | 61 | 443 | 7 | 41 |
| `stream` | `md2_stream` (CAP 1 and 0) | 54 | 453 | 26 | 44 |
| `units` | `md2_counter`, `md2_shifter`, `md2_lfsr`, `md2_acc` | 18 | 342 | 11 | 36 |
| `moves` | top | 38 | 1190 | 3 | 20 |
| `line` | `md2_line` | 36 | 249 | 15 | 61 |
| `core` | `md2_core` (C=0, C=1) | 2 | 423 | 14 | 34 |
| `debug` | top | 9 | 92 | 8 | 41 |
| `glue` | top | 181 | 323 | 11 | 117 |
| `hostpins` | top, `md2_host` | 7 | 226 | 14 | 62 |

The `bank` cut shows 0 registers because it uses `free`/`expression` over each
gate and verifies the latches structurally (`verify.check_bank_mask`), not
through `cone.register`.

### Overlaps

342 covered cells are read by more than one cut: 252 by two cuts, 65 by three,
23 by four and 2 by five. The largest pairs are `hostpins`/`hostread` 217,
`hostcmd`/`hostpins` 77, `hostcmd`/`hostread` 74, `corectl`/`moves` 42,
`hostmap`/`thread` 39 and `verify/host` with each host cut 19. Overlaps are
expected: the composed `hostpins` cut re-extracts the host cones, and
`moves`/`corectl` share the `w_cw` pick.

### Output pins

All 24 output bits are driven by covered logic:

* `uo_out[0]` is `miso`, ultimately `md2_host.tx[7]`, whose register is proved
  by `hostread`/`hostpins`;
* `uo_out[1]` is `irq`, the `glue` control register;
* `uo_out[2..7]` and `uio_out[0..7]` are `o_out[8..13]`, `o_out[0..7]`, and
  `uio_oe[0..7]` is `o_oe`; `glue.emit_outputs` proves each reset-released next
  state.

No output bit depends on an unproved cone.

## Closure: the 35 UNCLOSED leaves

These are grouped by the RTL that drives them. Every one is chip-top glue that
a module-level cut binds free; the module's own transition is proved, the
selection network that computes the free input is not.

| leaves | bits | driver (Yosys `src`) | assessment |
|---|---:|---|---|
| `mem.p_sel` | 2 | `project.v:485-486` | P0 port selector `(w_p0[13:8] == D_P0_AL/AH/W)`; `mem_check` takes `p_sel` free. Real logic not proved — SPEC_V2 §9a. |
| `units.md2_shifter.sel` ×2 | 2 | `project.v:396` | shifter op strobe `OPG(DG_SHK, D_SHSH)`; `units_check` binds `sel` free and only checks the wiring. Real logic not proved — SPEC_V2 §6. |
| `units.md2_acc.hit` | 6 | `project.v:281,283` | accumulator `HITG(DG_ACC)` hit mask; `units_check` takes `hit` free. Real logic not proved — SPEC_V2 §6. |
| `g_cn[0..2].op_lo/op_hi` | 6 | `project.v:409-410` | counter LO/HI strobes `OPG(DG_CNK, D_CNT*_LO/HI)`; `units_check.extract_sel` takes them as leaves and proves only the 2-bit `sel` decode from them. Real logic not proved — SPEC_V2 §6. |
| `g_lf[0..1].op_st/op_b0..2` | 8 | `project.v:425-428` | LFSR strobes `OPG(DG_LFK, D_LF*_*)`; same pattern as the counters. Real logic not proved — SPEC_V2 §6. |
| `line.sym_op` ×4 | 8 | `project.v:514` | TOP symbol-operation mux `(ws[13:8] == D_L_SYM) ? 0 : ... D_L_DBIT ...`; `line_check` binds `sym_op` free. Real logic not proved — SPEC_V2 §3. |
| `stream.cap_en/adv/rx_we/rewind/flush/clr_starved` (both variants) | 12 | `project.v:456,463,470-473` | stream control glue: `cen & ~replay`, `OPG(DG_SK, D_S*_ADV/RX)`, `(mctl & w[0]) | (hctl & h_wd[0])`, flush, clear-starved. `stream_check` binds them free. Real logic not proved — SPEC_V2 §6/§13.2. |
| `debug.d_wr_ectl/em0/em1/rlv0/rlv1` | 5 | `project.v:660,666-670` | DBG write strobes `h_* | (cw_drain & (cw_dbg_off == HO_DBG_*))`, including the `cw_dbg_off` subtraction. `debug_check` binds the merged strobes free. Real logic not proved — SPEC_V2 §12.4/§13.1. |

Count check: 1 + 1 + 1 + 6 + 8 + 1 + 12 + 5 = 35 leaves. 49 bits because
`p_sel` is 2 bits, `md2_shifter.sel` is 1 bit per instance (2), `hit` is 6
bits, `line.sym_op` is 2 bits per instance (8), and the rest are 1 bit each
across both variants/instances.

Every other free leaf closes:

| leaf category | leaves | what it means |
|---|---:|---|
| `owned_register` | 265 | the register's next state is extracted by some cut |
| `covered_cone` | 202 | the driving cell is in some cut's cone or a named structural check |
| `bank_latch+constant` | 95 | `cfg` slices: latch outputs of the bank plus mask-zero tie-offs |
| `constant` | 9 | explicit tie-offs |
| `macro` | 5 | program/data SRAM macro read data (stated memory contract) |
| `pin` | 4 | `ui_in`/`uio_in` at the synchroniser input |
| `UNCLOSED` | 35 | above |

The sum is larger than 597 because a bus can contain several categories.

## Uncovered cells: 830, all in the chip top

| cells | Yosys `src` | group | one-line assessment |
|---:|---|---|---|
| 276 | `project.v:281` | `hits`: 138 `$eq` + 138 `$and` | per-move group comparison and enable of `HITG` for the unit strobes; the `moves` cut proves only the picked words, not these hit vectors. Real logic not proved — SPEC_V2 §6. |
| 322 | `project.v:283` | `hits` priority mask: 115 `$and`, 115 `$logic_not`, 92 `$reduce_or` | the one-hot priority reduction inside `hits`. Same gap. |
| 132 | `project.v:307` | `dsteq`: 132 `$eq` | destination equalities inside `OPG` for 22 unit strobes. Same gap. |
| 16 | `project.v:514` | line symbol op mux | `sop` decode for the four line instances (feeds the UNCLOSED `sym_op` leaves). Real logic not proved — SPEC_V2 §3. |
| 12 | `project.v:472` | stream rewind/flush | `(mctl & w[0]) | (hctl & h_wd[0])` and the flush twin, both variants. Real logic not proved — SPEC_V2 §13.2. |
| 4 | `project.v:463` | stream `cap_en` | `cen & ~replay` (plus the `$not`), both variants. |
| 4 | `project.v:470` | stream `adv` | `OPG(DG_SK, D_S*_ADV)` reduce, both variants. |
| 4 | `project.v:471` | stream `rx_we` | `OPG(DG_SK, D_S*_RX)` reduce, both variants. |
| 2 | `project.v:473` | stream `clr_starved` | `hctl & h_wd[7]`, both variants. |
| 4 | `project.v:456` | stream `mctl` | `OPG(DG_SK, D_S*_CTL)` reduce, both variants. |
| 4 | `project.v:396` | shifter strobe | `OPG(DG_SHK, D_SHSH)` reduce, both instances. |
| 6 | `project.v:409` | counter `op_lo` | `OPG(DG_CNK, D_CNT*_LO)` reduce, three counters. |
| 6 | `project.v:410` | counter `op_hi` | `OPG(DG_CNK, D_CNT*_HI)` reduce, three counters. |
| 4 | `project.v:425` | LFSR `op_st` | `OPG(DG_LFK, D_LF*_ST)` reduce, two LFSRs. |
| 12 | `project.v:426-428` | LFSR `op_b0..b2` | `OPG(DG_LFK, D_LF*_B*)` reduce, two LFSRs. |
| 2 | `project.v:485` | P0 `p_sel` low mux | `(w_p0[13:8] == D_P0_AL) ? 0 : ...`; feeds `p_sel`. |
| 2 | `project.v:486` | P0 `p_sel` high mux | the second ternary stage. |
| 1 | `project.v:660` | `cw_dbg_off` | `{16'd0, cw_pending_addr} - {16'd0, HA_DBG_BASE}` for the DBG write strobes. |
| 15 | `project.v:666-670` | `d_wr_ecal/em0/em1/rlv0/rlv1` | `h_* | (cw_drain & (cw_dbg_off == HO_DBG_*))`, five 3-cell groups. |

Total: 276 + 322 + 132 + 16 + 30 + 32 + 4 + 16 = 830. No uncovered cell exists
outside `project.v`.

## What the result says

* **The design's datapath is covered.** All module internals — the CPU cores,
  lines, threads, streams, units, host link, configuration arbiter/stage,
  data-RAM arbiter and latch bank — are read by a cut, and every output pin is
  driven by proved logic.
* **The remaining hole is the chip-top strobe network.** The `moves` cut
  proves the 23 picked 15-bit words (FLAGS, CW, P0, HOSTOUT, the register
  groups, shifter/counter/LFSR/stream/line groups) and the 4 symbol picks, and
  the conflict mask. The units, streams, line, mem and debug cuts then take
  their own `op_*`/`sel`/`adv`/`p_sel`/`d_wr_*` strobes as free leaves and
  prove the transition conditioned on them. The cells that compute those
  strobes from the picked destination (`HITG`/`OPG`/`dsteq`, plus the DBG
  strobe merge and the P0 selector) are not inside any cone. That is exactly
  the 830 uncovered cells and the 35 UNCLOSED leaves.
* **A single "strobe network" cut would close the gap.** It would extract
  `hits`/`dsteq`/`OPG` for every group and the `d_wr_*` merge, and state them
  against a small independent predicate (destination/groups → each unit's
  enable, op and DBG byte). It would then replace the free leaves of the
  `units`, `stream`, `line`, `mem` and `debug` cuts, closing all 35 leaves and
  almost all 830 uncovered cells. Until then, these leaves are honest
  spec-level assumptions (they are specific, named nets, not arbitrary
  inputs), but they are not proved.

## Trust boundary

* **Yosys elaboration.** What the walk sees is the post-`proc; opt_clean`
  netlist. `opt_clean` removes unused cells, so a cell that only feeds nothing
  is not in the inventory. This is the same elaboration the checkers use.
* **The extraction is the checkers'.** Cell sets are derived from the roots
  and leaves the checkers' own adapters bind. The wrappers are observational:
  they record after a successful call and never change a binding. A checker
  that stopped binding a net would shrink its set here too, exactly as its
  proof would weaken.
* **Cell-level, not bit-level.** A cell counts as covered when one cone reads
  it; a wide cell shared between a proved and an unproved cone is not
  distinguished. This is the granularity the item asks for (its count is by
  cell). It can overstate coverage of a shared wide cell and understate the
  precision of a cone.
* **Root recording over-approximates slightly.** `_bit_bool` and `bool_of` are
  recorded as roots because the thread/glue cuts express one-bit cones through
  them. Those bits are always reached from a real root, so the walk's reachable
  set is unchanged; recording them avoids missing the one-bit register inputs.
* **Structural credit is labelled.** The bank latch/gate, SRAM-wrapper,
  output-register, reset-synchroniser and `core_valid` cells are covered by the
  named structural checks, not by a Lean cone. `coverage.json` keeps the
  `detail` string per cell.
* **The cell models are boundaries.** `cfg_lgcp_beh`/`cfg_dlhrq_beh` match the
  IHP library cells by the bank cut's stated trust; the SRAM macros have the
  memory contract (synchronous read, byte-masked write, registered read data)
  used by the mem/debug cuts. Neither is proved here.
* **Not modelled.** Physical timing, latch analog behaviour, the synchroniser
  metastability window, and the memory contents are outside all cuts and this
  inventory. Coverage of a cell is a statement about the proof boundary, not
  silicon correctness.
* **No Lean proof is re-run.** The inventory is only as current as the RTL and
  the extraction scripts; it should be regenerated after an RTL or checker
  change. The `coverage.json` records the exact command and tool versions.

## Limitations of this report

* `coverage.json` lists every covered cell for a sample-sized audit; the human
  reports (`uncovered.txt`, `closure.txt`, `summary.txt`) are the intended
  artifacts. At ~9000 cells the JSON is ~3 MB.
* The uncovered groups are grouped by the start line of the Yosys `src`
  attribute. Yosys assigns a function's body the function's source line, so a
  whole `hits`/`pick` expansion can share one line (the large groups above).
* The inventory does not judge whether each proved module is *fully* proved
  semantically; it only reports which cells its cones read. The checker
  READMEs' "Remaining gaps" remain the semantic complement.

## Update 2026-11-21 16:10: strict closure reached

With the op-strobe cut (`strobes_check.py`, `Metronome/Strobes.lean`) added to
`CHECKERS`/`CUTS`, `python lean/coverage_check.py --strict
--artifacts-dir data/raw/lean_coverage_v4_20261121c` exits 0:

- cells: 8,959 covered + 3 SRAM macro black boxes = 100.00 % of 8,962
  occurrences, 0 uncovered;
- closure: 633 free leaves, 0 UNCLOSED;
- output pins: 24/24 bits driven by covered logic.

"Covered" means read by some cut's extracted cone or credited by a named
structural check (see Method); it does not by itself mean the cross-cut
composition is proved in Lean. The SRAM macros are trusted to their stated
contract (registered read, byte mask).
