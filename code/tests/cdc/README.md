# Metronome pad-input CDC verification

Two independent checks of the asynchronous-input boundary of `tt_um_brentius_metronome` (SPEC v2 §1–2):

1. **Structural audit** of the elaborated RTL: every raw pad input reaches exactly one first-stage flop, and
   nothing else; the reset pin reaches only the reset synchroniser.
2. **Metastability-injection simulation**: each input edge may be resolved one clock cycle late (seeded, per pin,
   per edge), and the protocol-level results decoded from the chip's own pins must equal the unperturbed control.

```sh
source code/tools/env.sh
python -m pytest code/tests/cdc -q                 # default: audit, 3 mutations, guards, negative control, 2 scenarios
CDC_EXTENDED=1 python -m pytest code/tests/cdc -q  # add the v4 UART training/retransmit/reply scenarios
python code/tests/cdc/audit_cdc.py --json-out audit.json   # structural audit alone
```

Everything is simulator-only. Nothing here has been measured on silicon; see "Evidence classes" and "Limits".

## Evidence classes

Every claim below carries one of these labels (AGENTS.md vocabulary):

| Label | Meaning here |
|---|---|
| **structural audit of RTL elaboration** | read out of the Yosys netlist of `src/` after `proc; opt; opt_clean`; a claim about connectivity, not about timing |
| **RTL-simulated** | Icarus simulation of `src/` with the lockstep source list, the IHP SRAM behavioural models and the behavioural latch/gating cells (`cells_behav.v`) |
| **gate-level simulated** (RTL-simulated class applied to a routed netlist; not a separate AGENTS.md class) | the same bench on a routed Icarus netlist plus the IHP standard-cell models; run on the routed v4 netlist 2026-11-19, passed (see Status below) |
| **calculated** | closed-form number from the stated parameters, no simulation |
| **assumed** | a modelling choice or an input to a calculation that is not itself verified here |

## Structural audit (Yosys)

`audit_cdc.py` elaborates `tt_um_brentius_metronome` from the shared lockstep source list
(`code/tests/lockstep_v2/rtl_sources.py`, 19 files with the SRAM models and `SIM`/`COCOTB_SIM`/`FUNCTIONAL`/
`USE_IHP_SRAM`) and inspects the JSON netlist module by module. **Structural audit of RTL elaboration**, at
`HEAD b7b4068` plus the working tree of 2026-11-19.

Elaborated design: 24 modules, 58 distinct cell types, all classified. Run time ≈6 s.

| Check | Claim (**structural audit of RTL elaboration**) |
|---|---|
| `RAW_FANOUT` | Each of the 16 raw pad bits `{ui_in, uio_in}` drives **only** the matching D bit of the 16-bit first stage `s1`, in order `s1[k] = raw[k]` with `raw = {ui_in, uio_in}`. No other cell, port or output loads a raw bit. `s1` is a single 16-bit `$sdff` clocked by the rising edge of `clk`; its reset is the *synchronised* `rst_q`, not the raw pin. |
| `SYNC_CHAIN` | Each `s1` bit loads **only** the matching D bit of `s2`; no other load exists. `s2` drives `sp` bit-for-bit and also the functional logic (16 further loads, allowed, see below). `sp` (third stage) has 14 loads. |
| `RSTN_FANOUT` | Raw `rst_n` reaches exactly **two** pins, the active-low asynchronous clears `rst_m.ARST` and `rst_q.ARST` of the reset synchroniser, and nothing else: no combinational cell, no latch, no data pin, no output port. Both flops clear to 0 and shift a 1 through on rising `clk`, i.e. `rst_q` releases two edges after `rst_n` rises. |
| `RESET_NETS` | The synchronised reset `rst_q` reaches only reset terminals: synchronous resets of flops (10 `$sdff` + 2 `$sdffe` active-high + 45 `$sdffe` active-low at the top, through 3 comb cells) and the reset input ports of 27 submodule instances, plus the 2112 async-clear pins of the configuration latch bank (`cfg_dlhrq_beh.RESET_B`, fed by that bank's `rst_s`, not by `rst_n`). Combinational cones are followed; every terminal must be a reset pin (a `$print`-style observer is reported separately). |
| `NO_RAW_COMB_PATH` | `ui_in`, `uio_in`, `rst_n` and `ena` have no combinational path to `uo_out`/`uio_out`/`uio_oe` and reach no transparent latch. (`ena` is unused by the design besides a `_unused` sink.) |
| `CELL_TYPES` | Fail-closed: any cell type, sequential input pin or module without an explicit role raises `AuditError` and the audit fails. There is no "skip unknown" path. |

### Which fanouts the audit allows, and why

The design's documented contract is *two* flops (`s1`, `s2`) into functional logic plus a third (`sp`) for
edge detection. The audit therefore permits:

* **raw pad bit → `s1.D[k]` only.** Anything else would mean an unsynchronised use of an asynchronous pin, which is
  exactly what this check exists to exclude. A second load fails `RAW_FANOUT`; a combinational use also fails
  `NO_RAW_COMB_PATH`.
* **`s1` → `s2.D` only.** `s1` is the metastable stage; its value must not be consumed by logic.
* **`s2` → `sp.D` and → functional logic.** `s2` is the first stage the design is allowed to use (SPEC v2 says the
  protocol logic sees the two-flop version). Per-bit `s2` fanout beyond `sp` is counted and reported, not failed.
* **`sp` → functional logic (14 loads).** `sp` is a third, fully synchronised stage used for rise/fall detection;
  its fanout is reported for information.
* **`rst_n` → `rst_m.ARST`, `rst_q.ARST` only.** Any combinational use, any data pin and any other reset pin fails
  `RSTN_FANOUT`. The configuration latches need an *asynchronous* clear; they get it from the synchronised `rst_q`
  (through `rst_s`), so the raw pin is not fanned out to 2112 latch pins.
* **`rst_q` → reset terminals only** (synchronous and asynchronous resets, submodule reset ports, latch async
  clears). A data pin or an output port reachable from `rst_q` fails `RESET_NETS`.
* **Sub-cells and behavioural models** are resolved through their own module definitions (hierarchical
  combinational reachability), never assumed opaque. The two behavioural cells (`cfg_dlhrq_beh`, `cfg_lgcp_beh`)
  have explicit pin-role tables.

### Mutation tests (proof the audit can fail)

Three mutants are planted on a **temporary copy** of `src/` (never on `src/` itself), each must make the audit fail
with the named check. **RTL-simulated** is not involved: these are structural-audit runs.

| Mutant | Planted change | Expected finding |
|---|---|---|
| `raw_input_into_output` | `uio_out = o_out[7:0] \| {7'd0, ui_in[0]}` | `RAW_FANOUT` + `NO_RAW_COMB_PATH` |
| `s1_used_as_synchronised` | `pins_level` built from `s1` instead of `s2` | `SYNC_CHAIN` |
| `raw_rst_n_into_output` | `uio_oe = o_oe \| {7'd0, ~rst_n}` | `RSTN_FANOUT` |

`test_audit_fail_closed` additionally feeds an unknown cell type (`$frobnicate`, `sg13cmos5l_mystery_1`) and
requires `AuditError`.

## Metastability-injection simulation

The bench (`cdc_jitter_tb.py`) replays a lockstep protocol scenario, driving the raw pads at falling clock edges
with a 16.666 ns period (60 MHz, **assumed** board clock). Each input edge on a masked pin is resolved either in the
cycle it was driven (probability `1 - CDC_JITTER`) or `CDC_JITTER_DEPTH` cycles later (default 1, `CDC_JITTER` 0.5),
independently per pin and per edge, from a seeded RNG. This models a first-stage flop that resolves late; it never
models an *early* resolution, so it cannot invent an input the board did not drive. Reset participates too where the
scenario allows it.

Every scenario runs one **clean** pass and one pass per seed inside a single simulation, each starting from reset.
Results are decoded **only from the chip's pins**: SPI MISO (`uo_out[0]`) and the UART transmitter (`uo_out[2]` = O8).
The decoded protocol result must be identical for every pass; the cycle-exact pin trace is also compared, but its
divergence is reported rather than asserted, because a correctly-functioning design may legitimately shift by a
cycle.

| Scenario | Default | Stimulus and acceptance (**RTL-simulated**) |
|---|---|---|
| `spi_host` | yes | All 16 input bits jittered. Host load/readback at SCK = clk/16: an 8-byte data-RAM write, a CTRL/LINE configuration write, five exact readbacks covering RAM, registers and write-only configuration (reads 0), a second write burst, and RAM-retention re-read. |
| `uart_example` | yes | P5 only. Score-compiled 8N1 receiver at 531 clocks/bit (1.90 % below nominal 115 200 baud, **calculated**), 4 bytes; then the shipped `uart_tx.mas` example re-transmits the same 4 bytes on O8. |
| `spi_host_fast` | negative control | Sentinel write at clk/16, readback, overwrite at clk/2, readback; used only by `test_negative_control`. |
| `uart_rx_control` | `CDC_EXTENDED=1` | v4 firmware, 24 clocks/bit, P5 jittered; framing and retransmitted training bytes. |
| `uart_rx_baud` | `CDC_EXTENDED=1` | Same learner, alternating 24/25-clock bits (≈2 % baud error); a 1-cycle slip is ≈4 % of a bit. |
| `uart_tx_rx` | `CDC_EXTENDED=1` | Lockstep v4 stage 2: learn 8N1 framing, retransmit the training frames; status/error flags from CTRL. |
| `uart_reply` | `CDC_EXTENDED=1` | Lockstep v4 stage 2 reply: answer the held-out byte (`0x42`). |

<!--RESULTS-START-->
### Default-suite results (RTL-simulated, 2026-11-19)

Measured from `results/cdc_rtl_20261119/*.json`: `CDC_SEEDS=1,2`, `CDC_JITTER=0.5`, `CDC_JITTER_DEPTH=1`,
16.666 ns clock. "Edges" counts input transitions on the masked pins that the model resolved; "late" counts how
many of those were pushed one cycle out. Both passes of every scenario decode **identically to the clean control**.

| Scenario | cycles/pass | seed 1: edges / late | seed 2: edges / late | protocol decode | first pin-trace divergence |
|---|---|---|---|---|---|
| `spi_host` | 9 945 | 5 893 / 2 923 | 5 893 / 2 937 | equal: `data[0x1040] = a55a00ff817e33cc`, `CTRL` block `000001005a0001a200`, `HOSTIN/HOSTOUT = 3c00`, RAM re-read `a55a00ff817e33cc`, write-only `LINE.INC` reads `00000000` | cycle 3 806 (reported, not asserted) |
| `uart_example` | 58 522 | 17 / 10 | 17 / 6 | equal: RX `00ffa580`, TX on O8 `00ffa580`, both 4 bytes, 8N1 with 1 stop bit at 531 cycles/bit | none (trace bit-identical) |
| `spi_host_fast` (negative control) | 1 604 | 46 / 92 (2 cycles each) | — | **different, as required**: clean `[5a5a, a53c]`, perturbed `[5a5a, 5a5a]` (clk/2 overwrite lost) | — |

The UART example's pin trace is *bit-identical* under ±1-cycle jitter: at 531 cycles/bit one cycle is 0.19 % of a
bit (**calculated**), far inside the fixed-rate receiver's sampling window, and the O8 transmitter is driven by the
firmware's own timing. The extended UART scenarios run at 24 clocks/bit, where the same one-cycle slip is 4.2 % of a
bit (**calculated**), and there it *does* move the waveform:

| Extended scenario (1 seed, `results/cdc_rtl_20261119/extended/`) | cycles | seed 1: edges / late | protocol decode | first pin-trace divergence |
|---|---|---|---|---|
| `uart_tx_rx` | 202 213 clean, 80 151 jittered | 177 / 88 | equal: 11 training frames retransmitted on O8, status 1, framing `(1,8,0,11,1)`, ERRSUM 0 | cycle 172 494 |
| `uart_reply` | 204 517 clean, 80 151 jittered | 177 / 88 | equal: reply `0x42` on O8 after 11 training frames, ERRSUM 0 | cycle 174 749 |

So the tolerant UART example is a *weak* jitter test by construction (its timing margin is huge); the 24-clock
scenarios are the ones that would expose a one-cycle defect in the receiver's sampling, and they decode identically
while the output waveform shifts.
<!--RESULTS-END-->

### Negative control

`test_negative_control` proves the comparison can report a difference, using the `spi_host_fast` scenario:
a sentinel value is written at clk/16 (8 cycles of MOSI setup) and read back, then the same address is overwritten
at clk/2 — one cycle of MOSI setup — and read back again. Both readbacks must show both values in the clean pass.
With every MOSI edge resolved **two** cycles late (twice the ±1-cycle model, chosen so the effect is unambiguous),
the clk/2 overwrite is lost and the second readback still returns the sentinel, so `protocol_results_equal` is
`False` and the test passes only because the divergence was required (`CDC_EXPECT_DIVERGENCE=1`).

Two useful margin observations from the same scenario (**RTL-simulated**):

* A **one**-cycle late MOSI resolution at clk/2 does *not* corrupt the write: the synchroniser delays `SCK` and
  `MOSI` together, so a per-pin slip is common-mode until it exceeds the receiver's internal margin. The campaign's
  ±1-cycle model is therefore tolerated even at the fastest host clock this bench can produce.
* **SRAM keeps its contents across a reset** (SPEC v2: configuration is cleared, memories are not), so a corrupted
  write is invisible to a readback of the address it failed to write. The negative control therefore writes a
  sentinel first; a naive "write then read" control passes vacuously.

## Gate-level runner (RunPod)

```sh
# routed netlist as the argument; IHP PDK cell models found under /root/pdk by default
code/tests/cdc/gl_cdc.sh /workspace/results/TAG/final/nl/tt_um_brentius_metronome.nl.v \
    --out /workspace/results/TAG/cdc --scenarios spi_host,uart_example --seeds 1,2
code/tests/cdc/gl_cdc.sh --rtl --scenarios spi_host --seeds 1 --out ./cdc_rtl_dryrun   # no netlist
```

The runner needs `iverilog` on `PATH`, a Python with cocotb (`/root/ttvenv/bin/python`, else `python3` or
`$CDC_PYTHON`) and, for the gate-level mode, `sg13cmos5l_stdcell.v` plus the `*_udp.v` UDP models in
`--stdcell` (default `/root/pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog`). It writes
`environment.json`, one JSON per scenario, `sim/results_*.xml`, `pytest.log`, `run.txt` (command line) and
`run_meta.json` (date, netlist path and SHA-256, tool versions, rc, wall time) to `--out`, refuses to overwrite a
non-empty directory unless `--force`, and **exits non-zero on any mismatch**, because it propagates pytest's exit
status.

**Update 2026-11-19 (orchestrator): run on the routed v4 netlist** (SHA-256 `5cb8a739f119c92025cf1a645c90ef40269a44d57da8e600a78076f6f75ecb3d`, pod `ee2cb09mzouzot`, Icarus 13.0): `gl_cdc.sh NETLIST --out ...` rc=0 in 92 s; spi_host and uart_example protocol results equal across seeds 1,2 (SPI pin trace diverged from cycle 3,806, so jitter took effect; the UART pin trace did not change); the negative control diverged as required. Gate-level simulated, zero delay. Evidence: `data/raw/hwv_routed_20261119/gl_items23.tgz` (`gl/` extracted beside it). The text below predates the run.

**Status at delivery: the gate-level run for the v4 netlist had not happened yet.** No routed v4 netlist exists in this
checkout, and no RunPod run was made for this item. What *has* been done (gate-level harness smoke on the old v1 netlist only; no logs were retained from that smoke, so treat it as unevidenced - review S7):

* `bash -n gl_cdc.sh` passes; the `--rtl` mode was executed end to end on this machine
  (3 tests, rc=0, JSON + XML + `run_meta.json` written).
* The gate-level code path was executed locally against the **archived v1 routed netlist**
  (`code/.build/template_saved_v1_gl/tt_um_brentius_metronome.nl.v`, SHA-256 `b0ab7252…99d6e5e8`) with the local
  std-cell models (`code/.build/template_gl_models`): the bench compiled with `sg13cmos5l_stdcell.v` + `*_udp.v`,
  ran, decoded the sentinel and payload readbacks correctly, the negative control diverged as required, and the
  runner returned 0. That exercises the build/elaboration/output path, **not** the v4 netlist and not routing.

### How jitter is injected at gate level

The bench is pin-level in both modes, so jitter is always injected **at the stimulus**: the DUT's pads are driven
one cycle later than the ideal edge. In gate level the first-stage `s1` flip-flop is a real `sg13cmos5l` standard
cell inside the netlist and is never forced from the testbench — the delayed pin is captured by the actual
gate-level synchroniser and propagates through the real netlist, and the decode still comes only from `uo_out`.
This is the same "late resolution" outcome as in RTL, not a model of metastability: the std-cell models are
unit-delay functional Verilog (no SDF), so a cell that would resolve to an intermediate level, the input aperture
and any routing delay are not represented. A GL run therefore repeats the *protocol tolerance* claim on the real
netlist; it does not turn the structural audit into a timing claim.

## Evidence set

<!--EVIDENCE-START-->
One canonical set, from the final default run: **`results/cdc_rtl_20261119/`** (58 KB, JSON/log/XML/txt only, no
binaries). Recorded in `results/cdc_rtl_20261119/run.txt` and `environment.json`:

| Field | Value |
|---|---|
| date | 2026-11-19T15:49:48Z start, suite ended 15:52:30Z |
| result | `10 passed in 162.63s (0:02:42)`, exit status 0 |
| command | `source code/tools/env.sh` then `python -m pytest code/tests/cdc -q -p no:cacheprovider` |
| revision | branch `metronome-v4.0`, HEAD `b7b4068` + uncommitted v4 working tree; `src/` unchanged |
| tools | Python 3.12.10, cocotb 2.1.0, Icarus Verilog 14.0 (devel) s20260301-638-ge072b3334-dirty, Yosys 0.70+190 (git sha1 485b63564), OSS CAD Suite 2026-10-22 |
| host | Windows 11 Enterprise, Intel Core i5-1245U |

Contents: `environment.json` (argv + versions), `audit.json` + `structural_audit.txt`, three `mutation_*.json`,
`spi_host.json`, `uart_example.json`, `spi_host_fast-negative-control.json`, `pytest.log`, the cocotb JUnit XML per
scenario under `sim/`, the two margin probes under `probes/` (`FINDINGS.md`), and the separate 1-seed extended run
of `uart_tx_rx`/`uart_reply` under `extended/`. The 5.1 MB Icarus build product (`sim/sim.vvp`) was deleted after
the run; `.gitignore` keeps `*.vvp`, `sim_build/`, `build/` and caches out of the tree.
<!--EVIDENCE-END-->

Reproduce with `source code/tools/env.sh && python -m pytest code/tests/cdc -q` from a fresh checkout (the
simulator build is always rebuilt into the output directory). Run time is dominated by Icarus on the full chip:
**2 min 43 s** for the whole default suite on the idle host above, and **4 min 5 s** when the same suite shared the
host with other work — both well under the 10-minute budget, leaving room for the heavier `CDC_EXTENDED=1`
scenarios. `CDC_SIM=verilator` is honoured but was not usable here: this OSS CAD Suite has no C++ toolchain and no
Perl driver for Verilator (checked 2026-11-19), so the default is Icarus.

## Limits

* Structural claims are about the **optimised elaboration** of `src/` at the stated revision, not about the routed
  netlist. A gate-level structural re-run would need the Yosys/harden netlist and the PDK liberty; the audit does
  not read SDF.
* The audit proves connectivity, not duration: it cannot show that `s2` is sampled by the receiver at the intended
  edge, nor that the reset release meets recovery/removal. **Assumed** by SPEC v2.
* The jitter model is a whole-pin delay. It does not model a flop that resolves to the *old* value and later
  changes within the cycle, metastability propagation, or correlated (common-mode) delays between pins. Correlated
  delays are in fact the benign case (see the negative control) and are only reported.
* Only the pins listed per scenario are jittered; `spi_host` jitters all 16 input bits, the UART scenarios jitter
  the data pin only (host SPI timing held fixed) to keep the run affordable.
* Protocol acceptance is absolute (expected byte sequences), not a comparison against the reference model binary;
  the reference-model equivalence of the same stimulus is the lockstep suite's job (`code/tests/lockstep_v2/`).
* **Assumed** 60 MHz clock (16.666 ns) and the pin map of `info.yaml`; the design is not characterised for
  input-edge rate or aperture, so no MTBF figure is claimed. An MTBF would need IHP flop characterisation, the
  routed resolution time and measured edge rates.
