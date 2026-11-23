# Metronome reset and power-up verification

Campaign record: 2026-11-19, branch `metronome-v4.0`, HEAD `b7b4068` plus the uncommitted v3/v4 work.
`src/` was not changed by this campaign. Canonical results are in `evidence/20261119/` (see its
`MANIFEST.json` for tool versions and command lines). The gate-level part has **not been run** against a
routed v4 netlist: no such netlist was available locally and no pod was started.

Evidence classes used below, per `AGENTS.md`:

| Class | Meaning here |
|---|---|
| **verified in simulation against the reference model** | full-chip RTL (Icarus) drove the same per-cycle pins as `sim/reference/metronome2` and every compared output vector matched |
| **RTL-simulated** | full-chip RTL (Icarus) observed directly, without needing a model match for the statement |
| **structural inventory** | derived by Yosys elaboration of `src/` and checked fail-closed by a test |
| **calculated** | derived from source or the model by reading the code, not observed in a run |
| **assumed** | plausible but not established by the evidence in this folder |
| **not run** | prepared but not executed |

## Quick start

Run from the repository root. Put the OSS CAD Suite on `PATH` (`source code/tools/env.sh` in Git Bash;
Yosys needs `lib` as well as `bin` on `PATH` on Windows).

```sh
python -m pytest code/tests/xinit -q
XINIT_SEEDS=8 python -m pytest code/tests/xinit -q                         # heavier (this record)
XINIT_RESULTS_DIR="$PWD/code/tests/xinit/evidence/20261119/default" python -m pytest code/tests/xinit -q
```

The default run is 25 tests: 24 simulations (201,216 simulated cycles) plus the inventory check. It took
184.5 s on this host (391 s while four other agents were compiling), well inside the `~10 min` budget.
`XINIT_SEEDS` sets the number of `random_all` load/run seeds (default 3),
`XINIT_LOCKSTEP_SEEDS` the number of generated `random_N` traffic scenarios (default 2, ~30k cycles each, the
dominant cost). `XINIT_FULL_RANDOM=1` restores the trailing register dump in those generated scenarios.
`XINIT_CASES="mode:scenario:seed,..."` adds single cases (diagnostics: seed isolation, bisection with
`XINIT_PATHS`); `XINIT_PATHS` overrides the deposit list. Neither is used by the default campaign.

Environment (measured here): Python 3.12.10, cocotb 2.1.0, pytest 9.2.0, Icarus Verilog 14.0 (devel,
s20260301-638-ge072b3334-dirty), Yosys 0.70+190 (485b63564), 16 ns clock (60 MHz equivalent).

## What runs

| Test | Stimulus | Claim | Class |
|---|---|---|---|
| `test_inventory` | regenerate Yosys JSON from `src/` | snapshot identical to `inventory.json`; every non-reset site classified | structural inventory |
| `random_flops-smoke/spi_target/v4_config_write` | existing lockstep scenarios | reset + known 0 SRAM reaches the model | verified against reference model |
| `random_flops-random_N` | generated host traffic, ~30k cycles | same, with random flops | verified against reference model |
| `random_all-xinit_load_run` | full program + data load, both cores run, 5,599 cycles | same, with **all 2,627 declared storage regs and all 1,024 SRAM words random** | verified against reference model |
| `random_sram-xinit_load_run` | as above but only SRAM random | isolates the SRAM image | verified against reference model |
| `random_all-xinit_load_read` | write 2 words, read 5 bytes | a loaded read is independent of prior SRAM | verified against reference model |
| `random_all-xinit_reset_only` | reset and idle | reset alone reaches the model state, random SRAM or not | verified against reference model |
| `random_all-xinit_mid_reset` | deposit 2,625 regs mid-run, hold reset 5 cycles, re-read CTRL | reset recovers the host link and runtime registers | verified against reference model |
| `random_all-xinit_pulse_W_P` | same, but a W ps pulse P ps after a falling edge | asynchronous clear is captured; `rst_q` release latency recorded | RTL-simulated |
| `x_check-*` | no deposit: every flop and SRAM word keeps Icarus' X | no X reaches `uo_out`/`uio_out`/`uio_oe` after reset and after a load | verified against reference model (X-free pins) + RTL-simulated (internal) |
| `x_probe-xinit_read_probe` | write 5 bytes, read 5 | the host-contract counterexample: a lookahead read of an unwritten word puts X on MISO | RTL-simulated |

The default pulse sweep is W/P ∈ {(16000,1000), (4000,1000), (1000,1000), (100,1000), (10,1000), (1,1000),
(1000,7500), (1,10000)} ps. Phase is measured from the falling edge; the next rising edge is at 8 ns, so
P+W > 8000 ps straddles it and P > 8000 ps starts after it.

## Inventory of non-reset storage (item 1)

`inventory_flops.py` elaborates the v2 RTL with the behavioural IHP SRAM models
(`hierarchy -top tt_um_brentius_metronome; proc; opt; opt_dff; opt_clean`) and walks every module instance.
The session fixture does this on every run and `test_inventory` compares the result with `inventory.json`;
repeated regenerations match apart from Yosys' generated cell IDs, which the test excludes because they change
between otherwise identical runs. **Structural inventory.**

| | Records (module definitions) | Bits in the elaborated design |
|---|---|---|
| resettable storage | 168 | 3,191 |
| non-reset flops (`$dff`/`$dffe`) | 8 | 322 |
| non-reset clock-gate latches (`$dlatch`) | 1 (284 instances) | 284 |
| SRAM words | 2 arrays / 3 macros | 49,152 (1,024 words) |

The nine non-reset sites are `ir` in each core (64 bits each), the 284 `cfg_lgcp_beh` clock-gate enables,
`held_addr`/`held_data` in `md2_cfg_arb`, `addr1`/`data1` in `md2_cfg_stage`, and the SRAM read register
`dr_r`. Each has an explicit overwrite or validity-gating argument in `CLASSIFICATION`; a new site fails the
test until it is argued, an unknown storage cell type fails, an unexpanded black box fails, and a storage Q
bit without a source-declared `reg` path fails. **Structural inventory.**

The deposit list is the 2,627 declared register paths that cover storage. It accounts for exactly 3,797
bits, equal to the inventory's non-SRAM storage total, so no combinational net is deposited: a deposit on a net
that only aliases a storage bit is not a deposit on the flop, and after `opt_clean` a bit can carry both names.
The 6.5 MB Yosys JSON is an intermediate, now written to a temporary directory and git-ignored; pass
`--yosys-json OUT` to `inventory_flops.py` to keep it.

## Random power-up (item 2)

`random_all` sets every one of the 2,627 paths and all 1,024 SRAM words from a per-path seeded RNG before
`rst_n` is asserted (which happens before the first rising edge), then runs reset + SPI load in lockstep with
the model. **Verified in simulation against the reference model.**

| Run | Seeds | Result |
|---|---|---|
| `random_all-xinit_load_run` | 1, 2, 3 (default), 1–8 (heavy) | 0 mismatching cycles; 5,599 cycles per seed |
| `random_flops-random_N` | 1, 2 (default and heavy) | 0 mismatching cycles; 29,723–30,580 cycles per seed |
| `random_flops-smoke`, `-spi_target`, `-v4_config_write` | 1, 2, 3 | 0 mismatching cycles |

The heavy set (`evidence/20261119/heavy/`, 30 tests, 216 s) is the same suite with `XINIT_SEEDS=8`. A pass
means the reset and load really do overwrite every random bit that can be observed: the comparison covers
`uo_out`, `uio_out` and `uio_oe` on every cycle from 3 cycles after the last asserted reset, and the readbacks
inside the scenarios compare MISO contents, not just activity.

### The earlier divergence: confirmed and fixed

The partial work attributed a divergence to a bench deposit artifact but kept no log, and its deposit list
still contained the offending names. Re-running the heavier seed set reproduced it exactly: seed 5 of
`random_all` failed 138 cycles from 5,069 (the loopback pin stayed low while the model toggled). **RTL-simulated.**

Bisection (each run deposits only the named subset, seed 5): SRAM-only passes; all registers fail; the core
module's paths alone reproduce it; within the core, `{xt_o, xl_o}` plus the core state registers is the
minimal failing combination. `xt_o`/`xl_o` are `output wire` ports driven from the `xt`/`xl` flops. Depositing
them sticks on the port net and overrides the flop's value until the flop changes, which corrupts thread
selection.

Root cause: `declared_regs` read from `output reg disp_e,` to the **end of the ANSI port list**, so every
following port — including `output wire` ports (`xt_o`, `xl_o`, `mv_src`, `mv_dst`, `dbg_*`, `miso`,
`req_*`) — was treated as a declared reg. A second, smaller hole was that `opt_clean` merges combinational
nets into flop bits, so the 512-bit combinational `src`/`sv`/`gv` vectors named storage bits too. The parser
now reads the port list item by item, and a name is used only when every one of its bits is a storage Q bit or
a constant. The list dropped from 2,652 to 2,627 paths and now covers exactly the 3,797 storage bits; seed 5
and seeds 1–8 pass. The fix is in the inventory, not the RTL. **Structural inventory** + **RTL-simulated**.

## X-init (item 3)

`x_check` leaves every flop and every SRAM word at Icarus' X. After reset and after a full load, all three
output vectors are X-free on every compared cycle and every cycle equals the model; the reset-state check
also requires `cfg`, run control, flags, host registers, output data and enables to be exactly 0 (an X would
fail). **Verified in simulation against the reference model**, with the internal observation below
**RTL-simulated**.

Where X lives (recorded per run in the `internal` field of the JSON):

* `ir` in both cores is X at reset (`core0.ir.defined=false`) and defined after the load that first fetches
  (`true`); it is only consumed while `xv=1`, and `xv` is reset.
* All three SRAM `dr_r` read registers are X at reset and become defined when a consumer's read lands.
* The default stream configuration issues a data-RAM read of word 0 at cycle 6 (load/run) or 8 (reset-only)
  before the host writes anything; the monitor records it as an unwritten-word read. Under these stimuli it
  does not reach a pin. **RTL-simulated.**
* A host read of an unwritten word does reach a pin: `x_probe` writes 5 bytes at `0x123`, reads 5, and the
  lookahead read of word 74 (byte `0x128`) puts X on `uo_out` from cycle 1308 of that 1,347-cycle run
  (MISO is unobservable from then on). This is the host-contract counterexample, not an RTL defect.
  **RTL-simulated.**

X-init cannot prove the absence of X in silicon; it shows that the reset and load paths used here never
consume uninitialised storage. Storage that is not read in a scenario can stay X indefinitely (e.g. `ir` in
`reset_only`).

## Reset asserted mid-run, and the minimum pulse (item 4)

`xinit_mid_reset` loads and runs the loopback program, deposits random values on 2,625 paths (all except
`rst_m`/`rst_q`) one cycle before asserting reset, holds reset for 5 cycles, then re-reads the CTRL block over
SPI. The state check at reset+3 cycles is all-zero, the readback matches the model, and the outputs on every
cycle match. **Verified in simulation against the reference model.**

The pulse sweep gives the measured synchroniser behaviour (**RTL-simulated**):

| Width (ps) | Phase (ps) | Rising edges with `rst_q` low | Release |
|---|---|---|---|
| 1, 10, 100, 1,000, 4,000 | 1,000 | 1 | next rising edge |
| 16,000 | 1,000 | 2 | edge after that |
| 1,000 | 7,500 (straddles 8 ns) | 2 | edge after that |
| 1 | 10,000 (after the rising edge) | 1 | next rising edge |

**Minimum in simulation: 1 ps**, the 1 ps timescale floor; any non-zero pulse works because reset assert is
asynchronous (`rst_m`/`rst_q` clear on `negedge rst_n`, and the configuration latch bank's `RESET_B` is
`rst_q`). The synchroniser then holds `rst_q` low for one rising edge, or two when the pulse is still active
at a rising edge (that edge also clears `rst_m`). The chip has no internal reset stretcher, so the host must
hold `rst_n` low for at least the library cells' asynchronous-reset pulse width plus reset distribution skew.
**The silicon minimum is not established here: it is assumed to be set by the SG13CMOS5L cell pulse-width and
recovery/removal specifications, which this digital simulation does not model.** A pulse coincident with a
rising edge is a sampling race and is outside this sweep.

One abstraction caveat: the reference model resets on clocked `rst_n` (it holds reset for three edges after
one asserted step). For a sub-cycle pulse the RTL runs one edge earlier than the model. The bench compares
only after 3 idle cycles, when a constant input stream makes the sampled pipeline identical, so every pulse
case passes; a stimulus that changed an input within two cycles of a sub-cycle reset would expose the offset.
The reset-state assertion is independent of this. See `FINDINGS.md`.

## Host contract: what the host must initialise (item 7)

Reset establishes the chip's control state and configured outputs. It does not clear the SRAM, and it does
not need to: the only storage the host must load is memory contents. **Structural inventory** for the list,
**verified in simulation against the reference model** for the sequences that exercise it.

| Storage | Reset? | Host obligation | Evidence |
|---|---|---|---|
| Program SRAM, 2 × 256 × 64 bits (one per core) | no | write **all eight bytes** of every word the core can fetch: the instruction, its fall-through successor, branch targets and the fetch-ahead word (the core fetches on jump, load and dispatch, `md2_core.v`). The tested program pads each instruction with a self-jump. | calculated from the fetch logic; **RTL-simulated**: padded `xinit_load_run` passes with random SRAM |
| Data SRAM, 512 × 32 bits, byte-masked | no | initialise every **whole 32-bit word** a stream or replay reads, including padding past the stream's `LEN` and the next word after the last byte of a host read | **RTL-simulated**: `x_probe` (unwritten word 74 → X on MISO); monitor records every unwritten read |
| Data SRAM word 0 | no | the default stream configuration prefetches it after reset, before any host write; initialise it if the first stream byte must be defined | **RTL-simulated**: monitor records the read at cycle 6/8 |
| Configuration bank (2,112 latches), run control, host registers, flags, output registers, `misr`/`dc` | yes, asynchronous clear via `rst_q` | nothing; reset sets them to 0 and any earlier host configuration is lost | **RTL-simulated**: `reset_checks` all zero in every RTL case |
| `ir` (2 × 64 bits), SRAM `dr_r` (3), `held_*`, `addr1`/`data1`, 284 clock-gate latches | no | nothing: overwritten before use or gated by a reset control, each argued in `CLASSIFICATION` | **structural inventory** + **RTL-simulated** (`x_check` internal observation) |
| SRAM contents across a mid-run reset | no reset port on the macros (structural); retention after reset **not demonstrated** | treat as retained but unverified; reload if in doubt | **structural inventory** only. `xinit_mid_reset` randomises all SRAM words before the reset and re-reads only CTRL, so it does not show retention (review S2, 2026-11-19). The CDC suite's observation that a write-to-readback control passes after a failed write is consistent with retention (`code/tests/cdc/FINDINGS.md`), RTL-simulated |

A byte write initialises only that lane. A macro read is word-wide even when the consumer selects one byte,
so the monitor is conservative: it lists word/lane combinations read before being written, including reads
that do not affect a sampled output.

## Gate level (item 5) — run 2026-11-19 on the routed v4 netlist

**Update 2026-11-19 (orchestrator): run on the routed v4 netlist** (SHA-256 `5cb8a739f119c92025cf1a645c90ef40269a44d57da8e600a78076f6f75ecb3d`, pod `ee2cb09mzouzot`, Icarus 13.0): `run_gate.sh` rc=0, 5 passed and 1 skipped (the RTL-only inventory test) in 37 s; x_check reset_only/load_run/load_read and random_sram load_run/load_read ran 69/5,599/1,431 cycles each with 0 model mismatches and 0 X on pins; random_sram filled 3 SRAM arrays. Gate-level simulated, zero delay. Evidence: `data/raw/hwv_routed_20261119/gl_items23.tgz`. The text below predates the run.


`run_gate.sh NETLIST.NL.V OUTDIR` runs the pin-only variants against a routed, unpowered netlist and exits
non-zero if any case fails:

```sh
# On RunPod, PDK at /root/pdk/ihp-sg13cmos5l, python /root/ttvenv/bin/python
bash code/tests/xinit/run_gate.sh /workspace/results/TAG/final/nl/metronome.nl.v \
     /workspace/results/TAG/xinit_gl
```

It sets `XINIT_NETLIST`, `XINIT_STDCELL_DIR` (default
`/root/pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog`) and `XINIT_RESULTS_DIR`, then runs
`python -m pytest code/tests/xinit`. Output: per-case JSON and JUnit XML, `gl.log`, and `summary.json` with
the return code, wall time, netlist SHA-256, tool versions and pytest counts. `bash -n` passes; argument
handling was checked (exit 2 for a missing netlist).

Gate mode runs five cases: X-init for `reset_only`, `load_run` and `load_read`, plus the same two load cases
with every SRAM word randomised at power-up. Flop deposits and the hierarchy-based read/write monitor need
RTL hierarchy and do not run at gate level; there, every flop starts X, which is a stronger statement than a
random 0/1. A flattened netlist's SRAM array is not reachable through Icarus VPI (the escaped instance is
discoverable, its internals are not), so gate mode compiles a copy of the SRAM core model whose `initial`
block fills the array when run with `+xinit_random_sram`; the same binary serves the X-init cases without
that plusarg. This mechanism was checked by compiling the v1 template netlist
(`code/.build/template_saved_v1_gl`) and observing the three fills (512 + 256 + 256 words; no log of that check was retained, review S7); it has **not run
against a v4 routed netlist**, so no gate-level claim is made. Gate results are functional only (no SDF
back-annotation), and a passing gate simulation would not by itself prove silicon behaviour.

## Findings and gaps

See `FINDINGS.md`. In short: no RTL defect was found; the earlier seed-5 divergence was reproduced and root-caused to
a bench deposit on the `xt_o`/`xl_o` output-wire ports, fixed in the inventory (not the RTL); the reference model's clocked reset abstraction differs from the RTL by one edge for sub-cycle
pulses; the silicon minimum reset pulse width is not established; and gate-level and hardware evidence are
absent.
