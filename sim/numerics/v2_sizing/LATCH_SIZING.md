# Latch configuration bank sizing (Metronome v2, section 4.7)

Evidence class: **synthesized estimate** (Yosys, pre-placement, flat, no clock tree, no routing). Not placed, not
timed, not measured. Date 2026-11-12. Yosys 0.70+190 (git 485b63564, OSS CAD Suite 2026-10-22). Library
`build/pdk/sg13cmos5l_stdcell_typ_1p20V_25C.lib` (typical, 1.20 V, 25 C). Flow: `synth`, `dfflibmap -liberty`,
`abc -liberty`, `stat -liberty`. Reproduce: `source code/tools/env.sh && python sim/numerics/v2_sizing/area_latch.py`
(raw log `latch_area.log`, script `area_latch.ys`). BYTES=256 (2,048 bits, `CONFIG_BITS_TOTAL` in `code/md2/machine.py`).

## Result (um2)

| | Latch bank | Flop bank |
|---|---:|---:|
| Total | 66,287 | 140,899 |
| Per bit | 32.37 | 68.80 |

Saving 74,612 um2 (36.4 um2/bit), about 53% of the flop bank. Breakdown of the latch bank:

| Part | Count | Area |
|---|---:|---:|
| `dlhrq_1` latches (27.22) | 2,048 | 55,738 |
| `lgcp_1` clock gates (27.22), one per byte | 256 | 6,967 |
| Byte decode (nor2 x259, nand2/3/4, etc.) | about 300 cells | 2,259 (remainder) |
| Write/reset flops (`dfrbpq_1`): reset sync 2, we1 1, addr1 8, data1 8, data2 8 | 27 | 1,323 |

Flop bank: 2,067 `dfrbpq_1` (101,260), 2,048 `mux2_1` for the hold/enable path (37,159, 18.14 each), decode about 2,400.

## Findings against section 4.7 and the design ledger
- The latch bank is 32.4 um2/bit all-in (latch 27.2 + gate 3.4 + decode 1.1 + write flops 0.65). The flop bank is 68.8
  um2/bit, not 49 + 10: the enable costs a mux2 (18.14) per bit, so the saving per bit is 36.4, above the 32 the design
  assumed. Over 2,048 bits: 74.6k um2 saved against a flop-with-enable baseline (one clock gate per byte would also
  let flops avoid the mux; that comparison is not made here).
- Clock gates are 6,967 um2 for 256 byte groups. Fewer, wider groups (for example 16-bit) halve this at the cost of
  a 16-bit data path; not evaluated.
- Data fanout: each `data2` bit drives 256 latch D pins; the flow must buffer it (not in this estimate).

## Interface and timing (documented in `rtl/cfg_latch_bank.v`)
- `we`, `waddr`, `wdata` sampled on rising edge E1. `q` changes just after E2 = E1 + 1 cycle (2 cycles from the
  sampling edge to a register sampling `q` on E3). Verified for both banks (`test_latency`).
- E1 registers we/addr/data. Decode of the registered we/addr feeds the `lgcp` GATE only; GCLK comes only from the
  gate cell. E2 registers `data2`; the byte's latches are transparent during the high phase after E2 and close on the
  falling edge. `data2` changes only on rising edges, so it is stable around the closing edge: hold is a half-cycle
  check (falling edge to next rising edge, 8.33 ns at 60 MHz before skew), and the setup is also half a cycle plus
  data2 clk-to-q fanout delay. Not timed here.
- Reset: `rst_s` (async assert, 2-flop synchronised release) drives all latch RESET_B and `we1`. Writes sampled in the
  first two cycles after `rst_n` rises (while `rst_s` is low) are ignored. Writes to `waddr >= BYTES` are ignored.

## Verification (RTL-simulated, Icarus, behavioural cells)
`python -m pytest code/tests/v2_sizing/test_cfg_latch_bank.py -q`: 14 passed (6 cocotb tests on each of
`cfg_latch_bank` and `cfg_flop_bank`, plus Verilator `-Wall` lint of each). Tests: reset clears, single-byte write,
back-to-back writes (and same-byte rewrite), write in reset-release cycle ignored, out-of-range ignored, latency.
Lint waivers: none in the wrapper; `rtl/cells_behav.v` waives DECLFILENAME (two cell models in one file) and LATCH and
COMBDLY (the models are latches by definition). Behavioural `cfg_lgcp_beh`/`cfg_dlhrq_beh` match the liberty function
but have no delays, so they cannot show a gate race (see open items).

## Open items (not done)
- `sg13cmos5l_lgcp_1` is marked `dont_use : true` in the liberty file: instantiated cells are kept by Yosys, but the
  LibreLane flow (resizer, CTS, STA clock-gating checks, antenna) must be checked to accept it. Not run.
- The cells are instantiated, so no latch is inferred; the LibreLane lint step
  and `USE_IHP_CELLS` define handling (and whether the clock-gate output is treated as a clock net by CTS) need the
  physical run in `tt_latch_top/`. Back-annotated gate-level simulation of the write path is still required (4.7).
- Clock routing for 256 gated nets, and the flow's treatment of latch time borrowing, are unmeasured.
- `sg13cmos5l_dllrq_1` (29.03) exists but is not used.

## Update 2026-11-12: write path changed after the place-and-route skeleton (D24)

The measurements above were taken with the `data2` stage. `cfg_latch_bank.v` now loads `data1` only on a write and
drives the latches from it; `data2` is gone (8 fewer flops, about 0.4k µm² less than the table, calculated from the
`dfrbpq_1` area). The gate still opens at E2, so the write latency is unchanged, but `data1` has been stable since E1:
the latch opens on settled data and STA borrows no time through it, given the 2-cycle setup exception to the latch D
pins in `tt_v2_pnr/src/project.sdc`. The exception is valid only under the new **write spacing rule**: `we` is never
high on two consecutive rising edges (one host strobe per SPI byte guarantees it; a `COCOTB_SIM` check flags it).
Back-to-back writes are therefore no longer supported; `test_back_to_back` became `test_spaced_writes` and
`test_consecutive_write_flagged`. Flow result: HARDEN_LEDGER "v2 skeleton iterations", run `v2pnr_r4_20261112T0921`.

Back-annotated gate-level check (V2_DESIGN 4.7) of the routed skeleton: passed at slow, typ and fast corners
(`tt_v2_pnr/test/test_cfg.py`, evidence `data/raw/v2pnr_skeleton_20261112/v2pnr_r4_20261112T0921/sdf/`).
