# Metronome v2 RTL: synthesized area

## Current synthesis (D32, Sol continuation, 2026-11-12)

Baseline f945c29 plus the uncommitted full v2 RTL, including the host-stop/start-edge priority fix.
Command: `python code/tests/rtl_v2/area.py --log data/raw/v2_resume_sol_20261112/area_final.log` with the documented OSS CAD Suite on PATH.
Same Yosys/library/defines and flow as below. **Synthesized estimate: 274,908.2868 um? of standard cells**, 18,534 cells including three SRAM black boxes whose area is excluded.
Raw evidence: `data/raw/v2_resume_sol_20261112/area_final.log`; rounded hierarchy in `area_final_summary.log`.
The old result below is retained as earlier evidence. The current result is about 25.1k um? below the 300k synthesis budget;
placement, clock tree, timing repair, routing and final macro-inclusive fit are still unverified for this full RTL.
The library, source and tool hashes are recorded in this continuation's manifest.

## Previous synthesis (before D32)

Date 2026-11-12. Baseline revision f945c29 (branch metronome-v2.0) plus the uncommitted v2 RTL in `src/` and the
D28 spec update (start commit, `FIRST`). Command: `source code/tools/env.sh && python code/tests/rtl_v2/area.py`;
raw log `code/tests/rtl_v2/area.log`.

Tools: Yosys 0.70+190 (git sha1 485b63564). Library: `build/pdk/sg13cmos5l_stdcell_typ_1p20V_25C.lib` (IHP
sg13cmos5l, typical corner), as in the sim/numerics/v2_sizing runs. Flow: `synth -top tt_um_brentius_metronome`,
`dfflibmap`, `abc`, `opt_clean`, `stat -liberty`, hierarchical. Defines `SYNTHESIS USE_IHP_SRAM USE_IHP_CELLS`: the
configuration bank instantiates the library latch `dlhrq_1` and clock gate `lgcp_1` (their library area is counted);
the three SRAM macros are black boxes and are **not** counted.

**Evidence class: synthesized estimate.** Pre-placement, no clock tree, no timing-repair buffers or resizing, no
routing. The v2 skeleton's place-and-route added 24.3k µm² of repair buffers to 135k of synthesized cells (V2_DESIGN
4.8 / U10), so expect the placed figure to be higher. Whether the design fits and closes timing on the 8x4 die at
60 MHz is not shown by this number.

## Result

**Standard cells: 271,622 µm²** (18,222 cells; 1,031 flops `dfrbpq_1`, 2,084 latches `dlhrq_1`, 284 clock gates
`lgcp_1`). Macros beside it: 2 x 256x64 and 1 x 512x32 SRAM, 266.1k µm² (from LEF, V2_DESIGN 4.8).

| Block | Instances | µm² each | µm² total |
|---|---|---|---|
| `md2_cfg_bank` (2,084 latch bits, 284 gated bytes) | 1 | 68,455 | 68,455 |
| `md2_core` (core 0 / core 1) | 2 | 20,160 / 19,899 | 40,059 |
| `md2_line` | 4 | 14,883 | 59,533 |
| `md2_stream` | 2 | 7,839 | 15,678 |
| `md2_mem` (arbiter, P0, host request) | 1 | 6,516 | 6,516 |
| `md2_thread` | 6 | 1,087 | 6,520 |
| `md2_acc` (A, flags, R0..R3) | 1 | 4,329 | 4,329 |
| `md2_host` (SPI) | 1 | 4,358 | 4,358 |
| `md2_lfsr` | 2 | 3,806 | 7,612 |
| `md2_counter` | 3 | 1,740 | 5,220 |
| `md2_shifter` | 2 | 1,531 | 3,063 |
| `md2_pmem` / `md2_dmem` wrappers (byte-mask glue) | 3 | 18 | 54 |
| top level (synchronisers, host decode and register reads, write groups, source and guard vectors, triggers, output pins, control) | 1 | 50,225 | 50,225 |
| **Total** | | | **271,622** |

## Comparison

- V2_DESIGN 4.8 ledger (after the sizing run): 276k to 290k µm², limit 300k. This RTL is 271.6k synthesized,
  about 28k under the limit on the same basis (v1.0 synthesized 287.8k and closed).
- The latch bank is 32.8 µm² per bit (68,455 / 2,084), against 32.4 measured for the 2,048-bit sizing bank.
- The cores are 20.2k / 19.9k against 18.9k / 19.0k in the sizing core (which had a stubbed source bundle).
- Lines are the largest block after configuration: 14.9k each. Three 16-bit tap comparators against the phase,
  the next phase, a window comparator, the hold comparator and two 32-entry tables are in each.
