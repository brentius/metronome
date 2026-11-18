# Metronome v3 RTL bundle: synthesized area against the v2 baseline

**Evidence class: synthesized estimate, typical library.** Yosys 0.70+190 (git 485b63564), IHP sg13cmos5l
`build/pdk/sg13cmos5l_stdcell_typ_1p20V_25C.lib`, flow of `code/tests/rtl_v2/area.py` (`synth`, `dfflibmap`, `abc`,
`opt_clean`, `stat -liberty`, hierarchical; defines `SYNTHESIS USE_IHP_SRAM USE_IHP_CELLS`; library latch and clock
gate counted; SRAM macros black boxes, not counted). Script: `area_v3.py` (same flow, source directory as a
parameter). Pre-placement: no clock tree, no buffering or resizing, no routing; it says nothing about fit or 60 MHz
timing. Raw logs: `data/raw/v3_rtl_20261116/area_*.log`. Date 2026-11-16, branch `metronome-v3.0`, uncommitted tree.

## Baseline reproduction

| Tree | Total µm² | Note |
|---|---|---|
| Documented v2 (AREA.md, D32 tree, 2026-11-12) | 274,908.3 | the brief's reference figure |
| `HEAD` e8f669f `src/` (committed v2) | 273,835.5 | `area_v2_head_e8f669f.log`; 1.1k below the documented figure, cause not traced (the documented run's tree is not exactly the committed one) |
| `refs/v3-baseline/20261116` `src/` (v2 + external timing restructures of `project.v`, `md2_acc.v`, `md2_lfsr.v`) | **280,026.4** | `area_v2_baseline.log`; the restructured accumulator alone is 10.4k against 4.3k |
| v3 (this work) | **292,047.6** | `area_v3.log` |

The v3 delta is measured against the v3 baseline snapshot, the same tree v3 started from: **+12,021 µm²**
(budget 15k). Against the documented 274,908 the v3 tree is +17.1k, but 5.1k of that is the earlier timing
restructure, not v3.

## Per block (µm², synthesized)

| Block | v2 baseline | v3 | Δ | What v3 added |
|---|---|---|---|---|
| `md2_cfg_bank` | 68,455.5 | 69,170.4 | +714.9 | 28 latch bits for `LIVE` (2 per output pin) |
| `md2_core` 0 / 1 | 20,450.7 / 21,209.4 | 21,094.1 / 22,043.9 | +643.4 / +834.4 | IR load enable (64 muxes), freeze gate on XV/RV and state enables, readback ports |
| `md2_line` x 4 | 15,527.0 each | 14,745.0 each | -782.0 each (-3,128) | `& ~frz` on two edges and the advance, `HELD` enable. The decrease is ABC structural variation, not a saving from v3 |
| `md2_stream` S1 (CAP=0) / S0 (CAP=1) | 6,397.4 each | 7,953.5 / 8,304.1 | +1,556.1 / +1,906.7 | freeze gating of every update, `WB` landing capture rule; S0 also the capture push, `WB` record load, word request |
| `md2_mem` | 6,461.3 | 7,525.4 | +1,064.1 | whole-word write mux (32-bit data, byte enables), freeze on grants, pointer hold |
| top level | 51,525.0 | 59,954.5 | +8,429.5 | MISR (32 flops + XOR), `DC` (19 flops + incrementer), `EMASK` (13), freeze/step/enables, doorbell hold, `FP`/`INVP` hold, output-pin `LIVE` muxes and freeze enables, `DBG` readback mux and decode |
| unchanged blocks | 37,021.8 | 37,021.8 | 0 | acc, host, LFSRs, counters, shifters, threads, SRAM wrappers |
| **Total** | **280,026.4** | **292,047.6** | **+12,021.3** | |

Flops: 1,004 -> 1,096 (+92); latches 2,084 -> 2,112 (+28); clock gates 284 (unchanged).

**Reading the number.** The line block fell 3.1k although it gained gates; that is run-to-run ABC structure, so the
honest range for the logic v3 added is about +12k to +15k µm² (estimated). The bundle fits the 15k rule on this
measurement but leaves little room; physical re-closure (placement, CTS, hold repair) is not run and is expected to
add buffers, as it did for v2 (V2_DESIGN 4.8: +24.3k of repair buffers on 135k for the skeleton).

## Logic added to existing paths (timing, not analysed with STA)

- **Guard -> hit:** `mv_en = (XV & ~FRZ) & guard_ok`. Both XV and FRZ are flops, so the extra AND is on the early
  input only; the late guard input still passes one AND2 (expected no added depth on the late path; not checked by STA).
- **Move data:** unchanged (no new logic on source selection or the write-group pick).
- **Pin edge -> line start/accept -> phase, tap, boundary -> trigger:** one AND (`& ~FRZ`) after the edge select, and
  one AND on each thread's event before `trig`. New logic on an existing path.
- **Arbiter -> SRAM inputs:** grants gain `& ~FRZ`; `m_be` and `m_wd` gain a 2:1 mux (word-write capture record).
  This is on the RAM address/data setup path to the macro.
- **Output pins:** the `LIVE` 2:1 mux sits between the COMMITTED-bit select and the 32:1 table, plus a freeze enable
  on the pin registers; the new live path starts at the synchroniser flop `s2`. Registered at the pin register as v2.
- **New paths:** MISR (pin registers -> XOR -> MISR), `DC` incrementer, `DBG` readback into the host read mux.

Re-running STA at the slow corner (setup, r4b +2.28 ns) and fast corner (hold, r4b +0.10 ns) needs the physical
flow, which this task did not run.
