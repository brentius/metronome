# Metronome v2 pipelined core: sizing and logic depth

Date 2026-11-12. Baseline revision e7ce29f (branch metronome-v2.0) with the uncommitted v2 definitions in `code/md2/` (`md2_defs.vh`). Tools: Yosys 0.70+190 (485b63564), Icarus Verilog 14.0 (devel s20260301), Verilator 5.053 devel, cocotb 2.1.0, Python 3.12.10, OSS CAD Suite 2026-10-22. Libraries: `build/pdk/sg13cmos5l_stdcell_typ_1p20V_25C.lib` for area and `sg13cmos5l_stdcell_slow_1p08V_125C.lib` for depth.

## What was built

| File | Contents |
|---|---|
| `rtl/md2_core.v` | Core with IR, fetch-ahead, guard and jcond evaluation, three moves, round-robin dispatch and watchers |
| `rtl/md2_core_thread.v` | Per-thread state: PC 8, READY, RUNNING, EN, OVR (12 flops) |
| `rtl/md2_core_pmem.v` | 256x64 synchronous-read program memory: behavioural model, black-boxed for area |
| `rtl/md2_core_top.v` | Sizing wrapper: 2 cores, 2 memories, 6 threads, a commons stub (guard, source and per-line inputs as ports) and thread configuration as ports (latches in v2) |
| `area_core.py`, `area_core.ys` | Area and depth runs; raw output in `core_area.log`, which ends with the v1 reference table |
| `code/tests/v2_sizing/test_core.py`, `tb_core.py` | cocotb/Icarus bench with a small md2 assembler built on `code/md2/machine.py`, plus Verilator lint |

The design is synthesizable Verilog-2005 and passes `verilator --lint-only -Wall` cleanly.

## Verification (RTL-simulated, cycle-exact against V2_DESIGN 4.6; no reference model exists yet)

`source code/tools/env.sh && python -m pytest code/tests/v2_sizing/test_core.py -q` gives **11 passed**: 10 cocotb tests and the lint. The tests check:

- From a trigger at cycle t, the first instruction executes at t+3.
- Sequential instructions run one per cycle. Not-taken `if`/`ifnot` jumps cost nothing.
- A taken jump leaves exactly one idle cycle. The fetched-ahead word, which holds ACC.LD, T.STOP and R3 moves, writes nothing, and EN stays at 1.
- A jump on L.IN0 uses the executing thread's line only.
- A pause writes the PC, both sequential and jump-target, and the next trigger resumes there.
- Dispatch after a pause leaves one idle cycle.
- Three continuously ready threads are served round-robin as 0,1,2,0,1,2,... with equal shares.
- W0 (global guard F3) and W1 (line-relative L.PINA) redirect dispatch, with W0 taking priority.
- A thread bound to core 1 is ignored by core 0.
- Response bound with n=2, m=3 (bound 8): every peer trigger offset from -7 to +2 was swept, with the round-robin cursor both favouring and not favouring the peer. The measured worst case was **8, equal to the bound**, with peer offset 0 and the round-robin cursor favouring the peer. Without that preference the worst was 7.

As a mutation check, letting the wrong-path word reach X fails two tests.

## Area (synthesized estimate, typical corner, hierarchical, pre-placement)

| Block | µm² each | Flops each | v1 equivalent |
|---|---|---|---|
| md2_core | 18,882 (C=0) / 18,978 (C=1) | 82 | md_core 15,781, 15 flops |
| md2_core_thread | 941 | 12 | inside md_engine in v1, so not a delta |
| top glue (thread hand-off) | 1,784 | 0 | inside md_engine/project in v1 |

**Core delta against v1: +3.1k µm² per core, +6.3k for both cores, +134 flops.** The 82 flops per core are IR 64, fpc 8, xv, rv, xe 3, xl 2 and rr 3. The +134 flops alone are about 6.6k at 49 µm² each. Some logic is saved because no PC incrementer is needed: the sequential next PC is the fetch PC itself. This is **within the V2_DESIGN 4.8 ledger estimate of +10k**.

Comparability caveats:
- The source mux is limited to the 39 v2 sources at their true widths, as v1 did. An earlier run with a full 64x8 bundle gave 25.3k per core, which was an artefact of the stub.
- If the commons and thread hand-off glue is counted against v2, add 1.8k.

## Logic depth (estimate: ABC `stime` at the slow corner, area-oriented mapping with -D 16667)

Flops were cut into .q/.d ports and one endpoint group was kept per run. The figures exclude wires, clock-to-Q and setup, and module inputs (guards, sources) arrive at time 0.

| Path | Comb. delay | Cells | Worst start → end |
|---|---|---|---|
| IR → jump/next address → SRAM address (dispatch inputs tied off) | 2.05 ns | 9 | xl → guard → taken → fetch_addr |
| IR → guard evaluation → discard decision | 1.39 ns | 7 | ir[59] (jcond) → jmp |
| IR → move enables and source data | 1.62 ns | 7 | ir[38] → mv_data |
| Thread state → dispatch, watchers → SRAM address | 4.29 ns | 17 | t_core → fetch_addr |
| Whole md2_core | 4.69 ns | 21 | rr → fpc D (same dispatch path) |

To turn these into full path estimates I added the following. Each figure's source is given, and none of them is an STA result:
- clock-to-Q of `dfrbpq_1` at the slow corner, about 0.35–0.5 ns, from the liberty tables;
- SRAM A_ADDR setup, at worst 0.26 ns, and A_REN setup, 0.27 ns, both read from the v1 slow-corner SDF in `data/raw/metronome_v1.0/reports/nom_slow_1p08V_125C/`;
- a wire allowance.

The results:
- IR → SRAM address is about 3 ns.
- The dispatch → SRAM address path is about 5–6 ns. This is the longest path inside the core, and it was already present in v1, behind the SRAM.
- Each is well under the 16.67 ns period.

For the move bus, IR clock-to-Q (about 0.5 ns) replaces the v1 SRAM clock-to-out (about 5.5 ns). On v1's worst slow-corner path (slack -0.42 ns, `max.rpt`), that suggests roughly 4–5 ns of new slack. This is **estimated**: closure is unproven until place-and-route and STA of the integrated v2. OpenSTA (`sta`) is not in the OSS CAD Suite installation.

## Rules chosen where V2_DESIGN 4.6 was ambiguous

1. **A taken jump's target is presented in the jump's X cycle.** The address comes straight from IR.imm and the guard. The alternative was to register the target first, which would add a second idle cycle.
2. **The wrong-path word is dropped by not setting xv.** IR loads every cycle without an enable; xv qualifies it. The dropped word cannot write moves, T.STOP or the PC.
3. **Pause with a taken jump stores the target**, as in v1. The fetched-ahead word is dropped, and the dispatch decision is made in the pausing X cycle from the current READY and watcher state.
4. **The core is busy in the cycle after dispatch** (R stage, xv=0, rv=1). Nothing new dispatches then.
5. **The executing line (xl) is registered at dispatch**, not muxed from the thread configuration on every cycle. LINE must therefore not change mid-burst, which is already required because configuration is fixed while a burst runs.
6. **Guard and source edge cases:** G_TRUE is forced to 1 and guard codes 62–63 to 0 (SPEC 9a). Source codes from 39 upward read 0.
7. **Thread state follows SPEC v1 section 4:** a trigger while READY or RUNNING sets OVR, and a T.STOP move clears EN without ending the burst.
8. **The bound is tight.** The worst case is n+2+Σ(m+1). It occurs when the peer wins the round-robin in the dispatch cycle t+1.

## Open issues

- Guard and source arrival times from the commons are unknown. The input-symbol LUT and line mux add delay ahead of `cond`/`jcond` and are not counted here.
- No integrated STA has been run, and wire delay is not modelled.
- There is no v2 reference model yet, so the timing tests encode V2_DESIGN 4.6 directly.
- The thread slices' host interface and OVR clearing are placeholders.
