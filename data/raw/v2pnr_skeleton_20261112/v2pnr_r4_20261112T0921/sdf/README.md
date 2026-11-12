# Back-annotated gate-level runs of v2pnr_r4_20261112T0921 (2026-11-12)

The configuration-latch write-path check V2_DESIGN 4.7 asks for: the routed netlist (`final/nl`) simulated with the
signoff SDF of each corner (`final/sdf/nom_*`), Icarus Verilog 13.0, cocotb 2.1.0, IHP sg13cmos5l cell models with
specify paths, clock 16.666 ns. Runner `code/flow/runpod/sdf_v2.sh`; test files in
`sim/numerics/v2_sizing/tt_v2_pnr/test/` (`test_cfg.py`, `gen_cfg_probe.py`, `cfg_latch_chk.v`, `sdf_for_icarus.py`,
`run_local.py --sdf`). Each directory: `sim.log`, `results.xml`, `cfg_probe.json`, `sdf_summary.txt`. `runs_20261112T1216.log` is the volume's run log after these runs.

| Run | Corner | Test | Result |
|---|---|---|---|
| `cfg_slow` | slow 1.08 V 125 C | test_cfg | pass: 65 state checks, strobes = writes on 49/49 bytes, monitors 0, Q 0.270-0.440 ns after gate |
| `cfg_typ` | typ 1.20 V 25 C | test_cfg | pass: same checks, Q 0.170-0.280 ns |
| `cfg_fast` | fast 1.32 V -40 C | test_cfg | pass: same checks, Q 0.120-0.190 ns |
| `proj_slow` | slow | test (functional smoke) | pass |
| `proj_fast` | fast | test (functional smoke) | pass |
| `neg_cfg_slow_4ns` | slow, 4 ns clock | test_cfg | pass (not a failing control: the D24 write path keeps 1.5 cycles from data to gate close) |
| `cfg_fast_headererr`, `proj_fast_headererr` | fast | | superseded: SDF header `-40.000::-40.000` not rewritten (one SDF error); both passed, rerun clean |

All kept runs: 0 SDF errors; the 1,105 TIMINGCHECK blocks are reported unsupported by Icarus, which is why
`cfg_latch_chk` monitors setup (0.30 ns), hold (0.05 ns) and gate width (0.15 ns) at every latch pin itself. Its
self-test (`chk_selftest.v`) counts each injected violation once and a clean write none.

**Not simulated** (by `sdf_for_icarus.py`, reported in `sdf_summary.txt`): 27,560 cell-to-cell INTERCONNECT delays
(largest 0.167 ns; Icarus 13 crashes on them), and the three SRAM macros' delays (clock to output about 6.5 ns slow;
Icarus cannot parse bit-indexed ports), so SRAM reads are optimistic in `proj_*`. The latch write path has no SRAM in it.
Without the rewrite, Icarus silently skipped the latch, clock-gate and gated-clock-buffer cells (escaped names).
