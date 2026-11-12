# Sol continuation verification, 2026-11-12

Baseline: branch `metronome-v2.0`, HEAD `f945c29`, plus uncommitted steps 3-4. `final_manifest.json` records the exact source/library hashes, tools, parameters, results and artifact hashes. `source_manifest.json` is the earlier snapshot; its only later source change was the evidence preamble in `wiki/SPEC_V2.md`. The initial interrupted-author work is preserved, not committed.

## Final checks

Use Python 3.12 with cocotb 2.1.0. Add `C:/Users/b_yee23/tools/oss-cad-suite/bin` and `/lib` to PATH and set VERILATOR_ROOT to its `/share/verilator`. The machine's PowerShell execution policy blocks `env.ps1`, so these paths were set directly. No simulator check was accepted as a skip.

| Command | Result | Raw log |
|---|---|---|
| `python -m pytest code/tests/score code/tests/scorec -q` | 185 passed (140 score, 45 compiler) | software_final.log |
| from sim/reference: `python -m pytest tests_v2 -q` | 43 passed | model_green.log |
| `python -m pytest code/host2/tests code/tests/md2 -q` | 78 passed | host_map_final.log |
| `python -m pytest code/tests/rtl_v2 -q` | 9 passed: 5 block wrappers, 3 lint modes, generated tables | rtl_blocks_green.log |
| `LOCKSTEP_TAG=_final python -m pytest code/tests/lockstep_v2 -q` | 13 passed: 9 directed + random seeds 1..4, IHP SRAM models | lockstep_final.log |
| `python test/run_local.py` | 1 passed | template_final.log |
| `python code/tests/rtl_v2/area.py --log data/raw/v2_resume_sol_20261112/area_final.log` | 274,908.2868 um? standard-cell estimate | area_final.log |

`xml/` preserves 19 cocotb result files: 13 pin scenarios, five unit wrappers and template. `compiled_examples/` preserves score inputs, generated assembly, images and fit reports for UART, SPI and Ethernet in both roles; static check errors are zero. Ethernet uses `skip_periodic=True` explicitly. `compiled_examples.json` records binding, options, instruction counts and warnings. `data/processed/v2_resume_sol_20261112.json` is the derived summary.

## Failures retained

- Shifter CFG-before-LD/SH: 4 of 8 new model cases failed before deferring CFG; all pass in model_green.log (D31). The initial reproduction is in the conversation tool record; subsequent pin-level `shifter_parallel` and unrestricted cross-core random stimulus pass.
- host_stop_model_red.log and host_stop_rtl_red.log reproduce the same forbidden commit with RUN=0 in both model and RTL. model_green.log and rtl_blocks_green.log verify D32.
- spi_peripheral_red.log reproduces STARVED after deselection. spi_peripheral_guard_green.log is a **failed intermediate attempt**: an END guard was insufficient because CS-off rewound the stream before a queued TX burst. spi_peripheral_selected.log contains the later test-rate mismatch; the rate-matched codec and live-CS guard resolve these cases.
- spi_abort_red.log reproduces MISO stuck high after CS rises with SCK high. spi_final.log verifies all 11 SPI cases after stop-before-start commits idle (D33).
- rtl_lockstep_initial.log is baseline investigation (21 passing checks), not the final source-set qualification; use the final logs above. area.log/area_summary.log are the pre-D32 synthesis and remain unchanged.

## Limits

These are functional RTL simulation/model/codec results and a pre-placement synthesis estimate. Pin lockstep uses a 16 ns functional clock and unit benches 10 ns, without delays; neither proves silicon speed. Timing reports assume nominal 60 MHz. SRAM arrays are zero-initialized for comparison. External pin bundles are compared each cycle; only memory/register locations actually read via SPI are compared. The full v2 has no new physical-fit, STA, DRC/LVS, GL or SDF signoff. Compiler I2C, tether, multiple groups and periodic link pulses remain unsupported. O2/O4/O5 retain their draft positions.
