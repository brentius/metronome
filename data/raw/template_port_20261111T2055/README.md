# Tiny Tapeout template port evidence

Baseline: `a235fd6`, branch `metronome-v2.0`, 2026-11-11. This is the v1 machine inside the official template, not the v2 architecture implementation.

- `inputs.json`: input hashes at the local verification checkpoint.
- `template_rtl.log`: Icarus 14-devel / cocotb 2.1.0 / Python 3.12.10, template pin-only smoke test with IHP SRAM models. 1/1 passed; O8 edges separated by exactly 60 clocks. Clock period 16.666 ns (approximately 60 MHz).
- `run_tt_test.py`: equivalent RTL invocation of `test/Makefile` for this Windows machine, which has no make. Run `python data/raw/template_port_20261111T2055/run_tt_test.py .` with OSS CAD Suite on PATH.
- `regression.log`: initial failure retained (old `src/gen` include path and intentional template/blackbox filenames rejected by lint). Lockstep skipped because the initial PowerShell environment script could not execute.
- `rtl_after.log`: after the path and scoped filename-lint fixes, all 10 RTL/lint tests pass.
- `legacy_pack_before.log`, `legacy_pack_after.log`: retained packaging script failed at the old header path, then built successfully after migration repair.

Full regression and official GitHub Actions verification are in progress. These local simulations do not establish physical signoff or 60 MHz slow-corner timing closure. The new physical configuration matches the saved v1.0 r6 configuration for all project-controlled keys; the official template supplies design name, sources, die, pins, routing layers and runtime settings.
