# Tiny Tapeout template port evidence

Baseline: `a235fd6`, branch `metronome-v2.0`, 2026-11-11. This is the v1 machine inside the official template, not the v2 architecture implementation.

- `inputs.json`: input hashes at the local verification checkpoint.
- `template_rtl.log`: Icarus 14-devel / cocotb 2.1.0 / Python 3.12.10, template pin-only smoke test with IHP SRAM models. 1/1 passed; O8 edges separated by exactly 60 clocks. Clock period 16.666 ns (approximately 60 MHz).
- `run_tt_test.py`: equivalent RTL invocation of `test/Makefile` for this Windows machine, which has no make. Run `python data/raw/template_port_20261111T2055/run_tt_test.py .` with OSS CAD Suite on PATH.
- `regression.log`: initial failure retained (old `src/gen` include path and intentional template/blackbox filenames rejected by lint). Lockstep skipped because the initial PowerShell environment script could not execute.
- `rtl_after.log`: after the path and scoped filename-lint fixes, all 10 RTL/lint tests pass.
- `legacy_pack_before.log`, `legacy_pack_after.log`: retained packaging script failed at the old header path, then built successfully after migration repair.

- `regression_env.log`: 565 passed, 9 setup errors, retained because this process imported the old RTL header setting before the repair.
- `regression_final.log`, `regression_final.xml`, `local_summary.json`: fresh full regression on source commit `c83a7f4f0b3443ab065fc4619414ffa5bbd36f21`: **574 passed, no failures/errors/skips**, 509.52 s. Includes directed RTL, per-pin RTL/reference lockstep and formal checks.
- `probe_faults/`: intentional probe-fault results from that passing regression; each fault must cause a cocotb failure for its pytest regression to pass. Generated XML files accidentally included in the source-port commit are restored to their prior content separately; the new results are preserved here.
- `sram_lint.log`: `verilator_bin --lint-only -Wall -DUSE_IHP_SRAM -Isrc --top-module tt_um_brentius_metronome src/*.v` (source list expanded by PowerShell), exit 0.
- `sram_elaboration_after.log`: Yosys `read_verilog -DSYNTHESIS -DUSE_IHP_SRAM -Isrc <all src/*.v>; hierarchy -check -top tt_um_brentius_metronome; proc; check; stat`, exit 0. Initial unsupported wildcard invocation is retained in `sram_elaboration.log`.
- `tool_versions.txt`: local tool versions.
- `github_gds_snapshot_2111.log`: incomplete live GDS job snapshot; not a completed flow result.
- `run_saved_v1_gl_smoke.py`, `saved_v1_gl_inputs.json`, `saved_v1_gl_smoke.log/xml`: supplemental template-testbench check on the saved v1 post-route netlist (only its top name changed in an ignored build copy), with IHP-Open-PDK `89d42ee6` standard-cell models and the existing SRAM models. **1/1 passes**, with O8 edges every 60 clocks, in zero-delay gate simulation. This does not verify the new GitHub physical result or SDF timing. The manifest records input hashes and model provenance.

Official Actions on `c83a7f4`: [RTL test](https://github.com/brentius/metronome/actions/runs/43099316783) and [docs](https://github.com/brentius/metronome/actions/runs/43099316690) passed. [GDS / precheck / gate-level](https://github.com/brentius/metronome/actions/runs/43099316692) is still running at this checkpoint.

These local simulations do not establish physical signoff or 60 MHz slow-corner timing closure. The new physical configuration matches the saved v1.0 r6 configuration for all project-controlled keys; the official template supplies design name, sources, die, pins, routing layers and runtime settings. No RunPod resource was started for this port.

## Reproducing local verification

Use source commit `c83a7f4f0b3443ab065fc4619414ffa5bbd36f21`, the versions in `tool_versions.txt`, and a new output directory for each run. The commands below are PowerShell equivalents of the repository's Bash setup; they do not require executing `env.ps1`.

```powershell
$env:PATH = 'C:/Users/b_yee23/tools/oss-cad-suite/bin;C:/Users/b_yee23/tools/oss-cad-suite/lib;' + $env:PATH
$env:VERILATOR_ROOT = 'C:/Users/b_yee23/tools/oss-cad-suite/share/verilator'
$checkDir = 'data/raw/template_recheck_' + (Get-Date -Format 'yyyyMMddTHHmmss')
New-Item -ItemType Directory -Path $checkDir | Out-Null
python code/md/gen.py --check
python -m pytest code/tests code/host sim/reference -q -p no:cacheprovider --junitxml="$checkDir/regression.xml" *> "$checkDir/regression.log"
python data/raw/template_port_20261111T2055/run_tt_test.py . *> "$checkDir/template_rtl.log"
```

Read the process exit codes and XML results; the expected full-suite result at this revision is 574 passed with no skips. The tests also refresh transient simulator files under `code/tests/`; those are not the preserved evidence in this directory.

For the supplemental saved-v1 gate smoke, obtain `sg13cmos5l_stdcell.v` and `sg13cmos5l_udp.v` from `ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog/` in IHP-Open-PDK commit `89d42ee6d2fd9b50b86a1aada6fee6673c3e6008`, into `code/.build/template_gl_models/`. Compare their hashes to `saved_v1_gl_inputs.json`. Copy `run_saved_v1_gl_smoke.py` into the new `$checkDir` before running it: its XML and input manifest are written beside the script. This preserves the original run's inputs and results. The netlist is the saved v1 `data/raw/metronome_v1.0/gds/tt_um_metronome.nl.v`, not the pending GitHub build.

On Linux, the official template entry point is `cd test && make`, followed by `python -m cocotb_tools.check_results results.xml`. The GDS workflow runs that test again on its generated gate-level netlist through the official GL action. Do not substitute the saved-v1 supplemental result for that required gate.
