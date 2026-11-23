# Board-twin evidence

Raw output of the runs that the numbers in `../README.md`, `../SWEEP_RESULTS.md` and `../../host2/board/README.md`
come from. Nothing here is edited by hand except this file: the log is pytest's own output (redirected straight from
the process, not re-encoded) and the JSON is what `board_twin_tb.py` wrote.

| File | What it is |
|---|---|
| `pytest_full_20261119.log` | full `python -m pytest code/tests/board_twin -q` run, from a deleted `sim_build_twin/` with `TWIN_REBUILD=1` |
| `run_meta.json` | date, command line, tool versions, repository revision, and the per-test durations pulled from that log |
| `sweep_results.json` | the 38-point SCK period/phase/jitter grid (`TWIN_RESULTS` of the full run) |
| `sweep_table_20261119.md` | `sweep_table.py` rendering of `sweep_results.json`, copied into `../SWEEP_RESULTS.md` |
| `fine_phase_results.json` | the 20-point fine-phase grid at clk/5 and clk/6 |
| `fine_phase_table_20261119.md` | `sweep_table.py --fine` rendering of it |

Environment used for all of it: Windows 11, Python 3.12.10, cocotb 2.1.0, pytest 9.2.0, Icarus Verilog 14.0 (devel)
`s20260301-638-ge072b3334-dirty` from OSS CAD Suite `20261022`, IHP SRAM behavioural models from `test/sram_model/`
(listed in `code/tests/lockstep_v2/rtl_sources.py`), chip clock 16 ns in the twin.

## Regenerating

```sh
source code/tools/env.sh                   # or put the OSS CAD Suite bin/ and lib/ on PATH
rm -rf code/tests/board_twin/sim_build_twin
TWIN_REBUILD=1 python -m pytest code/tests/board_twin -q          # the full run

# the fine-phase grid (writes next to this file; use an absolute path: cocotb runs with cwd = the test directory)
TWIN_GRID="5:0.02,5:0.12,5:0.22,5:0.32,5:0.42,5:0.52,5:0.62,5:0.72,5:0.82,5:0.92,\
6:0.02,6:0.12,6:0.22,6:0.32,6:0.42,6:0.52,6:0.62,6:0.72,6:0.82,6:0.92" \
TWIN_RESULTS="$PWD/code/tests/board_twin/evidence/fine_phase_results.json" \
python -m pytest code/tests/board_twin -q -k sweep -s

python code/tests/board_twin/sweep_table.py code/tests/board_twin/evidence/sweep_results.json
python code/tests/board_twin/sweep_table.py code/tests/board_twin/evidence/fine_phase_results.json --fine
```

`test_sweep_table_in_sw_results` fails when `../SWEEP_RESULTS.md` no longer contains the table rendered from the
sweep JSON, so the documented numbers cannot drift away from the run that produced them.

## Why the JSON has both `phase` and `rise_phase_min`/`rise_phase_max`

`phase` is what the loader asked for; `rise_phase_*` is the phase of every SCK rising edge the twin actually saw,
measured from the chip clock edge. They agree to within the 250 ps simulator-race guard, which shifts the timeline
when a pin change would land within 250 ps of a clock edge (`nudges` in the JSON, and per point in `nudges`).
