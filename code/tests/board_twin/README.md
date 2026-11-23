# Board twin: the real RP2350 loader core against the full-chip RTL

`code/host2/board/` is the host software that will run on the demo board's RP2350. This directory runs **that same
Python code**, imported unchanged, against `tt_um_brentius_metronome` in Icarus, with an adapter that models the
RP2350's GPIO timing: a configurable SCK period, SCK edges at any phase (including a fraction of a cycle) of the
chip's own clock, per-edge jitter, and a configurable MISO sample instant.

```sh
source code/tools/env.sh
python -m pytest code/tests/board_twin -q                 # everything, 116 s idle (review rerun) to 442 s under load
python -m pytest code/tests/board_twin -q -k core         # 45 pure-CPython loader tests, under a second, no simulator
TWIN_GRID=16:0.05,16:0.95,8:0.5 python -m pytest code/tests/board_twin -q -k sweep -s
TWIN_REBUILD=1 python -m pytest code/tests/board_twin -q  # force an Icarus rebuild
python code/tests/board_twin/sweep_table.py code/tests/board_twin/sim_build_twin/sweep_results.json
```

| File | Role |
|---|---|
| `conftest.py` | puts `board/` (host core), `sim/reference` (cycle model) and `code/tests/lockstep_v2` on `sys.path` |
| `twin_bus.py` | `TwinBus` (RP2350 GPIO timing model, executes the loader's operations, records the achieved SCK phase) and `ModelMonitor` (per-cycle RTL-vs-model comparison) |
| `twin_check.py` | the single verdict: `trial_flags()` and `link_problems()`, computed from raw bytes and never from a stored boolean |
| `board_twin_tb.py` | cocotb tests: `twin_smoke`, `twin_sweep`, `twin_negative`, `twin_uart_tx` |
| `test_board_twin.py` | pytest wrapper: builds the full chip once, runs each cocotb test, checks the sweep report and that `SWEEP_RESULTS.md` still matches it |
| `test_core.py` | pure-CPython tests of the loader core against a spec-level fake SPI target, the phase/timing model, and the pinned-SDK checks |
| `sweep_table.py` | renders a sweep JSON as the Markdown tables in `SWEEP_RESULTS.md` (and the fine-phase grid with `--fine`) |
| `SWEEP_RESULTS.md` | the measured answer to "where does the link stop working", generated from the JSON |
| `FINDINGS.md` | defects found in the host software and the twin while building this, with reproductions |
| `evidence/` | raw log and JSON of the runs the numbers here come from |

Evidence classes: everything this directory runs is **RTL-simulated** (Icarus, IHP SRAM behavioural models) or
**host software tested against a spec-level fake**. Nothing here is hardware; **nothing has been measured on a board**
and no RP2350 has executed the loader.

The RTL source list and the IHP SRAM behavioural models come from `code/tests/lockstep_v2/rtl_sources.py` (imported,
not copied). The loader core is `code/host2/board/metronome_core.py`; nothing in this directory reimplements it.

## What each test proves

- `twin_smoke` — at the spec limit (clk/16, phase 0.95): `ID` = 0xA2, an 8-byte data-RAM round trip, a write-only
  configuration address reading 0, `PHASE`/`CTL`/`PC`/`STAT` round trips, a started line and an enabled thread, and a
  full `probe()` of `CTRL`/`LRT`/`TRT`, with **every RTL output pin compared to the cycle model every cycle**.
- `twin_sweep` — 38 SCK timing points (period 2..32 chip cycles x phase 0.05..0.95 x jitter, including ±0.45-cycle
  jitter, a non-integer period and a 0.05 sample lead). Each point re-aligns the twin's timebase, resets the chip,
  reads `ID`, round-trips 4 data-RAM bytes and a runtime register, then reads both back at clk/16 so a write failure
  is not mistaken for a read failure. The assertion is the spec contract: **no SPEC-conforming point (period >= 16)
  may fail**; the rest is a report. Results and analysis in `SWEEP_RESULTS.md`.
- `twin_negative` — the checker's own negative control. A passing trial is copied and one raw field is corrupted
  (`readback` byte, register readback, write-path evidence, ID, cycle-model mismatch count); each copy must be
  rejected by `twin_check.link_problems()`, and the same bytes as the expectation must pass again (so the verdict is
  data-driven, not a hard-coded rejection). Then a real timing violation: SCK at clk/2, eight times over the SPEC
  limit, must fail the link (the ID read does not return 0xA2) while the RTL still matches the cycle model — a
  protocol limit, not an RTL/model divergence.
- `twin_uart_tx` — image load + read-back, then the example program's output: assembles
  `code/host2/examples/uart_tx.mas` with the repository toolchain, loads the resulting image over SPI with the real
  loader, checks `ID`, `RUN`, line/thread state, `ERRSUM`, `HOSTSTAT` and that program memory reads 0 (SPEC v2 9),
  writes two bytes to `HOSTIN` (waiting for `HOSTSTAT.INV` to clear first) and decodes O8 (`uo_out[2]`) with an
  independent 8N1 decoder at 3125/6 cycles per bit: `0xA5`, `0x3C`. The whole run is compared against the cycle model
  every cycle, and the loader's own SPI traffic goes on during the UART frames.
- `test_core.py` — the SPI frame layout (3+n bytes; n data bytes for n dummy bytes; `n+1` read requests, i.e. the
  prefetch), CS_N idle state, auto-increment, image coalescing/order (byte for byte against
  `metronome2_tools.image`), the clk/16 guard, `probe()` decoding, the phase/timing promises of `Timing`, the
  MicroPython-readiness scan of the core, and that the pinned SDK commit/licence are in both the code and
  `code/host2/board/README.md`.

## What to distrust, and the negative controls for it

- A passing sweep would be meaningless if the verdict were vacuous: `twin_negative` corrupts each compared field and
  requires a failure, and requires a pass when the expectation is made equal to the data.
- A "phase sweep" would be meaningless if the phase were not the one requested: `test_core.py` checks the promise in
  pure Python (`test_first_sck_edge_lands_at_the_requested_phase`, `test_transaction_spans_whole_chip_cycles`), and
  the sweep JSON records the phase that actually occurred (`rise_phase_min`/`rise_phase_max`). 33 of the 38 points
  land exactly on the requested phase and two more agree to 2e-4; the three remaining are the two jitter points and
  the non-integer period, where the edges must walk.
- A "RTL passes" claim would be meaningless if the RTL disagreed with the reference model: `ModelMonitor` compares
  every output pin every cycle, and reports zero mismatching cycles over 175 350 cycles in the sweep alone.

## Grid covered

SCK period: **2, 3, 3.5, 4, 5, 6, 8, 10, 12, 15, 15.5, 16, 20, 24, 32** chip cycles (clk/32 .. clk/2). Phase of the
first SCK edge, inside a chip clock period: **0.05, 0.37, 0.50, 0.62, 0.95** across those periods (38 points). Per-edge
jitter: **0**, **±0.30** and **±0.45** chip cycles. MISO sample lead: **0.25** (default) and **0.05** of the SCK half
period. Plus a separate 20-point fine grid of ten phases at clk/5 and clk/6 (`evidence/fine_phase_results.json`).

## How the twin models the RP2350, and what it does not

Modelled: the instant of every pin change (fractional chip-clock cycles, `cocotb.triggers.Timer` in ps with a 16 ns
chip clock, the same period the lockstep bench uses); SCK period, phase and per-edge jitter; the MISO sample instant;
`rst_n`; `ui_in[3..7]`/`uio_in` for extra stimulus.

Pin changes are kept at least 250 ps away from a clock edge (a simulator-race guard; 28 nudges over the 38 points, all
smaller than 1/60 of a cycle) because a real asynchronous edge has no defined sampling instant in a zero-delay
simulation. The bus re-aligns its timebase to a clock edge at the start of every sweep point so those nudges do not
accumulate from one point to the next. That is the only stimulus adjustment the twin makes.

**Not modelled:** TT mux and pad delays, RP2350 GPIO slew and drive strength, PIO FIFO/scheduling jitter, board trace
skew, metastability in the two-flop synchroniser (the RTL samples the level exactly at the clock edge), the real
60 MHz source's phase noise, and any supply/thermal effect. The twin is RTL-simulated evidence, not hardware evidence —
`wiki/EVIDENCE.md` assumption A1 lists exactly these gaps.

## Reading the model comparison

`ModelMonitor` feeds `metronome2.chip.Chip` the pin levels the RTL samples at each rising edge and compares `uo_out`,
`uio_out` and `uio_oe` after that edge, i.e. the same contract as `code/tests/lockstep_v2`. The SRAM model arrays are
zeroed at time 0 to match the model's zeroed memories, as in lockstep. Pin levels are read at the edge *after* the
clock tick, which is what the input synchronisers sample, so the model sees the same cycle the RTL does; getting that
one cycle wrong shifts TX by one bit and shows up immediately as single-cycle mismatches (that is how the ordering
was validated).

Across the four simulator tests (175 350 cycles in the sweep, 62 920 in the fine grid, plus the smoke, negative and
UART runs) the number of mismatching cycles is **zero**.

## Measured runtime and result

`python -m pytest code/tests/board_twin -q` on 2026-11-19, Windows 11, Python 3.12.10, cocotb 2.1.0, Icarus
Verilog 14.0, from a deleted `sim_build_twin/` with `TWIN_REBUILD=1` (raw log and tool versions in
`evidence/pytest_full_20261119.log` and `evidence/run_meta.json`):

```
50 passed in 442.04s (0:07:22)
```

Per-test durations from that run (`--durations=0`): `twin_sweep` 265.56 s, `twin_uart_tx` 122.59 s, `twin_smoke`
38.54 s, `twin_negative` 14.78 s, the 45 core tests 0.6 s. The Icarus build takes about 20 s when it has to run.

The wall time depends heavily on what else is running: the same suite took 311 s and 327 s in earlier runs of this
same tree while other agents' Icarus simulations were also active, and `twin_sweep` alone has taken 144 s to 265 s.
Plan for **2 minutes on an idle machine (116 s, review rerun 2026-11-19) and up to ~7.5 minutes under concurrent load (442 s)** and read the log for the measurement.

## Known gaps

- **No hardware.** No RP2350, no demo board, no silicon; the loader has never executed under MicroPython (see
  `code/host2/board/README.md` for what that does and does not imply).
- `uart_tx.mas` is the hand-written v2 example and its idle loop samples `HOST.INV` and `HOST.IN` in the same burst,
  so a `HOSTIN` write landing between the two samples is consumed without a start bit (the `F-HOSTIN` finding in
  `wiki/EVIDENCE.md`). The test writes two bytes at two different phases and both decode, but that is a spot check,
  not a write-phase sweep. See `FINDINGS.md`.
- The sweep uses one sample lead per point (0.25, plus three at 0.05), not a two-dimensional sample-point sweep.
