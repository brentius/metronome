# Metronome RP2350 host loader

Real demo-board host software for `tt_um_brentius_metronome`: select the project, clock it at 60 MHz, reset it, load a
`metronome-image` JSON over the chip's SPI host link, start it and read back status.

| File | Role |
|---|---|
| `metronome_core.py` | **Pure Python, no machine imports.** SPI mode-0 master (SPEC v2 9), image loader, status read-back. Runs under CPython (the board twin and the unit tests drive it) and is written to run under MicroPython. |
| `ttboard_adapter.py` | Thin hardware layer on the Tiny Tapeout `ttboard` SDK: project select, clock, reset, `ui_in`/`uo_out` access, and the interpreter that executes the core's operations. Also carries the pinned SDK commit, licence and API list. |
| `board_cli.py` | Command line for the board (`selftest`, `load`, `status`, `read`, `write`, `hostin`, `bench`) and an offline `plan` command that validates an image under CPython. |

**Evidence classes, so nothing below over-claims.**

| Claim | Class |
|---|---|
| SPI frame layout, read latency, image ordering, `probe()` decoding | verified against the SPEC v2 9 *text* with a spec-level fake target (`code/tests/board_twin/test_core.py`) |
| The same core driving the real RTL: ID, data-RAM round trip, runtime registers, a loaded example program's UART output | **RTL-simulated** against the full chip in `code/tests/board_twin/` (Icarus, IHP SRAM models) |
| The SDK API names used below | read from the pinned SDK source; **not** executed |
| Anything on an RP2350 or a demo board | **not measured on hardware** — no board was available for this work |

The RTL twin that runs *this exact file* against the full chip is `code/tests/board_twin/` (see its `README.md`,
`SWEEP_RESULTS.md` and `FINDINGS.md`).

## Pinned upstream

Tiny Tapeout MicroPython SDK: **`TinyTapeout/tt-micropython-firmware` @ `15ba5ced7aae7746ea2f9004cb412109c9fe9c83`**
(2026-11-12, `main`; `pyproject.toml` version 2.0.0). The same hash is `ttboard_adapter.SDK_COMMIT`, and
`test_pinned_sdk_commit_is_in_the_code_and_the_readme` fails if this paragraph and the code ever disagree.

* **Licence: LGPL-2.1** (`LICENSE` at that commit; classifier `LGPLv2+`). This loader imports the SDK at run time on
  the board and bundles none of its source, so our files carry no LGPL obligation; keep the notice if you ever copy
  SDK code into the image.
* **How it was checked:** the tree was fetched read-only into `build/board_sdk/` (`git init` + `git fetch --depth 1
  origin <hash>` + `git checkout FETCH_HEAD`, a gitignored build directory) and read with an editor and `grep`. No
  script from the SDK was run, no board was touched. `test_pinned_sdk_api_names_exist_in_the_pinned_source` re-greps
  that checkout for every name in `SDK_API` (the test skips when the checkout is absent).
* API used, all present at that revision:

| Call | Use | Where in the pinned tree |
|---|---|---|
| `ttboard.boot.demoboard_detect.DemoboardDetect.probe()` | identify the board before `DemoBoard.get()` | `src/ttboard/boot/demoboard_detect.py` |
| `ttboard.demoboard.DemoBoard.get()` | the board singleton | `src/ttboard/demoboard.py` |
| `tt.mode = RPMode.ASIC_RP_CONTROL` | RP2 drives `ui_in`/`uio_in`, reads `uo_out`/`uio_out` | `src/ttboard/mode.py` |
| `tt.shuttle.find(name)` / `tt.shuttle.<name>` + `design.enable()` | select `tt_um_brentius_metronome` | `src/ttboard/project_mux.py`, `project_design.py` |
| `tt.clock_project_PWM(60e6)`, `tt.clock_project_stop()`, `tt.is_auto_clocking`, `tt.auto_clocking_freq` | project clock | `src/ttboard/demoboard.py` |
| `tt.reset_project(True/False)`, `tt.rst_n` | project reset (`rst_n`, active low) | `src/ttboard/demoboard.py` |
| `tt.ui_in.value`, `tt.uo_out.value` | host-link pins (`ui_in[0..2]`, `uo_out[0..1]`) | `src/ttboard/pins/pins.py` (byte write/read through `platform`) |
| `tt.shuttle.enabled`, `tt.mode_str` | the `describe()` line | `src/ttboard/project_mux.py`, `demoboard.py` |

The project must be in the board's shuttle JSON, or have a `[tt_um_brentius_metronome]` section in `config.ini`; the
`find()` fallback covers aliases (it is a substring match, so an alias containing the name also resolves).

## Install and run

```sh
# from the repository root; board/ goes to the RP2350 filesystem as a package
pip install --user mpremote
mpremote fs cp -r code/host2/board :
mpremote exec "import board.board_cli as cli; cli.main(['selftest'])"
```

or, from the board REPL:

```python
import board.board_cli as cli
cli.main(["load", "uart_tx.json"])     # image produced by metronome2_tools.image
cli.main(["status"])
```

`load` resets the chip, applies the image's ordered writes (coalesced into frames of at most 32 bytes), then reads
back `ID`, `CTRL`, the line and thread runtime blocks and prints a summary. `selftest` only resets and reads `ID`,
which must be `0xA2`. Neither command has been run on a board (see the evidence table).

Offline, on a PC (no board, no ttboard needed):

```sh
cd code/host2
python -m board.board_cli plan ../../build/uart_tx.json     # image -> frames, bus operations, load time
```

## Clock: 60 MHz

`Board.connect()` calls `tt.clock_project_PWM(60e6)` after `design.enable()`. From the pinned SDK source
(calculated, not measured):

* `clock_project_PWM` refuses `freq > max_rp2040_freq // 2` (`_get_best_rp2040_freq`, default
  `max_rp2040_freq = 133 MHz`, so **66.5 MHz** is the ceiling); above `freq*2 > 133 MHz` it raises the allowed RP2350
  system clock to `freq*2`, up to 250 MHz.
* `_get_best_rp2040_freq` scans the RP2350 clock down from the ceiling for an exact `sysclk / divisor` hit, so **60 MHz
  is exact at a 120 MHz RP2350 clock** (divisor 2, first exact hit scanning down from 133 MHz).
* PWM is used for `freq >= 3 Hz`; below 3 Hz the SDK switches to a PIO clock, which 60 MHz never takes.
* `info.yaml`'s `clock_hz: 60000000` makes `enable()` start the same clock through the project config path.

## SPI timing, and the one rule that matters

The core works in **chip clock cycles**; the adapter converts to microseconds (`1000000/60e6` per cycle). `Timing`
defaults to a 16-cycle SCK period = clk/16 = 3.75 MHz, the SPEC v2 9 limit, and `MetronomeHost(enforce_spec=True)`
(the default) raises rather than issue faster traffic.

`Timing.phase_cycles` places the **first SCK rising edge of every transaction** at a chosen phase inside a chip clock
period, exactly, for any period: the CS_N-low wait absorbs the sub-cycle part and the CS_N-high gap gives it back, so
the phase does not accumulate from transaction to transaction. `test_first_sck_edge_lands_at_the_requested_phase`
checks that in pure Python for integer and fractional periods, and the twin reports the phase that actually
occurred (`rise_phase_min`/`rise_phase_max`).

**MISO must be sampled at or before the SCK rising edge.** The target shifts its transmit register two to three chip
clocks *after* the synchronised rising edge (two-flop synchroniser plus the register, SPEC v2 2 and 9), so the level
in the middle of the SCK high phase already belongs to the next bit. `Timing.sample_lead_fraction` (default 0.25 of
the half period) puts the sample before the edge. A real mode-0 SPI peripheral samples at the edge, which is what the
twin's 0.05-lead points model; the sweep in `code/tests/board_twin/SWEEP_RESULTS.md` shows the read limit this
implies.

**Consequence for the datasheet wording (RTL-simulated, from that sweep):** "SPI mode 0" is only true for a master
that samples MISO at the rising edge. At clk/16 the high phase is eight cycles, so a sample up to about five cycles
after the edge is still safe; a master that samples late in the high phase (some PIO or software loops do) reads the
next bit. That margin is what clk/16 buys.

### Throughput limits of this implementation (calculated, not measured)

The link is bit-banged through `tt.ui_in.value` in interpreted MicroPython: three pin writes plus three waits per bit,
so roughly 5-10 µs per bit (about **100-200 kHz**), from the operation count and a typical MicroPython call cost.
That is far below 3.75 MHz but the protocol is unchanged: the `uart_tx` image is 87 data bytes in 9 frames, 912 SCK
bits, so 0.24 ms at clk/16 (calculated by `plan`) and about 6-9 ms at the bit-bang rate. A PIO backend would reach the
clk/16 limit; it is not implemented, because an untestable PIO program would be worse than an honest bit-bang. `bench`
measures the real toggle rate on the board.

## What this does not cover

- **No hardware run.** No RP2350, no demo board, no silicon. Every claim here is host-software, calculated or
  RTL-simulated.
- MicroPython compatibility is enforced **statically** only (`test_core_is_micropython_friendly`: no `json`/`time`/
  `typing` imports, no f-strings, no annotations, no float `%g`/`%e`). Nothing has been executed under MicroPython.
- No TT mux/pad delay, GPIO slew, board skew, PIO FIFO jitter or metastability model; the twin models pin-change
  instants only.
- `ui_in[3..7]` (P8..P12) and `uio_in[0..7]` are left for the caller (`TtBoardBus.ui_high`, `set_uio_in`); the loader
  only owns `ui_in[0..2]`. `uio_oe_pico` is not touched, so a program that drives O0..O7 leaves those pins as inputs
  on the RP2 side unless the caller sets them.
- The loader does not implement the SPEC v2 12.5 load contract (stop-before-configure); it assumes a freshly reset
  chip, which is what `load` does. `metronome2_tools.loader_contract.ContractLoader` has the checked variant; it needs
  a Python-level link object, which this adapter is not (the core is a generator, not a blocking link).
