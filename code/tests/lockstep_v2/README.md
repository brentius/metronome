# v2 lockstep: RTL against the metronome2 model, every pin, every cycle

```sh
source code/tools/env.sh
python -m pytest code/tests/lockstep_v2 -q                  # 9 directed scenarios + 4 random seeds
LOCKSTEP_SEEDS=20 python -m pytest code/tests/lockstep_v2 -q
LOCKSTEP_BEHAV_SRAM=1 ...                                   # md2_pmem/md2_dmem arrays instead of the IHP SRAM models
RTL_V2_SRC=/path/to/copy LOCKSTEP_TAG=_mut ...              # run against a mutated copy of src/ (mutation checks)
```

`lockstep_tb.py` drives `tt_um_brentius_metronome` (Icarus, IHP SRAM behavioural models, behavioural latch cells)
and `metronome2.chip.Chip` with identical `ui_in`, `uio_in` and `rst_n`, and compares `uo_out`, `uio_out` and
`uio_oe` after every rising edge. All configuration, programs and data RAM contents go in over the SPI host link
(writes at SCK = clk/4, reads at clk/16), and every read-back appears on MISO, so the register and RAM locations
actually read by a scenario are compared too. This is not a complete internal-memory comparison. Input pins can depend on the previous cycle's outputs (loopback). The SRAM model arrays are zeroed at
time 0 to match the model's zeroed memories. On a mismatch the first failing cycle dumps line, thread and core state
from both sides.

## Scenarios (`scenarios.py`)

| Name | Covers |
|---|---|
| `smoke` | ID, data RAM write/read, write-only configuration reads 0, runtime registers, unmapped addresses |
| `eth_loopback` | 10 Mbit/s (6 cycles per bit) TX stream on core 0, RX stream on core 1, O0 looped to P0 |
| `follower` | follower mode, edge-sourced tap 0, varying clock period, clock stop clears SYNC |
| `hold` | the hold (3.2a) on four lines, including HTAP on a disabled tap and on an edge-sourced tap 0; HELD read |
| `taps` | fired bits, SEG, TAPMISS from host PHASE jumps, windowed re-alignment, edge start, snapshot at the boundary |
| `units` | jumps, watchers, round robin, T.STOP, conflict, late, overrun, flag-rise and ALWAYS triggers, doorbells, mailbox, every unit, a stale pointer landing (v1 9a.3), ERRSUM, IRQ |
| `reset_mid` | a reset mid-run clears registers and configuration, memories keep contents |
| `spi_target` | D28: SPI mode-0 target whose start commit drives MISO before the first SCK edge; mode-1 line whose first boundary precedes any capture edge (no TAPMISS, `FIRST`); MSB-first TX and RX streams |
| `shifter_parallel` | Each core drives both shifters with simultaneous CFG and LD/SH in both move orders; shifter data and DONE-dependent bytes are exposed through the host mailbox |
| `random_<seed>` | random line, pin, stream, LFSR configuration; random programs on both cores (bursts ending in a pause, random guards, jumps, out-of-table fields); random threads, input activity and host traffic (doorbells, runtime writes, live table rewrites, reads) |

## v3 scenarios (`scenarios_v3.py`, SPEC v2 section 12, branch `metronome-v3.0`)

| Name | Covers |
|---|---|
| `v3_live_misr` | live-pin tables (`LIVE` b2 and b1) on a wired-AND loopback: open-drain read-back, collision flag, pass-through, both live bits; digest enabled, read, paused, cleared |
| `v3_freeze` | freeze over SPI with lines, threads, a transmit stream and a pointer loop running; frozen host RAM reads/writes, doorbell held, PHASE and OUT writes while frozen, single steps with `CST`/`FPC` reads, resume; digest over the whole run |
| `v3_ecap` | edge capture on S0 against S1 receive and P0 reads: a 16-cycle burst of one edge per cycle, simultaneous edges, masked pins, edges inside a freeze, END; records and `POS` read back over SPI |
| `random3_<seed>` | `random_<seed>` set-up plus random `LIVE` bits, digest, random edge-capture mask on S0, random freezes with steps and frozen reads (`LOCKSTEP_V3_SEEDS`, default 2) |

The digest, debug block and capture records are compared through MISO like every other read. `mutate_v3.py` runs
six RTL mutants (live pin swapped, digest polynomial, pins not held while frozen, step ignored, IR not held,
capture `DC` restarting at 0); each must fail its scenario.

## Independent UART receiver

`v4_uart_reply` loads the resident UART learner via SPI, feeds 8N1 training
at 24 chip clocks per bit, and checks that O8 sends the held-out byte `0x42`.
`LOCKSTEP_TRACE_UO` writes a byte per compared cycle from the actual RTL
output bus. Use a separately authored UART receiver to decode O8 and verify
that zeroing the reply's stop bit produces a framing error.

```sh
git clone https://github.com/alexforencich/verilog-uart.git build/v4_proto/verilog-uart
git -C build/v4_proto/verilog-uart checkout --detach 1b867e53af738e4a8bc7c839ca2f1c07f40382dc
python code/tests/lockstep_v2/check_uart_peer.py build/v4_proto/verilog-uart/rtl/uart_tx.v --emit-training build/v4_proto/uart_training.bin
LOCKSTEP_UART_TRAINING="$PWD/build/v4_proto/uart_training.bin" \
  LOCKSTEP_TRACE_UO="$PWD/build/v4_proto/uart_reply_pins.bin" \
  python -m pytest code/tests/lockstep_v2 -q -k v4_uart_reply
python code/tests/lockstep_v2/check_uart_peer.py build/v4_proto/uart_reply_pins.bin build/v4_proto/verilog-uart/rtl/uart_rx.v
```

Have Icarus Verilog and `vvp` on PATH. The checker expects the exact
`v4_uart_reply` stimulus and pin trace.

## Constraints on random stimulus (and why)

- Program memory is written only before `RUN_global` is set: a host program write in the same cycle as a fetch is
  undefined (SPEC 9a.8). The model returns the new word; the SRAM keeps its old output.
- Streams are rewound after their configuration is written (a MODE/MSB/START change without a rewind is
  unspecified, 9a.13).

The old restriction on simultaneous shifter CFG and LD/SH, and on cross-core shifter access, was removed after
fixing the model's move-order bug (D31). Both operations now use cycle-t LEN/MSB as section 6 requires. The line
block also has an independently asserted host-stop/start-edge collision regression (D32); model/RTL lockstep alone
had missed that shared error. Red/green evidence is in `data/raw/v2_resume_sol_20261112/`.

## Mutation checks (2026-11-12)

Each mutant of `src/` was run against the scenarios named; all were detected: start commit removed (`spi_target`),
`FIRST` ignored (`spi_target`), stream bit order fixed LSB-first (`spi_target`), hold disabled (`hold`), round-robin
cursor off by one (`units`, random), write-group winner reversed (`units`, random), stale-landing RDY rule removed
(`units`). The first three survived the scenarios before `spi_target` was added.
