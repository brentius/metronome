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
