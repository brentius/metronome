# Machine-spec lockstep harness

Runs the Lean executable machine spec (`machine-sim`, workstream A of `BOTS/PLANS/LEAN_MACHINE_SPEC_PLAN.md`) in
per-cycle lockstep against the Python cycle model `sim/reference/metronome2` on the pin-level scenarios of
`code/tests/lockstep_v2` (`scenarios.py`, `scenarios_v3.py`, `scenarios_v4.py`). Both sides get identical pins; the
output pins and a 197-key architectural state dump are compared after every cycle.

## Files

| File | Role |
|---|---|
| `dump_model.py` | `dump(chip) -> dict` of the plan's keys from the Python model (read-only); memory sums cached |
| `lean_proc.py` | `LeanProc`: starts the exe, writes inputs ahead, reads one JSON line per cycle with a timeout |
| `run_lockstep.py` | CLI and `run()`: builds a scenario, steps both sides, compares, reports |
| `fake_sim.py` | Stand-in exe (second Python `Chip`) to self-test the harness without Lean; `--flip CYCLE:KEY:BIT` plants a difference |
| `test_machine_lockstep.py` | pytest over the directed v2/v3/v4 scenarios plus random seeds |
| `EXCLUDED.md` | Key coverage (nothing excluded) and what is not dumped |

## Commands

Set up once (PowerShell): `$cad="$env:USERPROFILE/tools/oss-cad-suite"; $env:PATH="$env:USERPROFILE/.elan/bin;$cad/bin;$cad/lib;$env:PATH"`.
Plain Python 3.12 also works; cocotb is not needed.

```
python code/tests/machine_lockstep/run_lockstep.py smoke
python code/tests/machine_lockstep/run_lockstep.py v3_freeze --out data/processed/lockstep_v3_freeze.json
python code/tests/machine_lockstep/run_lockstep.py random_3 --keys 'L0.*,A,F' --ignore 'DMEM.sum' --max-cycles 5000
python -m pytest code/tests/machine_lockstep -q                  # skips with a reason if the exe is missing
MACHINE_LOCKSTEP_SEEDS=10 python -m pytest code/tests/machine_lockstep -q
```

Exe: `lean/.lake/build/bin/machine-sim(.exe)` (build: `lake build machine-sim` in `lean`), or
`MACHINE_SIM=<path>`, or `--exe`. Environment: `MACHINE_LOCKSTEP_SEEDS` (random_1..N, default 4),
`MACHINE_LOCKSTEP_V3_SEEDS` (random3_1..N, default 2), `MACHINE_LOCKSTEP_FAKE=1` (pytest against `fake_sim.py`).
Exit codes of `run_lockstep.py`: 0 match, 1 mismatch, 2 harness/exe error (timeout, crash, bad JSON).

Harness self-test (no Lean):

```
python code/tests/machine_lockstep/run_lockstep.py smoke --fake-model
python code/tests/machine_lockstep/run_lockstep.py smoke --fake-model --fake-flip 500:A:0   # must report A at cycle 500
```

## Protocol

stdin lines: `ui uio rst_n` (decimal) is one clock cycle (`ui` is the combined `ui_in`, `(ui & 7) | (hi & 0xF8)`, as
in `lockstep_tb.py`); `reset` returns to power-on state (no ack is assumed; the harness starts a fresh process per
scenario instead); `quit` exits. stdout: one JSON object per cycle holding the state after that cycle (the values in
cycle t+1) and the pins that cycle drives. Closed-loop `uio` callables receive the Python model's outputs of the
previous cycle, exactly as the RTL bench does. Inputs are streamed 128 cycles ahead of the reads (the Lean side never
feeds back into the stimulus), so the pipe round trip is not paid per cycle.

## Keys (197 per cycle)

`uo_out uio_out uio_oe`; `L{0..3}.PH RUN ARM REN HELD FIRST SC SP FIRED W SN REM STAGED COMMITTED TAPMISS`;
`T{0..5}.PC EN READY RUNNING ARMED LATE OVR`; `C{0,1}.XV IR RV FPC XT XL RR`; `F FP A Z C N R0..R3`;
`SH{0,1}.D CNT LEN MSB`; `CNT{0..2}.V`; `LF{0,1}.S`; `P0.PTR D RDY`;
`S{0,1}.POS BIDX BA CUR CV WB WV RQ LD PEND PV STARVED`; `RUN IRQEN CONFLICT MEMHAZ CWOVR INB INV INVP OUTB OUTV`;
`FREEZE FRZ FRZD MEN MISR CEN EMASK DC`; `CWA CWV CWQA CWQD BWP RPL RLV`; `DMEM.sum PMEM0.sum PMEM1.sum`.
`W` packs `{B1,A2,A1,A0}` in bits 3..0; the sums are `sum(mem[i]*(i+1)) mod 2^32` over 2,048 bytes (program memory:
little-endian bytes of the 64-bit words). A key missing from or extra in the Lean output counts as a mismatch
(unless filtered by `--keys`/`--ignore`, which take comma-separated `fnmatch` globs). See `EXCLUDED.md`.

## Report

Console: first mismatching cycle with every differing key (Python and Lean values) and the last six pin frames, then
up to `--max-keys` (default 20) distinct mismatching keys with the first cycle of each; the run stops at that count.
`--out` JSON: `scenario, cycles, ok, first_mismatch_cycle, mismatching_keys, mismatches[{key,cycle,python,lean}],
keys_compared, seconds, check`. `check` is the scenario's own post-condition run on the Python model.
Note that after the first divergence later keys usually cascade; triage the earliest cycle and the earliest key.

## Triage procedure

For the first mismatching key at cycle t, compare the Python model state at t-1, the pins at t, the relevant SPEC_V2
clause, and the Lean transition. Classify as exactly one of:

1. **Lean transcription error**: the SPEC text says what Python does; fix the Lean.
2. **Model divergence from SPEC_V2**: the Lean follows the SPEC text and Python does not; record it (DECISIONS), do not
   edit the model without a decision.
3. **SPEC ambiguity or omission**: the text allows both; record a SPEC fix candidate.

Never make a mismatch disappear by editing the model, ignoring the key or loosening the comparison. Use `--keys` only
to localise, not to pass.

## Runtime

Python-side cost is about 0.3 ms per cycle for the model plus dump (a 197-key dict); the Lean exe adds its own
step cost and JSON line. Runtimes with the fake exe (two Python models) are given in the handoff; the real figures
depend on the exe.
