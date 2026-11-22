# Workstream A progress (Lean machine spec)

## 2026-11-21 checkpoint 2 (acceptance complete)

- Builds: `lake build`, `lake build Metronome.Machine` and `lake build machine-sim` succeed with zero warnings
  (warningAsError on) and no `sorry`.
- `python gen_tables.py --check`: OK.
- `python machine_smoke.py`: PASS (SPI program load at SCK = clk/16, CTRL.RUN, thread 0 executes; ACC counts 0, 5, 6, ...).
- `python code/tests/machine_lockstep/run_lockstep.py smoke`: OK, 16,449 cycles, 197 keys/cycle, no mismatches.
- `machine-sim` speed: 200k cycles (idle machine, output to a file) in 16.5 s. Piping the output into a slow
  consumer such as `tail` under Git Bash takes about 90 s; that time is spent in the pipe, not the simulator.
- Clause trace: every row is classified, and strict `check_trace.py` passes with 0 errors. The 32 warnings are
  `theorem` rows with empty `decls`, which are consequences left for workstream E. Helper: `MemWrite`.
  Rows were filled by a one-off script (not kept); later edits are made by hand in `spec_trace.toml`.
- Docstrings: every public declaration outside `Util`/`Tables` starts with its SPEC section.
- AMBIGUITIES.md: 21 entries, each marked `-- AMBIG(n)` in the code.

Next (not workstream A acceptance): theorems for the §5 timing table, §13.1 timing and §3.2a "a hold only
lengthens beats" (workstream E); full lockstep scenario triage (orchestrator).

## 2026-11-21 resume checkpoint 1

- Previous session's files built cleanly; smoke and lockstep smoke passed; trace rows unfilled.
