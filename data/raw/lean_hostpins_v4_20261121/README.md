# Evidence: pin-level host transactions (Metronome v4)

Cut: `code/tests/lean/Metronome/HostPins.lean`, `HostPinsEquivalence.lean.in`,
`hostpins_check.py`. Notes: `code/tests/lean/HOSTPINS_NOTES.md`.

Machine: 10-core i5-1245U laptop, Windows, Lean 4.35.0 (Elan), Yosys 0.70+190,
2026-11-21, branch `metronome-v4.0`.

## Commands and exit codes

| Command (from `code/tests/lean` unless noted) | Exit | Wall |
|---|---|---|
| `lake build Metronome.SpiPins Metronome.HostRead Metronome.HostMap` | 0 | 1 s |
| `lake build Metronome.HostPins` | 0 | 1-12 s |
| `lake env lean -DwarningAsError=true Metronome/HostPins.lean` | 0 | 11-15 s |
| `lake env lean <scratch>/Axioms.lean` (`#print axioms`, output in `axioms.txt`) | 0 | 3 s |
| `python hostpins_check.py --artifacts-dir data/raw/lean_hostpins_v4_20261121/rtl` | 0 | 70 s |
| `python hostpins_check.py --mutations --artifacts-dir .../rtl_mutants` | 0 | 158 s |
| `git diff --quiet HEAD -- src` (from the repository root) | 0 | - |

`HostPins.lean` contains no `sorry` and no `native_decide`; `axioms.txt` has no
`sorryAx`. The witness theorems use neither `native_decide` nor `bv_decide`.

## Layout

| Path | Contents |
|---|---|
| `lean.log` | the `lake env lean -DwarningAsError=true` run (empty output = no diagnostics) |
| `lean_build.log` | `lake build Metronome.HostPins` |
| `axioms.txt` | `#print axioms` for the module's headline theorems |
| `run_status.txt` | one line per command with its real exit code |
| `rtl/` | the composed RTL check: `stdout.log`, `baseline.log` (Yosys, extraction facts, Lean output), `baseline.hostpins.lean` (exactly what Lean checked), `baseline.axioms.txt`, `tools.log`, `lake.log`, `run_status.txt` |
| `rtl_mutants/` | the same for the baseline plus `hostpins_tx_early` (rejected by the generated Lean) and `hostpins_sck_from_s1` (rejected by the structural check) |
