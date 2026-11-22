# Lean host write-strobe cut, 2026-11-18

Baseline: `metronome-v4.0` at `b7b40687cc26419bed64a25c467ed91be65f28a9`,
uncommitted working tree over that revision. No production RTL was edited; all
mutations ran on temporary copies of `src/`.

Tools: Lean 4.35.0 / Lake 5.0.0-src+eb6cafb (Elan), Yosys 0.70+190 (OSS CAD
Suite), Python 3.12.10, Icarus 14.0 devel via the same OSS CAD Suite.

RTL snapshot digest printed by the runner (all `.v`/`.vh` names and bytes,
SHA-256 over `name\0sha256(content)`):

```text
434c6ae6e52b85991f0be864394e5c93382f4aa239c9302ae0ef91d19dab2b3b
```

## Commands

From the repository root, with `.elan/bin` and the OSS CAD Suite `bin` and
`lib` directories first on `PATH`:

```text
python code/tests/lean/verify.py --mutations --artifacts-dir <fresh dir>
python -m pytest code/tests/md2/test_v4_model.py code/tests/lockstep_v2 -q \
    -k "test_v4_model or v4_config_write or spi_target"
```

## Results

`proof_final3/` is the canonical run. The baseline passed both generated Lean
proofs. The runner rejected all nine mutation cases with the expected layer:

| Case | Expected rejection | Actual |
|---|---|---|
| `spacing`, `priority`, `held_addr`, `held_data`, `stage_capture` | configuration equivalence (`rfl`) | rejected |
| `feedback` | chip-top wiring adapter | rejected |
| `host_gate` | host write-gate equivalence (`rfl`) | rejected |
| `host_counter` | host counter equivalence (`rfl`) | rejected |
| `host_filter` | exact AND-over-filter adapter | rejected |

Selected regression: **25 passed** (23 v4 cycle-model cases, `v4_config_write`
and `spi_target` full-chip Icarus lockstep). Console log
`proof_final3.console.log`; pytest log and JUnit XML are beside it. The
`proof_final/` and `proof_final2/` directories are retained earlier runs (the
first after adding the tool retry, the second before a proof-only cleanup);
`proof_final3/` is canonical because it is the last run against the final
source tree. The generated configuration proof hash is unchanged across all
three final directories; the host proof source changed only in its case split.

The baseline host theorem dependencies are the standard `[propext,
Classical.choice, Quot.sound]`; they are asserted by `#guard_msgs` in
`baseline.host.lean`. The configuration equivalence theorem keeps its original
zero-axiom dependency.

## Retained failed attempt

`proof/` is the first interrupted run. Its host proof process stalled during a
Windows cold start before producing a result; `proof_retry/` succeeded without
source changes, which led to the single-retry logic now in `verify.py`. The
failed host log was empty. These files are kept unchanged as tool-startup
evidence.

## Boundary

The host cut covers the registered `wr` and `bitc` equations generated from
`md2_host` and the exact conjunction `(u_host.wr & in_cfg) &
cfg_address_is_live(ha)` at the chip-top `cfg_host_now` net. `st` and `is_rd`
are free per-cycle inputs; their next-state logic, SPI pin timing, byte
framing, address decode correctness, payload content, synchroniser analog
behaviour and physical timing are outside this milestone. Yosys elaboration and
the Python RTLIL adapter are trusted.

