# Configuration address-decode Lean evidence (2026-11-18)

Baseline: `metronome-v4.0` at `b7b40687cc26419bed64a25c467ed91be65f28a9`
plus the untracked `code/tests/lean` work. The RTL snapshot used by the runner
has SHA-256
`434c6ae6e52b85991f0be864394e5c93382f4aa239c9302ae0ef91d19dab2b3b`
(the digest the runner prints before elaborating the chip top).

## Contents

- `proof/` — canonical `python code/tests/lean/verify.py --mutations` run:
  `tools.log`, `lake.log`, per-case `*.log`, `*.host.log`, `*.decode.log`,
  and the generated `*.lean` / `*.host.lean` / `*.decodehost.lean` /
  `*.decodecore.lean` inputs.
- `verify_stdout.log` — console output of the same run, including the accepted
  baseline, all 13 mutation outcomes and the two decode `#print axioms` lines.
- `pytest_v4_model.log` — 23 v4 cycle-model checks.
- `pytest_lockstep.log` — `v4_config_write` and `spi_target` full-chip Icarus
  lockstep cases.
- `gen_rtl_tables.log` — `gen_rtl_tables.py --check` output.
- `manifest.sha256` — SHA-256 of the files above (excluding itself).
- `run_status.txt` — wrapper-written command, exit code and tool versions. Its
  `case_count` line reads `13 (baseline plus 12 mutations)`, which is a
  miscount: the command runs 14 cases (accepted baseline plus 13 mutations).
  The raw line is preserved; the corrected count, with the evidence for it, is
  in `data/processed/lean_decode_v4_20261118/RECONCILIATION.md`.

`baseline_confirm/` is a supplementary baseline-only `verify.py` invocation
run after the canonical run; its `verify_stdout.log` ends with a captured
`EXIT=0`. `pytest_selected.log`/`pytest_selected.xml` are the combined 25-test
selection from the same session (23 v4 cycle-model plus `v4_config_write` and
`spi_target`). Both are preserved as separate evidence and are not covered by
this manifest.

## What the run proves

For every 16-bit address `a`, the translated elaborated host qualification
`in_cfg & cfg_address_is_live(ha)` (`Decode.rtlHostQual`) and the translated
elaborated core `cw_is_cfg` (`Decode.rtlCoreLive`) equal
`Decode.specLive a = inWindow a && maskLive a`. The kernel checks that the
42 maximal non-zero runs are exactly the 284 non-zero bytes of the elaborated
480-byte `u_cfg` `MASK` parameter, and that each `liveBytes` flag equals the
corresponding `MASK` byte being non-zero. The adapter checks the bank structure
(one clock gate and exactly the masked latch set per non-zero byte; the gate is
enabled by `we1` and an `addr1`-only select; each latch has the right `D`, `Q`,
`RESET_B` and gate; zero bits/bytes are tied off) and the arbiter wiring
(`host_addr = a_cfg[8:0]`, `core_addr = cw_pending_addr[8:0]`, `cw_is_cfg` in
the `core_valid` cone).
`Decode.offset_fits_nine` shows an accepted 16-bit offset is below 512, so the
nine-bit arbiter address carries the full window offset.

Boundary facts on the actual nets: `0x2000` and `0x21D7` are live, `0x201D`
is a mask hole, `0x20D0` is a partial `0x03` byte, `0x21DF` passes `in_cfg`
but is mask-zero, `0x21E0` is outside the window, and `0x1FFF` wraps below the
base. `Decode.first_live`, `Decode.last_live`, `Decode.hole_201D`,
`Decode.partial_byte`, `Decode.host_tail_indexed_not_live`,
`Decode.out_of_window`, `Decode.wrapped_below` and the per-site facts are
kernel `decide` results.

## Mutations

The canonical run accepted the baseline and rejected 13 planted changes at the
intended layer:

- `spacing`, `priority`, `held_addr`, `held_data`, `stage_capture` — Lean
  configuration equivalence.
- `feedback` — top-level wiring check.
- `host_gate`, `host_counter` — Lean host equivalence.
- `host_filter` — chip-top host-filter check.
- `decode_permissive` (`CFG_VALID_LINE_0` 32'h1FFFFFFF -> 32'hFFFFFFFF) — both
  decode equivalence proofs. The extra live bytes have no latches, so a
  write/readback bench cannot see this regression.
- `decode_core_bypass` (core decode sees address bit 1 in place of bit 0) —
  core decode equivalence only; the host decode proof is reused.
- `decode_mask_byte` (byte 30 of `CFG_MASK` becomes `0xFF`) — both decode
  equivalence proofs; the RTL still decodes `0x201E` as a hole while the
  elaborated bank now has a latch there.
- `decode_core_addr` (core arbiter address bit 0 forced low) — core arbiter
  address wiring check.

## Trust and scope

The decode theorems that use Lean's `bv_decide` (the two full-address
equalities, the interval/flag equivalence and the offset bound) rely on its
bit-blasted SAT certificate, which is checked by Lean's native LRAT checker.
`#print axioms` on the equalities shows a per-theorem native certificate axiom
in addition to `propext`, `Classical.choice` and `Quot.sound`. The runner checks that `sorryAx` is absent
and that the native `bv_decide` audit is present. The run/mask theorems and
boundary facts are kernel `decide`; the structural checks are Python. The
existing trust in Yosys elaboration, the RTLIL adapter and the JSON parameter
reader is unchanged.

Covered: the two configuration address-decode sites, the implemented bank mask
bits, and the connected nine-bit arbiter offsets. Not covered: payload content,
latch visibility and clock-to-Q timing, SPI pin timing and byte framing, the
core pending-write queue, the reset synchroniser analog behaviour, physical
timing and the rest of the chip top.
