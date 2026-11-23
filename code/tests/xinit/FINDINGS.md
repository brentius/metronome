# Findings: reset and power-up campaign

Scope: item 3 of `BOTS/PLANS/HW_VERIFY_20261119.md`, committed RTL at `b7b4068` plus the uncommitted working
tree. No `src/` change was made or is proposed here. Classes follow `AGENTS.md`.

## 1. No RTL defect found

The campaign found no case where reset, power-up or a mid-run reset leaves the RTL in a state that differs
from the model, and no X reaches a pin after reset+load under the tested stimuli. All default tests and the
heavy seed runs pass (`README.md`, `evidence/20261119/`).

## 2. The earlier divergence: a real bench artifact, reproduced and fixed

The partial work attributed an earlier mismatch to a bench deposit artifact but retained no log and left the
offending names in `storage_paths.json`. The heavier seed set reproduced it: **seed 5 of
`random_all-xinit_load_run` failed 138 cycles from cycle 5,069**, with the enabled loopback pin staying low
while the model toggled (`run_pin_values = [0]`). Random SRAM alone passed.

Bisection at seed 5, depositing only the named subset in `random_flops` mode (normal/zero SRAM, so only the
deposit varied). Each of these passed: SRAM-only; `ir`; all non-reset sites; the line, thread, stream, memory,
config and host groups; the core's `{src, mv_*, dbg_*, xt_o, xt_o}` and `{xv, rv, fpc, rr, xt, xl}` groups
separately. These failed: all registers; the core group; and the core state registers plus `{xt_o, xl_o}`.
**RTL-simulated.**

`xt_o` and `xl_o` are `output wire` ports (`assign xt_o = xt; assign xl_o = xl;`), i.e. nets with a
continuous driver, not flops. A VPI deposit on them sticks and overrides the port until the flop changes, so
the rest of the chip selects the wrong dispatching thread.

Root cause in `inventory_flops.py`: `declared_regs` matched `\breg\b([^;]*);`, which in an ANSI port list
runs from `output reg disp_e,` to the **end of the port list**, so every later port — including all
`output wire` ports (`xt_o`, `xl_o`, `mv_src`, `mv_dst`, `dbg_*`, `miso`, `req_*`) — was treated as a
declared reg. A second hole: `opt_clean` merges combinational nets into flop bits, so the 512-bit
combinational vectors `src`, `sv` and `gv` also named storage bits and were deposited whole.

Fix, both fail-closed:

* the port list is parsed item by item, so only `output reg`/`reg` items contribute names;
* a name is used only when every one of its bits is a storage Q bit or a constant, which rejects `src`, `sv`
  and `gv` because most of their bits are mux outputs.

The deposit list went from 2,652 to 2,627 paths and now accounts for exactly 3,797 bits — the inventory's
non-SRAM storage total — so every deposit lands on storage and nothing else. Seed 5 passes, and seeds 1–8 pass
in the heavy set. `test_inventory` regenerates and compares the snapshot on every run.

This confirms the deposit-artifact diagnosis with a precise mechanism; the fix is in the bench inventory, not
the RTL. The earlier "not reproducible" entry was written from the default three seeds; the failure appears at
seed 5 of the load/run case.

## 3. Reference model vs RTL: reset release after a sub-cycle pulse

`sim/reference` resets on clocked `rst_n`: one asserted `step` holds reset for three edges
(`rst_hold = 2`), matching the RTL's `rst_m`/`rst_q` synchroniser for a clock-sampled reset. For a pulse
shorter than a cycle that ends before a rising edge, the RTL clears `rst_q` asynchronously and resets for two
edges, so the RTL runs one edge before the model.

The bench compares from 3 cycles after the last asserted reset. With the constant host preamble used by
every scenario, `s1`/`s2`/`sp` hold the same idle value in both, so all pulse cases pass. A stimulus that
changed `ui_in`/`uio_in` within two cycles of a sub-cycle reset would expose the one-edge offset; any future
scenario of that shape needs a settle window or a model change. This is a **calculated** limitation of the
comparison, confirmed by the 1 ps/1 ns/4 ns pulse runs (`reset_latency.edges_low` = 1, model holds 1 extra
edges). No RTL change is implied; the RTL matches SPEC 1 (async assert, two-edge release).

## 4. Host-contract counterexample is by design, not a bug

`x_probe` writes five bytes at `0x123`, then reads five. The read command issues one extra lookahead read of
the *next* byte, which lands in word 74 (byte `0x128`). Because that word was never written, Icarus' X SRAM
returns X and `uo_out` (MISO) goes X from cycle 1308. The monitor also records the default stream
configuration's prefetch of data word 0 at cycle 6 (load/run) and 8 (reset-only) before any host write.

Both are host obligations, recorded in the README table, not RTL defects: a real SRAM returns unknown data
for unwritten words, and the design does not claim otherwise.

## 5. Tooling: a flattened netlist's SRAM array is not reachable through Icarus VPI

At gate level the SRAM macros appear as top-level escaped instances (`\u_dmem.u_sram`). Cocotb discovers the
instance and its ports, but not the model's internal `memory` array: Icarus reports the nested scope's
sub-elements in a format cocotb's GPI rejects (`Unhandled Sub-Element Format - i_SRAM_1P_behavioral_bm_bist`).
A hierarchical reference in Verilog (`tt_um_brentius_metronome.\u_pmem0.u_sram .i_...memory[i]`) does not
elaborate either. Gate-level random-SRAM init therefore compiles a copy of the SRAM core model with a
power-up `initial` gated by `+xinit_random_sram`. **RTL tooling limitation, not a design finding.** Verified
by compiling the v1 template netlist and seeing 512 + 256 + 256 words filled; not yet run on a v4 netlist.

## 6. Unused scenario kept for diagnosis

`xinit_load_run_short` loads only the executed instruction and leaves the fetch-ahead word unloaded. It ran
once under X-init: no X reached a pin within the scenario and the loopback pin never became an output, so it
does not demonstrate a failure and is not part of the default suite. It stays as a probe for a future
stimulus that forces the core to dispatch the unloaded word.

## 7. Gaps

* **Gate level: run 2026-11-19 on the routed v4 netlist, 5 passed (see README, Gate level).** At delivery it was not run: No routed v4 netlist was available locally and no pod was started. `run_gate.sh`
  is prepared and syntax-checked; its RTL-side paths are covered by the RTL suite.
* **Silicon minimum reset pulse width: not established.** Only the digital asynchronous-clear behaviour is
  simulated; the cell-level pulse-width and recovery/removal limits are assumed, not measured.
* **No hardware evidence.** Nothing here says anything about metastability, reset distribution skew or SRAM
  power-up contents on silicon; the SRAM randomisation is a simulation model.
* **X-init is bounded by stimulus.** Storage not read by a scenario can stay X indefinitely; the campaign
  covers reset plus the documented load/run/read sequences only.
