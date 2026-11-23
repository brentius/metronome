# SCK sweep: where does the Metronome host link actually stop working?

Answer, measured on the full-chip RTL with the real host loader core (evidence class: **RTL-simulated**):

| Claim | Verdict |
|---|---|
| SPEC v2 9 "keep SCK at or below clk/16 (3.75 MHz at 60 MHz)" | **Safe with margin.** All 12 SPEC-conforming points pass: every tested phase and jitter at clk/16, and clk/8 (twice the limit) at every tested phase. |
| Lockstep bench practice "writes at clk/4, reads at clk/16" | **Writes: yes, comfortably** (they still land at clk/2). **Reads: no** — at clk/4 the ID read and the data-RAM read fail; only the single-byte register read survives. |
| Maximum SCK at which every tested phase works | **clk/8** for reads and writes (2x the spec limit). clk/6 passes at one of the two tested coarse phases and at 3 of 10 fine phases, so it is a lucky-phase result, not a rate. |
| Maximum SCK for writes only | **clk/2** (half the spec period) in this sweep: a one-cycle-wide SCK high pulse is still captured by the two-flop synchroniser when its phase keeps it away from the clock edge. |
| Read failures are phase-dependent, not a cliff | **Yes.** At clk/5 the ID read passes at phases 0.62-0.92 and fails at 0.02-0.52; at clk/6 the data-RAM read passes at 0.72-0.92 and fails everywhere else. |
| The failures are a protocol limit, not an RTL/model divergence | **0 mismatching cycles** in 175 350 compared cycles across 38 points, and 0 in the 20 fine-phase points. |

## Provenance

- Repository `metronome-v4.0` at `b7b4068` with an uncommitted working tree; `src/` was not modified by this work.
- Run date 2026-11-19. Python 3.12.10, cocotb 2.1.0, Icarus Verilog 14.0 (devel) `s20260301-638-ge072b3334-dirty`
  from OSS CAD Suite `20261022`, IHP SRAM behavioural models from `test/sram_model/` (via
  `code/tests/lockstep_v2/rtl_sources.py`).
- Simulated chip clock: 16 ns period (62.5 MHz), the same period the lockstep bench uses. Every SCK number below is a
  **period in chip clock cycles** (`clk/N`), so it does not depend on that choice; `sck_hz_at_60mhz` in the JSON gives
  the 60 MHz equivalent (clk/16 = 3.75 MHz).
- Commands and raw output: `evidence/README.md`, `evidence/pytest_full_20261119.log`,
  `evidence/sweep_results.json`, `evidence/fine_phase_results.json`. The two tables below are rendered from those two
  JSON files by `sweep_table.py`; `test_sweep_table_in_sw_results` fails if this file stops matching the JSON.
- Reproduce one point: `TWIN_GRID=6:0.5:0.05 python -m pytest code/tests/board_twin -q -k sweep -s`.

## Method

For each point: re-align the twin's timebase to a chip clock edge, reset the chip through the loader, read `CTRL.ID`
(must be 0xA2), write 4 bytes to data RAM (0x1040..0x1043) and read them back, write `LRT0.PHASE` = 0x1234 and read it
back, then read the data RAM and the register again at clk/16. That last step separates the two failure modes:
`write ... ok` means the chip state is correct (the write path survived the timing point), `read ... ok` means MISO
was still valid at that SCK rate. All byte comparisons and the cycle-model comparison go through one verdict,
`twin_check.link_problems()`; `twin_negative` shows that the same verdict rejects a single corrupted byte and an SCK
rate eight times over the limit.

`phase` is the requested phase, inside a chip clock period, of the **first SCK rising edge of every transaction**. The
loader computes the CS_N-low wait so that this holds exactly for any period, and pays the sub-cycle remainder back in
the CS_N-high gap so it does not accumulate (`Timing.phase_setup_cycles`, `Timing.phase_return`). `TwinBus` records
the phase of every rising edge it actually produced, measured from the chip clock edge; for 33 of the 38 points
`rise_phase_min == rise_phase_max == phase` to 4 decimal places, two more agree to 2e-4, and the three exceptions are
the two jitter points and the non-integer period, where the edges walk on purpose.

`jitter` is uniform ±jitter on every SCK half period (an RP2350 GPIO scheduling model, deterministic LCG seed).
`sample lead` is where MISO is sampled: the fraction of the SCK half period *before* the rising edge (0.25 = two chip
cycles before the edge at clk/16). The twin nudges any pin change that would land within 250 ps of a clock edge
(a simulator race guard; 28 nudges over the 38 points, and the achieved phase is recorded after the nudge).

## Full table (38 points, 175 350 simulated chip cycles, all values after the two-step check above)

| SCK | period (chip cycles) | phase | jitter | sample lead | ID | read RAM | read reg | write RAM | write reg | model mismatches | verdict |
|---|---|---|---|---|---|---|---|---|---|---|---|
| clk/32 | 32 | 0.05 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/32 | 32 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/32 | 32 | 0.95 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/24 | 24 | 0.05 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/24 | 24 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/24 | 24 | 0.95 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/20 | 20 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/16 | 16 | 0.05 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/16 | 16 | 0.37 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/16 | 16 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/16 | 16 | 0.95 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/16 | 16 | 0.50 | 0.45 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/15.5 | 15.5 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/15 | 15 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/15 | 15 | 0.95 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/12 | 12 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/10 | 10 | 0.95 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/8 | 8 | 0.05 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/8 | 8 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/8 | 8 | 0.95 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/6 | 6 | 0.50 | 0.00 | 0.25 | ok | **fail** | ok | ok | ok | 0 | FAIL |
| clk/6 | 6 | 0.95 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/5 | 5 | 0.05 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/5 | 5 | 0.50 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/4 | 4 | 0.05 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/4 | 4 | 0.37 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/4 | 4 | 0.62 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/4 | 4 | 0.95 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/4 | 4 | 0.50 | 0.30 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/3.5 | 3.5 | 0.50 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/3 | 3 | 0.50 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/3 | 3 | 0.95 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/2 | 2 | 0.05 | 0.00 | 0.25 | **fail** | **fail** | **fail** | ok | ok | 0 | FAIL |
| clk/2 | 2 | 0.50 | 0.00 | 0.25 | **fail** | **fail** | **fail** | ok | ok | 0 | FAIL |
| clk/2 | 2 | 0.95 | 0.00 | 0.25 | **fail** | **fail** | **fail** | ok | ok | 0 | FAIL |
| clk/8 | 8 | 0.50 | 0.00 | 0.05 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/6 | 6 | 0.50 | 0.00 | 0.05 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/4 | 4 | 0.50 | 0.00 | 0.05 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |

- full link (ID read + RAM read + register read + writes) at every tested phase: clk/8, clk/10, clk/12, clk/15, clk/15.5, clk/16, clk/20, clk/24, clk/32
- reads at every tested phase: clk/8, clk/10, clk/12, clk/15, clk/15.5, clk/16, clk/20, clk/24, clk/32
- writes at every tested phase: clk/2, clk/3, clk/3.5, clk/4, clk/5, clk/6, clk/8, clk/10, clk/12, clk/15, clk/15.5, clk/16, clk/20, clk/24, clk/32
- model mismatches over all points: 0

### Fine phase sweep at the read boundary

Ten phases per period with the same method and 0.25 sample lead (separate run, 62 920 simulated chip cycles, 20
points, 2 nudges, 0 model mismatches). Every phase in this table is the achieved phase, exactly as requested:

| SCK | phase 0.02 | phase 0.12 | phase 0.22 | phase 0.32 | phase 0.42 | phase 0.52 | phase 0.62 | phase 0.72 | phase 0.82 | phase 0.92 |
|---|---|---|---|---|---|---|---|---|---|---|
| clk/5 ID read | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** | ok | ok | ok | ok |
| clk/5 RAM read | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** |
| clk/5 register read | ok | ok | ok | ok | ok | ok | ok | ok | ok | ok |
| clk/5 RAM write | ok | ok | ok | ok | ok | ok | ok | ok | ok | ok |
| clk/5 register write | ok | ok | ok | ok | ok | ok | ok | ok | ok | ok |
| clk/6 ID read | ok | ok | ok | ok | ok | ok | ok | ok | ok | ok |
| clk/6 RAM read | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** | ok | ok | ok |
| clk/6 register read | ok | ok | ok | ok | ok | ok | ok | ok | ok | ok |
| clk/6 RAM write | ok | ok | ok | ok | ok | ok | ok | ok | ok | ok |
| clk/6 register write | ok | ok | ok | ok | ok | ok | ok | ok | ok | ok |

- full link (ID read + RAM read + register read + writes) at every tested phase: none
- reads at every tested phase: none
- writes at every tested phase: clk/5, clk/6
- model mismatches over all points: 0

The read capability does not switch off at one period: it degrades into a phase-dependent "does the response arrive
before the sample point" race. clk/8 is the last period that works at every tested phase; clk/6 works at 3 of 10
phases and clk/5 at none for the data RAM, so clk/8 is the honest rate for a loader that cannot choose its phase.

## Why reads stop before writes

The target does not shift `TX` (MISO) on the SCK edge itself: the edge is seen through the two-flop synchroniser, so
`TX` updates **two to three chip clocks after** the SCK rising edge (SPEC v2 2 and 9, `md2_host.v`). A master must
therefore sample MISO **at or before** the rising edge. That gives the read path two separate deadlines:

1. the previous byte's data must already be in `TX` when the sample point arrives — a register read loads `TX` at the
   end of R+1 (SPEC v2 9), i.e. about two cycles after the address byte's last edge, and a data-RAM read adds the host
   request, the arbiter and the landing cycle (SPEC v2 6.2, 9), two to three cycles more;
2. the sample must still be before the shift that follows the next edge.

Deadline 1 shrinks with the period, so a single-byte register read keeps working down to clk/3-4 (its data is ready
in time) while a data-RAM read already fails at clk/6 except at the late phases, and even the ID read fails at clk/5
for the early phases — exactly the `read RAM fail / read reg ok` pattern in both tables. Moving the MISO sample from
0.25 to 0.05 of the half period (three rows at the bottom of the full table) turns the clk/6 phase-0.5 data-RAM
failure into a pass, which is the same deadline seen from the other side: a later sample is a shorter wait. Deadline
2 sets the write limit: a write only needs the SCK high pulse to be sampled once, which still happens for a
one-cycle pulse at clk/2.

Both mechanisms are **calculated** from the SPEC v2 9 text and the synchroniser latency of assumption A1 in
`wiki/EVIDENCE.md`; the *numbers* above are the RTL-simulated measurement.

## Limits of this sweep

- One sample lead (0.25) for most points, plus three 0.05 points; it is not a two-dimensional sample-point sweep.
- The coarse grid has 2-4 phases per period. Sub-cycle coverage comes from those phases, from the non-integer period
  and from the ±jitter points. A failure at one phase does not mean every phase at that period fails (see clk/6).
- Power-on phase is not random here: the twin aligns the bus to a chip clock edge and sets the phase explicitly. A
  real RP2350 has no such alignment, which is exactly why the clk/8 "works at every phase" result matters.
- No pad/mux delay, no metastability model, no RP2350 GPIO slew, no board skew (see the README). A real board can only
  be *worse* at the fast points; the clk/16 spec point has at least a 2x period margin in this model.
- Only the loader's traffic pattern was swept (single-byte and 4-byte transactions, one write per completed byte).
  D24 (no two configuration writes in consecutive cycles) holds everywhere: even at clk/2 a byte takes 16 cycles.
- **Not measured on hardware.** No board was available for this work.
