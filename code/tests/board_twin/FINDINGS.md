# Board-twin findings

Defects found while building item 1 of the hardware-side campaign, how they were confirmed, and what is still open.
Nothing here changes `src/`; the twin and the loader were the sources of every defect.

## 1. The sweep did not sweep the phase it claimed (host software, fixed)

**Symptom.** The previous version of `SpiLink.transaction` computed its first-edge wait as
`cs_setup + ((phase - (half - lead)) % 1)` and then went straight to CS_N high after the last bit. Two things follow
from that formula:

* the first rising edge of a transaction lands at `cs_setup + phase + lead` (mod one), so for a fractional period
  (where `lead = 0.25 * half` is not a whole number of cycles) every edge is `lead` cycles late; and
* the sub-cycle remainder of the CS_N-low wait was never given back, so each transaction shifted the origin by the
  fractional part of `phase` — 0.05, 0.1, 0.15, ... at a requested phase of 0.05.

**Evidence.** The JSON of a run of that code (since regenerated, so the numbers are quoted rather than linked)
recorded, at clk/32 with a requested phase of 0.05, `rise_phase_min = 0.0656` (0.05 plus the 250 ps race guard — the
first transaction, as predicted) and `rise_phase_max = 0.7656` (the accumulated 0.05 per transaction). At a requested
phase of 0.95/clk/16 it recorded 0.3756..0.8756. The "phase" column was decorative, and the phase-dependent
conclusions of the old `SWEEP_RESULTS.md` were drawn from phases nobody chose.

**Reproduction (no simulator).** Print the phase of the first rising edges for a requested phase of 0.95:

```sh
python -c "import sys; sys.path[:0]=['code/tests/board_twin','sim/reference','code/host2']; \
from board.metronome_core import MetronomeHost, Timing; from test_core import PhaseBus, run; \
b=PhaseBus(); run(MetronomeHost(Timing(16.0, 0.95), 60e6).read(0x2407, 1), b); print([round(x, 4) for x in b.rises[:3]])"
```

The current code prints `[0.95, 0.95, 0.95]` and every transaction spans a whole number of chip cycles.
`code/tests/board_twin/test_core.py::test_first_sck_edge_lands_at_the_requested_phase` and
`::test_transaction_spans_whole_chip_cycles` enforce exactly those two properties over integer and fractional periods,
so reintroducing the old formula fails them.

**Fix.** `Timing.phase_setup_cycles` absorbs `phase - half - cs_gap` (mod one) before the first edge and
`Timing.phase_return(nbytes)` pays the remainder back in the CS_N-high gap, so each transaction spans a whole number
of chip cycles and the next one starts where the last one started. `TwinBus.realign()` additionally restarts the
twin's timebase between sweep points, because the 250 ps simulator-race guard permanently shifts the timeline by up to
250 ps per nudge (27 nudges over the 38-point grid).

**Residual, by design:** within a point, a race-guard nudge still shifts the following edges by up to 250 ps
(0.0156 chip cycles), and jitter moves them on purpose. `rise_phase_min`/`rise_phase_max`/`nudges` in the result JSON
are the authoritative record; `phase` is the request.

## 2. The UART test's flow control never ran (host software, fixed)

`twin_uart_tx` had `if not (await bus.run(host.hoststat())) & 1:` — Python parses that as `(not ...) & 1`, which is
always 0, so the "wait for HOST.INV to clear" loop always ran its full 64 iterations (4096 cycles). It worked by
accident (4096 cycles is long enough), and it would have silently overwritten a byte if the loop bound had been
smaller. Replaced by `wait_host_ready()`, which loops on `HOSTSTAT & 1` and raises if `INV` never clears.

## 3. HOSTIN write-phase hazard in the v2 example (known, not fixed, not caused by this work)

`code/host2/examples/uart_tx.mas` has an idle loop that samples `HOST.INV` (guard) and `HOST.IN` (source) in the same
burst, so a `CTRL.HOSTIN` write that lands between those two samples is consumed without a start bit. This is the
documented `F-HOSTIN` finding in `wiki/EVIDENCE.md` (measured at 10 Mbaud: one write phase in twelve); the
compiler-generated v3 idle loop samples once and that version passes without the exclusion, but this hand-written v2
example is the one the board twin loads. The twin's UART check writes two bytes at two different phases and decodes
both, which is a spot check, not a phase sweep. A program-side issue, not RTL and not the loader.

## 4. `ERRSUM` bit 6 is v4-only (documentation, no action)

`wiki/SPEC_V2.md` section 9 defines `ERRSUM` as six bits, `{MEMHAZ, CONFLICT, STARVED, TAPMISS, OVR, LATE}` in bits
5..0. `code/md2/machine.py` (the v4 machine) adds `CWOVR` in bit 6, and `sim/reference/metronome2/regs.py` implements
it. The loader only ever tests `ERRSUM == 0`, so the difference does not affect it; noted so that a reader comparing
the two documents is not surprised. Not a defect in either document: `SPEC_V2.md` describes the v2/RTL it names, and
the branch is v4.

## 5. Not a finding, recorded because it bounds the evidence

The twin's `ModelMonitor` compares `uo_out`, `uio_out` and `uio_oe` against `metronome2.chip.Chip` on every cycle of
every run and records zero mismatching cycles, including at the timings where the *link* fails. So the failures
reported in `SWEEP_RESULTS.md` are host-link protocol limits, not RTL/model divergence.
