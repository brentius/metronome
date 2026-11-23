"""The RP2350 side of the board twin: a GPIO-timing adapter that drives the loader core against the full-chip RTL.

`TwinBus` executes the operations that `board.metronome_core` yields (`pins`, `wait`, `sample`, `reset_n`, `log`).  The
core's clock is in chip clock cycles; the bus converts a cycle to `CLOCK_PERIOD_PS` and advances simulation time with
`cocotb.triggers.Timer`, so an SCK edge can land anywhere inside a chip clock period, including a fraction of one.

What is modelled: pin-change instants (fractional cycle), SCK period and phase, per-edge jitter, and MISO sampling
inside the SCK high phase.  What is *not* modelled: TT mux/pad delay, RP2350 GPIO output slew or PIO FIFO jitter,
board trace skew, and the metastability a real asynchronous edge can cause (the RTL's two flops sample the level
exactly at the clock edge, with no metastability model).  See README.md.

`ModelMonitor` steps the cycle model (`metronome2.chip.Chip`) with the pin levels the RTL samples at each rising edge
and compares `uo_out`, `uio_out` and `uio_oe` every cycle, so a drift between the loader's pin timeline and its
intended cycle-level behaviour shows up immediately.
"""
from cocotb.triggers import ReadOnly, RisingEdge, Timer

CLOCK_PERIOD_PS = 16000          # 16 ns: the same simulation clock the lockstep bench uses (62.5 MHz; ratios hold)
EDGE_GUARD_PS = 250              # keep every pin change/sample at least this far from a clock edge (simulator race)


class ModelMonitor:
    """Per-cycle RTL-vs-model comparison (the lockstep_v2 contract), driven by the loader's own pin stimulus."""

    def __init__(self, dut, model=None, trace_uo=True):
        if model is None:
            from metronome2.chip import Chip
            model = Chip()
        self.dut = dut
        self.model = model
        self.expected = None
        self.cycle = 0
        self.mismatches = []
        self.mismatch_count = 0  # every mismatch; the list keeps only the first max_reported (review S4)
        self.max_reported = 8
        self.trace_uo = [] if trace_uo else None
        self.compare = True

    async def run(self):
        while True:
            await RisingEdge(self.dut.clk)
            # The level present at this edge is what the RTL's input synchronisers sample, i.e. the model's input
            # for the cycle that just ended.  The model's step returns the pin registers as they stand at the end of
            # that step, which is what the RTL drives during the cycle that starts now.
            ui = int(self.dut.ui_in.value)
            uio = int(self.dut.uio_in.value)
            rst_n = int(self.dut.rst_n.value)
            expected = self.model.step(ui, uio, rst_n)
            await ReadOnly()
            got = (int(self.dut.uo_out.value), int(self.dut.uio_out.value), int(self.dut.uio_oe.value))
            if self.compare and got != expected:
                self.mismatch_count += 1
                if len(self.mismatches) < self.max_reported:
                    self.mismatches.append((self.cycle, expected, got))
            if self.trace_uo is not None:
                self.trace_uo.append(got[0])
            self.cycle += 1

    def mark(self):
        """Trace index of "now": slice `trace_uo[mark_before:mark_after]` to isolate one experiment."""
        return len(self.trace_uo) if self.trace_uo is not None else 0


class TwinBus:
    """Drive `ui_in[2:0]`, `rst_n`, `uio_in` and sample `uo_out[0]` at arbitrary sub-cycle instants of the chip clock.

    Time is kept as `t_ps` nanoseconds-as-picoseconds since the alignment point, which is one clock edge plus
    `EDGE_GUARD_PS`.  `rise_phases` reports the phase of every SCK rising edge *relative to the chip clock edge*
    (the guard is subtracted), so a requested phase of 0.95 that the core honours shows up as 0.95, not 0.9656.
    """

    def __init__(self, dut, ui_high=0, uio_in=0, period_ps=CLOCK_PERIOD_PS):
        self.dut = dut
        self.period_ps = int(period_ps)
        self.ui_high = int(ui_high) & 0xF8
        self.uio_in = int(uio_in) & 0xFF
        self.t_ps = EDGE_GUARD_PS     # time since the chip clock edge, in ps
        self.aligned = False
        self.sck = 0
        self.cs_n = 1
        self.mosi = 0
        self.rise_phases = []         # actual phase (0..1) of every SCK rising edge, for the sweep report
        self.nudges = 0
        self.log = []

    # -- setup -----------------------------------------------------------------------------------------------------
    async def start(self):
        """Align the bus origin to a chip clock rising edge (+guard) so `phase_cycles` is a real chip-clock phase."""
        await RisingEdge(self.dut.clk)
        self.t_ps = EDGE_GUARD_PS
        self.aligned = True
        await Timer(EDGE_GUARD_PS, "ps")

    async def realign(self):
        """Restart the bus timebase at a chip clock edge.

        Every race-guard nudge shifts the pin timeline by up to `EDGE_GUARD_PS`, and that shift is permanent, so
        without this the requested phase would slowly walk between sweep points.  Re-aligning between points keeps
        the dependency of one point on the previous one to at most the nudges inside that point (recorded in the
        report as `rise_phase_min`/`rise_phase_max` and `nudges`).
        """
        await RisingEdge(self.dut.clk)
        self.t_ps = EDGE_GUARD_PS
        await Timer(EDGE_GUARD_PS, "ps")

    def set_ui_high(self, value):
        self.ui_high = int(value) & 0xF8
        self._drive()

    def set_uio_in(self, value):
        self.uio_in = int(value) & 0xFF
        self._drive()

    # -- ops -------------------------------------------------------------------------------------------------------
    async def run(self, gen):
        if not self.aligned:
            await self.start()
        send = None
        started = False
        while True:
            try:
                operation = gen.send(send) if started else next(gen)
            except StopIteration as stop:
                return stop.value
            started = True
            send = None
            kind = operation[0]
            if kind == "pins":
                self._pins(operation[1], operation[2], operation[3])
            elif kind == "wait":
                await self._wait(operation[1])
            elif kind == "sample":
                send = int(self.dut.uo_out.value) & 1
            elif kind == "reset_n":
                self.dut.rst_n.value = operation[1]
            elif kind == "log":
                self.log.append(operation[1])
            else:
                raise ValueError("unknown loader op %r" % (kind,))

    # -- bus primitives --------------------------------------------------------------------------------------------
    def _pins(self, sck, cs_n, mosi):
        previous = self.sck
        self.sck, self.cs_n, self.mosi = sck & 1, cs_n & 1, mosi & 1
        if self.sck and not previous:
            # Phase inside a chip clock period, measured from the clock edge the bus was aligned to.
            offset = self.t_ps - EDGE_GUARD_PS
            self.rise_phases.append((offset % self.period_ps) / float(self.period_ps))
        self._drive()

    def _drive(self):
        self.dut.ui_in.value = self.ui_high | self.sck | (self.cs_n << 1) | (self.mosi << 2)
        self.dut.uio_in.value = self.uio_in

    async def _wait(self, cycles):
        dt = int(round(cycles * self.period_ps))
        if dt < 1:
            dt = 1
        target = self.t_ps + dt
        phase = target % self.period_ps
        if phase < EDGE_GUARD_PS:
            dt += EDGE_GUARD_PS - phase
            self.nudges += 1
        elif phase > self.period_ps - EDGE_GUARD_PS:
            dt += self.period_ps - phase + EDGE_GUARD_PS
            self.nudges += 1
        self.t_ps += dt
        await Timer(dt, "ps")
