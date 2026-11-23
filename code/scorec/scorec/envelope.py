"""Calculate a timing envelope for a statically compiled 8N1 receiver."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import ceil


@dataclass(frozen=True)
class ReceiveEnvelope:
    sample_cycles: tuple[int, ...]
    rearm_cycles: int
    margin_cycles: Fraction
    low_error: Fraction
    high_error: Fraction

    def require(self, rate_error: Fraction) -> None:
        """Reject a symmetric sender rate tolerance outside the open interval."""
        if rate_error < 0 or not self.low_error < -rate_error <= rate_error < self.high_error:
            raise ValueError(f"sender rate error ±{float(rate_error):.3%} exceeds the calculated envelope "
                             f"({float(self.low_error):.3%}, {float(self.high_error):.3%})")


def uart8n1_envelope(compiled, *, jitter_cycles: Fraction = Fraction(0),
                     idle_bits: Fraction = Fraction(0)) -> ReceiveEnvelope:
    """Bound sender rate error for a generated, single-line 8N1 receiver.

    Positive error means a faster sender relative to the score's nominal
    rate. `sample_cycles` is measured from the synchronized start event.
    A one-cycle margin covers asynchronous quantization and start detection
    versus level sampling. `jitter_cycles` bounds additional displacement of
    any bit boundary relative to the first edge. `idle_bits` is a guaranteed
    extra gap between contiguous 8N1 frames in sender bit periods.

    Assumes a settled, armed chip, the v2 digital pin model, and the static
    scheduler check's operating conditions. Board/metastability effects are
    outside this calculation. No re-alignment or autobaud is supported here.
    """
    if jitter_cycles < 0 or idle_bits < 0:
        raise ValueError("jitter and idle gap must be nonnegative")
    program, ctx, report = compiled.program, compiled.ctx, compiled.check_report
    if (program is None or ctx is None or report is None or not report.ok or ctx.clk.mode != "started"
            or ctx.opts.get("autobaud") or ctx.opts.get("listener")
            or set(program.lines) != {0} or len(program.threads) != 1):
        raise ValueError("expected a statically checked 8N1 receiver with a single phase-tap thread")
    shape = [step for step in ctx.frame if step.kind != "gap"]
    if (len(shape) != 3 or [step.kind for step in shape] != ["sym", "field", "sym"]
            or shape[0].args != (0,) or shape[2].args != (1,)
            or any(step.count != 1 for step in shape) or shape[1].f.type.kind != "u"
            or shape[1].f.type.width != 8 or compiled.score.bits.order != "lsb"
            or compiled.score.bits.invert):
        raise ValueError("expected a start bit, eight LSB-first data bits and one stop bit")
    line = program.lines[0]
    thread = next(iter(program.threads.values()))
    if (not line.inc or line.inc >= line.mod or line.snap not in range(3) or not line.phase_tap(line.snap)
            or not line.pre < line.tap(line.snap) or line.ctl != 2 or line.follow or line.hen
            or line.edge_pin != line.pina or line.edge_pol != 2 or not thread.enable
            or thread.trigger != f"L0.TAP{line.snap}"):
        raise ValueError("receiver line must arm on the start edge and sample at a later phase tap")
    tap = line.tap(line.snap)
    samples = tuple(ceil(Fraction(index * line.mod + tap - line.pre, line.inc)) for index in range(10))
    margin = Fraction(1) + jitter_cycles
    rearm = report.threads[thread.n].resp_last
    if samples[0] <= margin:
        raise ValueError("first sample has no margin from the start edge")
    period = Fraction(ctx.clk.period)
    low = max(index * period / (cycle - margin) - 1 for index, cycle in enumerate(samples))
    high_sample = min((index + 1) * period / (cycle + margin) - 1 for index, cycle in enumerate(samples))
    high_rearm = (10 + idle_bits) * period / (samples[-1] + rearm + margin) - 1
    high = min(high_sample, high_rearm)
    if low >= high:
        raise ValueError("sample and re-arm timing leave no sender rate envelope")
    return ReceiveEnvelope(samples, rearm, margin, low, high)
