"""Timing constraints and the timing certificate (SPEC_V2_SCORE.md part A 18.1).

A score states the standard's timing requirements in a `constrain` section:

    constrain
      tSU_DAT  sda change when scl low -> scl rise   >= 250 ns

`measure` checks every constraint against a waveform sampled once per chip cycle: the reference codec's bus
("the score as written") or a pin trace of a compiled image on the cycle-level model ("as compiled"). For each
occurrence of A it takes the first B strictly after it, and reports the worst interval over all pairs, its margin
against the bound, and how many pairs were seen. This is a measurement over the frames supplied, not a proof over
all inputs: the certificate says how many pairs it saw, and a constraint with no pair is UNTESTED, never PASS.

Resolution is one chip cycle (16.7 ns at 60 MHz). An edge is the first cycle at the new level.
"""
from __future__ import annotations

import bisect
from dataclasses import dataclass
from fractions import Fraction

from .ast import Constraint, Score, TEvent
from .model import FCLK, qty_cycles


@dataclass
class CertLine:
    name: str
    text: str            # the constraint as written
    op: str              # >= | <=
    bound_ns: float
    worst_ns: float | None
    margin_ns: float | None
    pairs: int
    at_cycle: int | None   # cycle of the A event of the worst pair
    status: str          # PASS | FAIL | UNTESTED

    @property
    def ok(self):
        return self.status == "PASS"


def _levels(bus, wire):
    w = bus[wire]
    return [1 if v is None else v for v in w]       # a released drive reads as the pull-up


def _edges(lv, edge):
    out = []
    for t in range(1, len(lv)):
        a, b = lv[t - 1], lv[t]
        if a == b:
            continue
        if edge == "change" or (edge in ("rise", "rises") and b == 1) or (edge in ("fall", "falls") and b == 0):
            out.append(t)
    return out


def event_times(score: Score, ev: TEvent, bus) -> list[int]:
    """Chip cycles at which ev occurs on `bus` ({wire: [level per cycle]})."""
    if ev.kind == "edge":
        ts = _edges(_levels(bus, ev.wire), ev.edge)
        if ev.when_wire:
            q = _levels(bus, ev.when_wire)
            want = 1 if ev.when_level == "high" else 0
            ts = [t for t in ts if q[t] == want and q[t - 1] == want]    # the qualifier is stable across the edge
        return ts
    r = score.event(ev.event)
    ts = _edges(_levels(bus, r.wire), r.edge)
    if r.kind == "edge_while":
        q = _levels(bus, r.while_wire)
        want = 1 if r.while_level == "high" else 0
        ts = [t for t in ts if q[t] == want and q[t - 1] == want]
    return ts


def _ev_text(ev: TEvent) -> str:
    if ev.kind == "event":
        return ev.event
    s = f"{ev.wire} {ev.edge}"
    return s + (f" when {ev.when_wire} {ev.when_level}" if ev.when_wire else "")


def constraint_text(c: Constraint) -> str:
    v = c.qty.value
    vs = str(v.numerator) if v.denominator == 1 else f"{float(v):g}"
    return f"{_ev_text(c.a)} -> {_ev_text(c.b)} {c.op} {vs} {c.qty.unit}"


def measure(score: Score, bus, *, fclk: int = FCLK, period: Fraction | None = None) -> list[CertLine]:
    """Check every constraint of `score` on `bus` (a codec Waveform or {wire: [level per chip cycle]})."""
    if hasattr(bus, "wires"):
        bus = bus.wires
    if period is None:
        clk = score.clock_for()
        period = Fraction(fclk) / clk.rate if clk is not None and clk.rate else None
    ns = Fraction(10 ** 9, fclk)
    out = []
    for c in score.constraints:
        # qty_cycles counts time units at the nominal 60 MHz; rescale to this waveform's sample rate
        bound = qty_cycles(c.qty, period) * Fraction(fclk, FCLK) if c.qty.unit not in ("cycles", "beats") \
            else qty_cycles(c.qty, period)
        ta, tb = event_times(score, c.a, bus), event_times(score, c.b, bus)
        worst = at = None
        n = 0
        for a in ta:
            j = bisect.bisect_right(tb, a)
            if j == len(tb):
                continue
            d = tb[j] - a
            n += 1
            if worst is None or (d < worst if c.op == ">=" else d > worst):
                worst, at = d, a
        bound_ns = float(bound * ns)
        if worst is None:
            out.append(CertLine(c.name, constraint_text(c), c.op, bound_ns, None, None, 0, None, "UNTESTED"))
            continue
        worst_ns = float(worst * ns)
        margin = worst_ns - bound_ns if c.op == ">=" else bound_ns - worst_ns
        out.append(CertLine(c.name, constraint_text(c), c.op, bound_ns, worst_ns, margin, n, at,
                            "PASS" if margin >= 0 else "FAIL"))
    return out


def format_certificate(lines: list[CertLine], title: str = "") -> str:
    """A fixed-width table: constraint, bound, worst observed, margin, pairs, status."""
    hdr = f"{'constraint':<10} {'bound':>12} {'worst seen':>12} {'margin':>12} {'pairs':>6}  status"
    rows = [title, hdr] if title else [hdr]
    for ln in lines:
        b = f"{ln.op} {_fmt(ln.bound_ns)}"
        w = _fmt(ln.worst_ns) if ln.worst_ns is not None else "-"
        m = _fmt(ln.margin_ns, signed=True) if ln.margin_ns is not None else "-"
        rows.append(f"{ln.name:<10} {b:>12} {w:>12} {m:>12} {ln.pairs:>6}  {ln.status}")
    return "\n".join(rows)


def _fmt(x, signed=False):
    s = "+" if signed and x >= 0 else ""
    if abs(x) >= 1e6:
        return f"{s}{x / 1e6:.3f} ms"
    if abs(x) >= 1e3:
        return f"{s}{x / 1e3:.3f} us"
    return f"{s}{x:.1f} ns"
