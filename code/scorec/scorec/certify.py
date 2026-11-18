"""Timing certificate for a score (SPEC_V2_SCORE.md part A 18.1).

Two views of the same `constrain` section:

* **as written**: the reference codec's bus for given events, at the score's rate. This checks the score itself
  against the standard (a symbol's wave strings can violate a timing on their own).
* **as compiled**: a pin trace of the compiled image running on the cycle-level model, at one sample per chip
  cycle. This checks what the chip does, including the follower's reaction time and tap quantisation.

Both are measurements over the frames supplied (`pairs` says how many intervals were seen); neither is a proof
over every input. The compiler never imports the codec for code generation: this module is a reporting tool only.
"""
from __future__ import annotations

from . import _paths  # noqa: F401
from score.constrain import CertLine, format_certificate, measure  # noqa: F401
from score.model import FCLK


def _score(s):
    if isinstance(s, str):
        from score import parse
        return parse(s)
    return s


def written(score, events, *, params=None, rate=None) -> list[CertLine]:
    """Certificate of the score as written: encode `events` with the reference codec and measure its bus."""
    from score import Codec
    s = _score(score)
    c = Codec(s, params=params, rate=rate)
    enc = c.encode_all(events, lead=int(2 * c.P), tail=int(2 * c.P))
    return measure(s, enc.bus, period=c.P)


def compiled(score, trace: dict, *, fclk: int = FCLK, rate=None) -> list[CertLine]:
    """Certificate of a compiled image: `trace` is {wire: [level per chip cycle]} captured on the cycle model
    (or a logic analyser at one sample per chip cycle)."""
    from fractions import Fraction
    s = _score(score)
    clk = s.clock_for()
    r = rate or (clk.rate if clk is not None else None)
    return measure(s, trace, fclk=fclk, period=Fraction(fclk) / Fraction(r) if r else None)


def report(score, *, written_lines=None, compiled_lines=None) -> str:
    """Text certificate: one table per view supplied, then a one-line verdict."""
    s = _score(score)
    parts = [f"timing certificate: {s.name}"]
    for title, lines in (("as written (reference codec)", written_lines),
                         ("as compiled (cycle-level model trace)", compiled_lines)):
        if lines is not None:
            parts += ["", format_certificate(lines, title)]
    allv = (written_lines or []) + (compiled_lines or [])
    fails = sorted({ln.name for ln in allv if ln.status == "FAIL"})
    untested = sorted({ln.name for ln in allv if ln.status == "UNTESTED"})
    verdict = "PASS" if not fails and not untested else ("FAIL: " + ", ".join(fails) if fails else
                                                        "INCOMPLETE: untested " + ", ".join(untested))
    parts += ["", f"verdict: {verdict}"]
    return "\n".join(parts)
