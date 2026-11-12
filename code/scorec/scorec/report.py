"""Fit and timing report (SPEC A 12) and diagnostics in protocol terms (A 12.3)."""
from __future__ import annotations

from fractions import Fraction

from score.model import FCLK


def fastest_period(rep, ctx) -> int | None:
    """Smallest beat length in cycles at which every thread of a generated line meets its deadlines (calculated from
    the static check's burst data: overrun n + 2 + Sigma + 1 <= beat, commit s + 2 + Sigma <= beat)."""
    need = 0
    for tr in rep.threads.values():
        if tr.gap_beat is None and tr.gap_self is None and tr.gap_snap is None:
            continue
        need = max(need, tr.n_max + 3 + tr.others, (tr.sym_max + 2 + tr.others) if tr.sym_max else 0)
    return need or None


def time_diag(ctx, prog, rep, err: str) -> str:
    fp = fastest_period(rep, ctx)
    s = f"E-TIME   grammar: {err}"
    if fp and ctx.clk.period:
        s += (f"\n         beat is {float(ctx.clk.period):.2f} cycles at {FCLK / float(ctx.clk.period) / 1e6:.4g} MHz; "
              f"fastest rate that fits: {FCLK / fp / 1e6:.4g} MHz ({fp} cycles per beat)")
    return s


def fit_report(c) -> str:
    x = c.ctx
    L = []
    L.append(f"fit report: {c.score.name} / role {c.role}")
    clk = x.clk
    if clk.period is not None:
        L.append(f"  clock      {clk.mode}; beat {float(clk.period):.3f} cycles at 60 MHz = "
                 f"{FCLK / float(clk.period) / 1e6:.6g} MHz; {clk.note}")
    else:
        L.append(f"  clock      {clk.mode}; MOD {clk.mod} cycles (longest clock period accepted)")
    for t in x.taps:
        if clk.period is not None:
            exact = float(t.frac) * float(clk.period)
            got = t.T / clk.inc
            L.append(f"  tap {t.idx}      phase {t.T}/{clk.mod} = {got:.2f} cycles (asked {float(t.frac) * 100:g}% = "
                     f"{exact:.2f} cycles, error {got - exact:+.2f}); {t.why}")
    if x.txp:
        t = x.txp
        L.append(f"  symbols    {len(t.classes)} classes drive wires {t.wires}; encoding {t.encoding}; idle = code 0")
        for cl in t.classes:
            L.append(f"             code {cl.code:2d}  {', '.join(cl.members)}")
        L.append("  pins       " + ", ".join(f"{w} -> O{x.bind[w][1]} (sel bits {t.sel[w]})" for w in t.wires))
    if x.rxp:
        L.append(f"  input      pins A=P{x.rxp.pina}" + (f" B=P{x.rxp.pinb}" if x.rxp.pinb is not None else "") +
                 f"; {x.rxp.classes}")
    L.append(f"  program    core 0: {x.b.cores[0].ninsn} instructions, core 1: {x.b.cores[1].ninsn} instructions")
    if c.check_report is not None:
        for tr in c.check_report.threads.values():
            L.append(f"  thread {tr.n}   core {tr.core}: longest burst {tr.n_max} cycles; trigger -> last instruction "
                     f"{tr.resp_last}" + (f"; last symbol write at burst cycle {tr.sym_max}" if tr.sym_max else "") +
                     (f"; last input read at burst cycle {tr.in_max}" if tr.in_max else ""))
        fp = fastest_period(c.check_report, x)
        if fp and clk.mode == "generated":
            L.append(f"  rate       fastest generated rate that fits: {FCLK / fp / 1e6:.4g} MHz ({fp} cycles per beat; "
                     f"calculated from the burst lengths above)")
    for n in x.notes:
        L.append(f"  note       {n}")
    for w in c.warnings:
        L.append(f"  warning    {w}")
    for e in c.errors:
        L.append(e)
    return "\n".join(L)
