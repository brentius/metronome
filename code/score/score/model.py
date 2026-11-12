"""Shared semantics helpers: wave strings, symbol instances, expressions, clocks, types."""
from __future__ import annotations

import itertools
from fractions import Fraction

from .ast import *  # noqa: F403

FCLK = 60_000_000   # chip clock, Hz (RP2350 demo-board clock, confirmed OK at 60 MHz)
EVENT_NAMES = ("violation", "mismatch", "timeout", "lost")
DATA_SYMBOL = "bit"


class EvalError(Exception):
    pass


# ---- expressions ---------------------------------------------------------------------------------------------
def eval_expr(e, env: dict):
    if isinstance(e, Num):
        return e.value
    if isinstance(e, Name):
        if e.name not in env:
            raise EvalError(f"{e.pos[0]}:{e.pos[1]}: E-NAMES: '{e.name}' has no value here")
        return env[e.name]
    if isinstance(e, Un):
        a = eval_expr(e.a, env)
        return {"!": int(not a), "~": ~a, "-": -a}[e.op]
    if isinstance(e, Cond):
        return eval_expr(e.a, env) if eval_expr(e.c, env) else eval_expr(e.b, env)
    if isinstance(e, Bin):
        a, b = eval_expr(e.a, env), eval_expr(e.b, env)
        op = e.op
        if op == "&&":
            return int(bool(a) and bool(b))
        if op == "||":
            return int(bool(a) or bool(b))
        if op in ("/", "%") and b == 0:
            raise EvalError("division by zero")
        return {"+": lambda: a + b, "-": lambda: a - b, "*": lambda: a * b, "&": lambda: a & b,
                "|": lambda: a | b, "^": lambda: a ^ b, "<<": lambda: a << b, ">>": lambda: a >> b,
                "==": lambda: int(a == b), "!=": lambda: int(a != b), "<": lambda: int(a < b),
                ">": lambda: int(a > b), "<=": lambda: int(a <= b), ">=": lambda: int(a >= b),
                "/": lambda: a // b, "%": lambda: a % b}[op]()
    raise EvalError(f"cannot evaluate {e!r}")


def expr_names(e, out=None):
    out = set() if out is None else out
    if isinstance(e, Name):
        out.add(e.name)
    elif isinstance(e, Un):
        expr_names(e.a, out)
    elif isinstance(e, Bin):
        expr_names(e.a, out)
        expr_names(e.b, out)
    elif isinstance(e, Cond):
        for x in (e.c, e.a, e.b):
            expr_names(x, out)
    return out


def expr_cost(e) -> int:
    """Rough instruction-count estimate: one per operator or operand reference."""
    if isinstance(e, (Num, Name)):
        return 1
    if isinstance(e, Un):
        return 1 + expr_cost(e.a)
    if isinstance(e, Bin):
        return 1 + expr_cost(e.a) + expr_cost(e.b)
    if isinstance(e, Cond):
        return 2 + expr_cost(e.c) + expr_cost(e.a) + expr_cost(e.b)
    return 0


# ---- clock ---------------------------------------------------------------------------------------------------
def boundaries(clock: Clock | None) -> list[Fraction]:
    split = clock.split if clock else [Fraction(1, 2)]
    return [Fraction(0)] + list(split) + [Fraction(1)]


def nseg(clock) -> int:
    return len(boundaries(clock)) - 1


def beat_cycles(clock: Clock | None, rate=None) -> Fraction:
    """Beat length in chip cycles (exact; may be fractional, e.g. 115200 Hz -> 520.83...)."""
    r = rate if rate is not None else (clock.rate if clock else None)
    if r is None:
        raise ValueError("clock is 'free': pass rate= (Hz) to the codec")
    return Fraction(FCLK) / Fraction(r)


def qty_cycles(q: Qty, period: Fraction | None) -> Fraction:
    u = q.unit
    if u == "beats":
        if period is None:
            raise ValueError("a duration in beats needs a beat length (clock rate)")
        return q.value * period
    if u == "cycles":
        return q.value
    scale = {"ns": Fraction(1, 10 ** 9), "us": Fraction(1, 10 ** 6), "ms": Fraction(1, 1000), "s": Fraction(1)}
    if u in scale:
        return q.value * scale[u] * FCLK
    raise ValueError(f"bad time unit {u!r}")


# ---- wires ---------------------------------------------------------------------------------------------------
def idle_level(w: Wire):
    """Level the owner drives outside frames: 0, 1 or None (released)."""
    if w.idle == "released":
        return None
    if w.idle == "high":
        return None if w.drive == "open-drain" else 1
    if w.idle == "low":
        return 0
    return None if (w.drive == "open-drain" or w.dir == "shared") else 0


def pulled_level(w: Wire, idle=None):
    """Resolved level of a wire nobody drives."""
    if w.drive == "open-drain" or w.dir == "shared":
        return 1
    return 1 if w.idle == "high" else 0


# ---- symbols -------------------------------------------------------------------------------------------------
def parse_wave(wave: str, params: list[str], pos=None):
    """Wave string -> list of (kind, value): ('c', '0'|'1'|'z'|'x'|'.') or ('p', name, inverted)."""
    out, i = [], 0
    while i < len(wave):
        ch = wave[i]
        if ch == "!":
            if i + 1 >= len(wave) or wave[i + 1] not in params:
                raise ScoreError(f"'!' must be followed by a parameter name in wave {wave!r}", pos, "E-NAMES")
            out.append(("p", wave[i + 1], True))
            i += 2
        elif ch in "01zx.":
            out.append(("c", ch))
            i += 1
        elif ch in params:
            out.append(("p", ch, False))
            i += 1
        else:
            raise ScoreError(f"bad character {ch!r} in wave string {wave!r} (not a level or a parameter)", pos,
                             "E-NAMES")
    return out


def expand_wave(wave: str, params: list[str], args: tuple, n: int, pos=None):
    """Per-segment drive values for one symbol instance: list of '0','1','z','x','.'; length n."""
    items = parse_wave(wave, params, pos)
    if len(items) == 1:
        items = items * n
    if len(items) != n:
        raise ScoreError(f"wave {wave!r} has {len(items)} characters; the beat has {n} segment(s)", pos, "E-FIT-SEG")
    out = []
    for it in items:
        if it[0] == "c":
            out.append(it[1])
        else:
            v = args[params.index(it[1])]
            out.append(str(v ^ 1 if it[2] else v))
    return out


def symbol_instances(score: Score):
    """[(SymbolDef, args tuple)] with every parameter expanded over {0, 1}."""
    out = []
    for s in score.symbols:
        for args in itertools.product((0, 1), repeat=len(s.params)):
            out.append((s, args))
    return out


def inst_name(s: SymbolDef, args: tuple) -> str:
    return f"{s.name}({','.join(map(str, args))})" if args else s.name


def sym_wires(sdef: SymbolDef):
    return [w for w, _, _ in sdef.waves]


def effective_clock(score: Score):
    return score.clock_for()


def resolve_time(tr: TimeRef, sdef: SymbolDef, clock: Clock, args, period: Fraction | None):
    """Sample point as a fraction of the beat."""
    if tr.kind == "frac":
        return tr.frac
    if tr.kind == "dur":
        return qty_cycles(tr.qty, period) / period
    # edge: the boundary where the wire makes that transition inside this symbol's wave
    b = boundaries(clock)
    n = len(b) - 1
    for w, wave, pos in sdef.waves:
        if w == tr.wire:
            segs = expand_wave(wave, sdef.params, args, n, pos)
            lv = []
            for c in segs:
                lv.append(lv[-1] if c == "." and lv else {"0": 0, "1": 1, "z": 1, "x": None, ".": None}[c])
            a, c2 = (0, 1) if tr.edge == "rise" else (1, 0)
            for j in range(1, n):
                if lv[j - 1] == a and lv[j] == c2:
                    return b[j]
            return Fraction(0) if lv[0] == c2 else None
    return None
