"""Flatten a score's grammar into a frame of steps, one role-independent list (spec 7, 10.1).

The compiler handles the shapes the machine runs natively: a frame production repeated by `*`, made of symbol
terminals, constant bytes, fixed-width fields, `bytes` fields, a crc, gaps and a `||` pair.  Anything else is rejected
with E-UNSUPPORTED naming the construct, never compiled into something that silently misbehaves.
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from fractions import Fraction

from . import _paths  # noqa: F401
from score.analysis import fields_in, kind_of
from score.ast import (AsmBlock, Assign, Choice, ConstBits, ConstBytes, Dup, Every, Field, Gap, If, Num, Ref, Rep, Retry, Seq,
                       Switch, Turnaround, Within)
from score.model import qty_cycles

from .plan import CompileError


@dataclass
class Step:
    kind: str                # sym | const | field | gap | dup | star | event | every
    owner: str | None = None
    name: str | None = None            # symbol name / field name / event name
    args: tuple = ()
    count: int = 1                     # sym: consecutive beats
    bits: list = field(default_factory=list)       # const bits: bits in transmit order (before coding)
    data: bytes = b""                  # const bytes
    f: Field | None = None             # field node
    qty: object = None                 # gap
    body: list = field(default_factory=list)       # star / every / dup sides ([a_steps, b_steps])
    sides: tuple = ()
    pos: tuple | None = None

    def describe(self) -> str:
        if self.kind == "sym":
            return f"{self.name}{'(' + ','.join(map(str, self.args)) + ')' if self.args else ''}" + \
                   (f" x{self.count}" if self.count > 1 else "")
        if self.kind == "const":
            return f"const {len(self.data) * 8 + len(self.bits)} bits"
        if self.kind == "field":
            t = self.f.type
            return f"{self.f.name or t.kind}:{t.kind}{t.width or ''}"
        return self.kind


@dataclass
class FrameShape:
    frame: list              # steps of one frame
    periodic: list           # [(Every qty, steps)] before the frame loop
    start_name: str
    loop_kind: str = "star"


def _unsup(what, pos=None):
    where = f"{pos[0]}:{pos[1]}: " if pos else ""
    raise CompileError("E-UNSUPPORTED", f"{where}grammar: '{what}' is not compiled yet (frame shapes handled: symbol "
                                        f"terminals, const, fixed-width fields, bytes, crc, gap, || pairs, star loops)")


def _clone(st: Step) -> Step:
    """A copy of a step that shares no mutable Step state (counts, nested lists) with the original."""
    import copy
    c = copy.copy(st)
    c.body = [_clone(b) for b in st.body]
    c.sides = tuple([_clone(b) for b in side] if isinstance(side, list) else side for side in st.sides)
    c.bits = list(st.bits)
    return c


class Flattener:
    def __init__(self, score):
        self.s = score
        self.stack: list[str] = []

    def walk(self, n, owner) -> list[Step]:
        S = self.s
        if isinstance(n, Seq):
            out = []
            for it in n.items:
                out += self.walk(it, owner)
            return out
        if isinstance(n, Field):
            return [Step("field", n.by or owner, n.name, f=n, pos=n.pos)]
        if isinstance(n, ConstBytes):
            return [Step("const", owner, data=bytes(n.data), pos=n.pos, name="const")]
        if isinstance(n, ConstBits):
            return [Step("const", owner, bits=[int(c) for c in n.bits], pos=n.pos, name="const bits")]
        if isinstance(n, Gap):
            return [Step("gap", owner, qty=n.qty, pos=n.pos)]
        if isinstance(n, Dup):
            return [Step("dup", owner, sides=(self.walk(n.a, owner), self.walk(n.b, owner)), pos=n.pos)]
        if isinstance(n, Rep):
            if n.kind == "times" and isinstance(n.arg, Num):
                one = self.walk(n.node, owner)
                return [_clone(st) for _ in range(n.arg.value) for st in one]    # copies: merge_syms mutates counts
            if n.kind in ("star", "plus"):
                return [Step("star", owner, body=self.walk(n.node, owner), pos=n.pos, name=n.kind)]
            _unsup(f"repeat '{n.kind}' with a computed condition", n.pos)
        if isinstance(n, Every):
            return [Step("every", owner, qty=n.qty, body=self.walk(n.node, owner), pos=n.pos)]
        if isinstance(n, Ref):
            k = kind_of(S, n.name)
            o = n.by or owner
            if k == "sym":
                args = tuple(a.value if isinstance(a, Num) else None for a in n.args)
                if any(a is None for a in args):
                    _unsup(f"symbol '{n.name}' with a computed argument", n.pos)
                return [Step("sym", o, n.name, args, pos=n.pos)]
            if k == "event":
                return [Step("event", o, n.name, pos=n.pos)]
            ps = S.prods_named(n.name)
            if len(ps) != 1 or ps[0].params:
                _unsup(f"production '{n.name}' with parameters or several variants", n.pos)
            if n.name in self.stack:
                _unsup(f"recursive production '{n.name}'", n.pos)
            self.stack.append(n.name)
            out = self.walk(ps[0].body, o)
            self.stack.pop()
            return out
        names = {Choice: "choice '|'", If: "'if'", Switch: "switch", Retry: "retry", Within: "'within'",
                 Turnaround: "turnaround", AsmBlock: "inline assembly", Assign: "state update '<-' (part A 18.3)"}
        _unsup(names.get(type(n), type(n).__name__), getattr(n, "pos", None))


def merge_syms(steps: list[Step]) -> list[Step]:
    out: list[Step] = []
    for s in steps:
        if out and s.kind == "sym" and out[-1].kind == "sym" and (s.name, s.args, s.owner) == (
                out[-1].name, out[-1].args, out[-1].owner):
            out[-1].count += s.count
        else:
            out.append(s)
    return out


def frame_shape(score) -> FrameShape:
    fl = Flattener(score)
    start = score.prods[0]
    fl.stack.append(start.name)
    top = fl.walk(start.body, score.roles[0])
    periodic, frame, loop = [], None, None
    for s in top:
        if s.kind == "every":
            periodic.append((s.qty, merge_syms(s.body)))
        elif s.kind == "star" and frame is None:
            frame = merge_syms(s.body)
            loop = s.name
        else:
            _unsup(f"top-level {s.kind} outside the frame loop", s.pos)
    if frame is None:
        # a start production that is one frame, not repeated
        frame, loop = merge_syms(top), "once"
    return FrameShape(frame, periodic, start.name, loop)


# ---- helpers on steps --------------------------------------------------------------------------------------------
def field_bits(step: Step) -> int | None:
    t = step.f.type
    if t.kind in ("bit", "parity"):
        return 1
    if t.kind in ("u", "s"):
        return t.width
    if t.kind == "bytes" and t.length is not None and isinstance(t.length, Num):
        return 8 * t.length.value
    return None


def gap_beats(step: Step, period: Fraction) -> int:
    cyc = qty_cycles(step.qty, period)
    return max(0, int(math.ceil(cyc / period)))


def crc_range(frame: list[Step], f: Field) -> set[str]:
    """Names of the fields a crc/parity field covers (F1..F2 in field order)."""
    names = [s.f.name for s in frame if s.kind == "field" and s.f.name]
    a, b = f.type.first, f.type.last
    if b is None:                       # open range F1..* (part A 18.2): through the field just before the crc
        before = []
        for s in frame:
            if s.kind == "field" and s.f is f:
                break
            if s.kind == "field" and s.f.name:
                before.append(s.f.name)
        return set(before[before.index(a):]) if a in before else set()
    if a in names and b in names:
        return set(names[names.index(a):names.index(b) + 1])
    return set()
