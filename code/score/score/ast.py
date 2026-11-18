"""AST for the score language (wiki/SPEC_V2_SCORE.md part A)."""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Optional

Pos = tuple  # (line, col), 1-based


class ScoreError(Exception):
    """Syntax or static error with a position and (for static errors) a diagnostic code."""

    def __init__(self, msg: str, pos: Pos | None = None, code: str = "E-SYNTAX"):
        self.msg, self.pos, self.code = msg, pos, code
        where = f"{pos[0]}:{pos[1]}: " if pos else ""
        super().__init__(f"{where}{code}: {msg}")


@dataclass
class Diag:
    code: str
    msg: str
    pos: Pos | None = None

    def __str__(self):
        where = f"{self.pos[0]}:{self.pos[1]}: " if self.pos else ""
        return f"{where}{self.code}: {self.msg}"


# ---- expressions ---------------------------------------------------------------------------------------------
@dataclass
class Num:
    value: int
    pos: Pos = None


@dataclass
class Name:
    name: str
    pos: Pos = None


@dataclass
class Un:
    op: str
    a: object
    pos: Pos = None


@dataclass
class Bin:
    op: str
    a: object
    b: object
    pos: Pos = None


@dataclass
class Cond:
    c: object
    a: object
    b: object
    pos: Pos = None


@dataclass
class Qty:
    value: Fraction
    unit: str | None  # Hz kHz MHz ns us ms s cycles beats % or None
    pos: Pos = None


# ---- declarations --------------------------------------------------------------------------------------------
@dataclass
class Wire:
    name: str
    dir: str            # out | in | shared
    drive: str          # push-pull | open-drain
    idle: str | None    # low | high | released | None
    by: str | None
    pos: Pos = None
    mirror_of: str | None = None   # set for mirror wires


@dataclass
class RoleClock:
    role: str
    mode: str               # generated | started | recovered | follow
    wire: str | None = None
    edge: str | None = None          # rise | fall (started/follow)
    win: tuple | None = None         # (Fraction, Fraction) fractions of the beat (recovered)
    cap_wire: str | None = None
    cap_edge: str | None = None
    stretch: str | None = None
    pos: Pos = None


@dataclass
class Clock:
    rate: Fraction | None        # Hz; None = free
    roles: dict = field(default_factory=dict)   # role -> RoleClock
    split: list = field(default_factory=lambda: [Fraction(1, 2)])
    tolerance: Fraction = Fraction(2, 100)
    pos: Pos = None


@dataclass
class TimeRef:
    kind: str                    # frac | edge | dur
    frac: Fraction | None = None
    wire: str | None = None
    edge: str | None = None
    qty: Qty | None = None
    pos: Pos = None


@dataclass
class SymbolDef:
    name: str
    params: list
    waves: list                  # [(wire, wavestring)]
    samples: list                # [(wire|None, TimeRef)]
    pos: Pos = None


@dataclass
class Recog:
    names: list
    kind: str                    # edge_while | no_edge | level_for | edge
    wire: str | None = None
    edge: str | None = None      # rises | falls | low | high
    while_wire: str | None = None
    while_level: str | None = None
    qty: Qty | None = None
    pos: Pos = None


@dataclass
class Bits:
    order: str = "msb"
    differential: Optional[int] = None       # data value that causes a level change
    stuff: Optional[tuple] = None            # (bit|None, N, kind)
    invert: bool = False
    pos: Pos = None


@dataclass
class CrcDecl:
    name: str
    width: int
    poly: int
    init: int
    refin: bool
    refout: bool
    xorout: int
    pos: Pos = None


@dataclass
class ParamDecl:
    name: str
    type: str
    default: object
    for_role: str | None
    pos: Pos = None


@dataclass
class EnumDecl:
    """`enum NAME : uN` with `MEMBER = VALUE` lines (part A 18.3). Members are global integer constants."""
    name: str
    width: int
    members: dict            # member -> int
    pos: Pos = None


@dataclass
class StateDecl:
    """`state` line `NAME : uN = INIT` (part A 18.3): a value both roles keep across frames."""
    name: str
    width: int
    init: int
    pos: Pos = None


@dataclass
class TEvent:
    """One side of a timing constraint: a wire edge (optionally qualified by another wire's level) or a
    recognised event (part A 18.1)."""
    kind: str                    # edge | event
    wire: str | None = None
    edge: str | None = None      # rise | fall | change
    when_wire: str | None = None
    when_level: str | None = None   # high | low
    event: str | None = None
    pos: Pos = None


@dataclass
class Constraint:
    """`constrain` line `NAME  A -> B  >=|<=  QTY` (part A 18.1)."""
    name: str
    a: TEvent
    b: TEvent
    op: str                      # >= | <=
    qty: Qty
    pos: Pos = None


@dataclass
class AbortRule:
    event: str
    in_prod: str | None
    target: str
    pos: Pos = None


# ---- grammar -------------------------------------------------------------------------------------------------
@dataclass
class Type:
    kind: str                    # bit | u | s | bytes | crc | parity
    width: int = 0
    order: str | None = None
    length: object = None        # bytes[N]
    until: str | None = None     # bytes until X
    crc: str | None = None
    parity: str | None = None
    first: str | None = None
    last: str | None = None
    enum: str | None = None      # field typed by an enum: kind "u", width from the enum (18.3)


@dataclass
class Field:
    name: str | None
    type: Type
    by: str | None = None
    value: object = None
    expect: object = None
    hidden: bool = False
    notify: bool = False
    asm: str | None = None
    model: str | None = None
    pos: Pos = None


@dataclass
class ConstBytes:
    data: bytes
    pos: Pos = None


@dataclass
class ConstBits:
    bits: str
    pos: Pos = None


@dataclass
class Gap:
    qty: Qty
    pos: Pos = None


@dataclass
class Turnaround:
    beats: int
    pos: Pos = None


@dataclass
class Ref:
    """A bare name in the grammar: symbol, recognised event or production call (resolved by Score.kind_of)."""
    name: str
    args: list
    by: str | None = None
    pos: Pos = None


@dataclass
class Seq:
    items: list
    pos: Pos = None


@dataclass
class Choice:
    alts: list
    pos: Pos = None


@dataclass
class Dup:
    a: object
    b: object
    pos: Pos = None


@dataclass
class Rep:
    node: object
    kind: str                    # star plus opt times until while
    arg: object = None           # count expr (times) or condition (until/while)
    pos: Pos = None


@dataclass
class If:
    node: object
    cond: object
    pos: Pos = None


@dataclass
class Within:
    node: object
    qty: Qty
    pos: Pos = None


@dataclass
class Switch:
    expr: object
    arms: list                   # [(int, node)]
    other: object = None
    pos: Pos = None


@dataclass
class Every:
    qty: Qty
    node: object
    pos: Pos = None


@dataclass
class Retry:
    count: int
    node: object
    event: str
    pos: Pos = None


@dataclass
class Assign:
    """`NAME <- EXPR` in the grammar: update a state value (18.3). Both roles execute it at the same point."""
    name: str
    expr: object
    pos: Pos = None


@dataclass
class AsmBlock:
    raw: str
    contract: dict = field(default_factory=dict)
    pos: Pos = None


@dataclass
class Prod:
    name: str
    params: list                 # each: ("id", name) | ("lit", int)
    body: object
    pos: Pos = None


@dataclass
class Group:
    name: str
    wires: list
    clock: Clock | None
    pos: Pos = None


@dataclass
class Score:
    name: str
    version: int | None
    roles: tuple
    uses: list
    wires: list
    clock: Clock | None
    groups: list
    symbols: list
    recognise: list
    bits: Bits
    crcs: dict
    prods: list
    aborts: list
    params: list
    source: str = ""
    arbitrates: list = field(default_factory=list)
    # part A 18 (language extensions); all optional, so older code that builds a Score keeps working
    constraints: list = field(default_factory=list)     # [Constraint]
    enums: dict = field(default_factory=dict)           # name -> EnumDecl
    states: list = field(default_factory=list)          # [StateDecl]
    imports: dict = field(default_factory=dict)         # alias -> library score name (`use LIB as ALIAS`)
    over: tuple | None = None                           # (alias, production) for `protocol P over ALIAS.PROD`

    # -- lookups --
    def consts(self) -> dict:
        """Enum members as integer constants."""
        out = {}
        for e in self.enums.values():
            out.update(e.members)
        return out

    def state(self, name):
        for s in self.states:
            if s.name == name:
                return s
        return None

    def wire(self, name):
        for w in self.all_wires():
            if w.name == name:
                return w
        return None

    def all_wires(self):
        out = list(self.wires)
        for g in self.groups:
            out += g.wires
        return out

    def symbol(self, name):
        for s in self.symbols:
            if s.name == name:
                return s
        return None

    def event(self, name):
        for r in self.recognise:
            if name in r.names:
                return r
        return None

    def prods_named(self, name):
        return [p for p in self.prods if p.name == name]

    def param(self, name):
        for p in self.params:
            if p.name == name:
                return p
        return None

    def other_role(self, role):
        return self.roles[1] if role == self.roles[0] else self.roles[0]

    def wire_owners(self, w):
        """Roles that may drive wire w."""
        if w.mirror_of:
            return self.wire_owners(self.wire(w.mirror_of))
        if w.dir == "shared":
            return set(self.roles)
        by = w.by or self.roles[0]
        return {by} if w.dir == "out" else {self.other_role(by)}

    def clock_for(self, wire_names=None):
        """The clock of the (only) group; multi-group scores are not supported by the codec."""
        if self.clock:
            return self.clock
        return self.groups[0].clock if self.groups else None
