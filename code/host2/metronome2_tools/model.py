"""Assembled-program data model shared by the assembler, checker, image writer and disassembler (v2)."""
from __future__ import annotations

from dataclasses import dataclass, field

from ._md import M
from .encode import Insn, encode


class AsmError(Exception):
    def __init__(self, msg: str, line: int | None = None, file: str | None = None):
        self.msg, self.line, self.file = msg, line, file
        super().__init__(self.__str__())

    def __str__(self) -> str:
        loc = ""
        if self.file or self.line:
            loc = f"{self.file or '<src>'}:{self.line}: " if self.line else f"{self.file}: "
        return f"{loc}{self.msg}"


@dataclass
class AsmInsn:
    core: int
    addr: int
    insn: Insn
    line: int = 0
    text: str = ""

    @property
    def word(self) -> int:
        return encode(self.insn)

    @property
    def pause(self) -> bool:
        return self.insn.pause

    def enabled_moves(self):
        return [mv for mv in self.insn.moves if mv.guard != "never" and not (mv.src == "ZERO" and mv.dst == "NULL")]

    def edges(self) -> list:
        """[(successor address, extra cycles)] of this instruction.  A taken jump on a non-pausing instruction costs
        one idle cycle (SPEC v2 5); a pausing instruction ends the burst, its successors are resume points."""
        nxt = (self.addr + 1) % M.PROG_WORDS
        j = self.insn.jmode
        bubble = 0 if self.insn.pause else 1
        if j == "next":
            return [(nxt, 0)]
        if j == "always":
            return [(self.insn.imm, bubble)]
        out = [(self.insn.imm, bubble)]
        if nxt != self.insn.imm or bubble == 0:
            out.append((nxt, 0))
        return out

    def writes_sym(self) -> bool:
        return any(mv.dst in M.WRITE_GROUPS["L.SYM"] for mv in self.enabled_moves())

    def reads_input(self) -> bool:
        """Reads the line's snapshot-derived input: sources L.IN / L.CAP, or guards L.IN0 / L.IN1."""
        i = self.insn
        if any(mv.src in ("L.IN", "L.CAP") for mv in self.enabled_moves()):
            return True
        uses_cond = i.cond != "TRUE" and any(mv.guard in ("if", "ifnot") for mv in i.moves)
        if uses_cond and i.cond in ("L.IN0", "L.IN1"):
            return True
        return i.jmode in ("if", "ifnot") and i.jcond in ("L.IN0", "L.IN1")


@dataclass
class LineCfg:
    n: int
    inc: int = 0
    mod: int = 0
    taps: list = field(default_factory=lambda: [None, None, None])   # None = disabled (written as MOD)
    pre: int = 0
    wlo: int = 0
    whi: int = 0xFFFF
    wen: int = 0
    phase: int | None = None
    ctl: int = 0                    # initial CTL: bit 0 RUN, 1 ARM, 2 REN
    edge_pin: int = 15
    edge_pol: int = 0
    follow: int = 0
    t0_pin: int = 15
    t0_pol: int = 0
    t0src: int = 0
    snap: int = 0
    pina: int = 15
    pinb: int = 15
    lut0: int = 0
    lut1: int = 0
    hen: int = 0
    hpin: int = 15
    hlvl: int = 0
    htap: int = 3
    minperiod: int | None = None    # declared assumptions about a followed clock (check.py)
    minhalf: int | None = None
    line: int = 0                   # source line

    def tap(self, k: int) -> int:
        return self.mod if self.taps[k] is None else self.taps[k]

    def tap_enabled(self, k: int) -> bool:
        if k == 0 and self.t0src:
            return self.t0_pol != 0
        return self.taps[k] is not None and self.taps[k] < self.mod

    def phase_tap(self, k: int) -> bool:
        return self.tap_enabled(k) and not (k == 0 and self.t0src)


@dataclass
class ThreadCfg:
    n: int
    core: int = 0
    line_: int | None = None
    trigger: str = "NONE"
    watch: list = field(default_factory=lambda: [None, None])     # (guard name, label) per watcher
    start: str | None = None
    pc: int | None = None
    enable: bool = True
    line: int = 0                   # source line
    start_addr: int | None = None
    watch_addr: list = field(default_factory=lambda: [None, None])

    @property
    def bound_line(self) -> int:
        """Line the thread is bound to; defaults to the line of a Lg.* trigger, else 0."""
        if self.line_ is not None:
            return self.line_
        if self.trigger.startswith("L") and self.trigger[1].isdigit():
            return int(self.trigger[1])
        return 0

    @property
    def trigger_line(self) -> int | None:
        return int(self.trigger[1]) if self.trigger.startswith("L") and self.trigger[1].isdigit() else None


@dataclass
class OutCfg:
    n: int
    line_: int | None = None        # None = unbound (BOUND = 0)
    sel: tuple = (0, 1, 2)
    lut: int = 0
    oe: int = 0
    line: int = 0


@dataclass
class StreamCfg:
    n: int
    rx: int = 0
    msb: int = 0
    start: int = 0
    len: int = 0
    mark: int = 0
    line: int = 0


@dataclass
class Lfsr:
    n: int
    poly: int
    width: int = 32
    init: int = 0


@dataclass
class Program:
    clock_hz: float = 60e6
    code: dict = field(default_factory=lambda: {c: {} for c in range(M.N_CORES)})
    labels: dict = field(default_factory=dict)
    symbols: dict = field(default_factory=dict)
    lines: dict = field(default_factory=dict)
    threads: dict = field(default_factory=dict)
    outs: dict = field(default_factory=dict)
    streams: dict = field(default_factory=dict)
    lfsrs: dict = field(default_factory=dict)
    data: list = field(default_factory=list)
    irqen: int | None = None
    run: bool = True
    budgets: list = field(default_factory=list)
    warnings: list = field(default_factory=list)
    source_name: str = ""

    def words(self, core: int) -> dict:
        return {a: i.word for a, i in sorted(self.code[core].items())}

    def addr_name(self, core: int, addr: int) -> str:
        best = None
        for name, (c, a) in self.labels.items():
            if c == core and a <= addr and (best is None or a > best[1] or (a == best[1] and len(name) < len(best[0]))):
                best = (name, a)
        if best is None:
            return f"0x{addr:02X}"
        off = addr - best[1]
        return f"{best[0]}{'+%d' % off if off else ''}(0x{addr:02X})"
