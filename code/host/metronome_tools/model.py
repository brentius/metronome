"""Assembled-program data model shared by the assembler, checker, image writer and disassembler."""
from __future__ import annotations

from dataclasses import dataclass, field

from ._md import M, Insn, encode


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

    def successors(self) -> list[int]:
        """Addresses the next instruction of the same burst may have (a pause's successors are resume points)."""
        nxt = (self.addr + 1) % M.PROG_WORDS
        j = self.insn.jmode
        if j == "next":
            return [nxt]
        if j == "always":
            return [self.insn.imm]
        out = [self.insn.imm, nxt]
        return list(dict.fromkeys(out))

    def writes_sym(self) -> bool:
        return any(mv.dst == "E.SYM" and mv.guard != "never" for mv in self.insn.moves)


@dataclass
class BeatGen:
    n: int
    inc: int = 0
    mod: int = 0
    taps: list = field(default_factory=lambda: [None, None, None])   # None = disabled (written as MOD)
    pre: int = 0
    wlo: int = 0
    whi: int = 0xFFFF
    phase: int | None = None
    ctl: int = 0
    edge_pin: int = 15
    edge_pol: int = 0
    line: int = 0

    def tap(self, k: int) -> int:
        return self.mod if self.taps[k] is None else self.taps[k]


@dataclass
class Engine:
    n: int
    core: int = 0
    bg: int | None = None
    trigger: str = "NONE"
    pina: int = 15
    pinb: int = 15
    lut0: int = 0
    lut1: int = 0
    watch: list = field(default_factory=lambda: [None, None])     # (guard name, label) per watcher
    start: str | None = None
    pc: int | None = None
    enable: bool = True
    line: int = 0
    # resolved
    start_addr: int | None = None
    watch_addr: list = field(default_factory=lambda: [None, None])

    @property
    def bg_eff(self) -> int:
        if self.bg is not None:
            return self.bg
        if self.trigger.startswith("BG"):
            return int(self.trigger[2])
        return 0


@dataclass
class OutCell:
    n: int
    eng: int = 7            # 6, 7 = unbound
    lut: int = 0
    oe: int = 0
    line: int = 0


@dataclass
class Lfsr:
    n: int
    poly: int
    width: int = 32
    init: int = 0           # register-form (already reflected) initial state


@dataclass
class Program:
    clock_hz: float = 60e6
    code: dict = field(default_factory=lambda: {c: {} for c in range(M.N_CORES)})   # core -> addr -> AsmInsn
    labels: dict = field(default_factory=dict)        # name -> (core, addr)
    symbols: dict = field(default_factory=dict)       # .equ and derived constants
    bgs: dict = field(default_factory=dict)
    engines: dict = field(default_factory=dict)
    outs: dict = field(default_factory=dict)
    lfsrs: dict = field(default_factory=dict)
    data: list = field(default_factory=list)          # (addr, bytes)
    irqen: int | None = None
    run: bool = True
    budgets: list = field(default_factory=list)       # (engine, kind 'cycles'|'insns', value, line)
    warnings: list = field(default_factory=list)
    source_name: str = ""

    def words(self, core: int) -> dict[int, int]:
        return {a: i.word for a, i in sorted(self.code[core].items())}

    def addr_name(self, core: int, addr: int) -> str:
        """Human name of an address: nearest preceding label (plus offset) and the hex address."""
        best = None
        for name, (c, a) in self.labels.items():
            if c == core and a <= addr and (best is None or a > best[1] or (a == best[1] and len(name) < len(best[0]))):
                best = (name, a)
        if best is None:
            return f"0x{addr:02X}"
        off = addr - best[1]
        return f"{best[0]}{'+%d' % off if off else ''}(0x{addr:02X})"
