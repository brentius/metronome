"""Compilation context shared by the role templates, and the configuration blocks every template emits."""
from __future__ import annotations

from dataclasses import dataclass, field

from score.crc import STD

from .emit import Builder
from .plan import ClockPlan, CompileError, RxPlan, Tap, TxPlan, pin_tables

# data RAM layout (SPEC B 6.2: 2,048 bytes): host transmit region, host receive region, compiled constants
TX_BASE, RX_BASE, CONST_BASE = 0x000, 0x400, 0x7E0


@dataclass
class Ctx:
    score: object
    role: str
    frame: list
    shape: object
    clk: ClockPlan
    taps: list
    txp: TxPlan | None
    rxp: RxPlan | None
    slots: dict
    bind: dict
    b: Builder
    order: str = "msb"
    opts: dict = field(default_factory=dict)
    notes: list = field(default_factory=list)
    host: dict = field(default_factory=lambda: {"mailbox_in": [], "mailbox_out": [], "tx_stream": None,
                                                "rx_stream": None, "params": {}})
    init_moves: list = field(default_factory=list)     # one-time setup moves, executed by the init thread
    states: list = field(default_factory=list)         # (core, label, description, instructions) for the report

    def crc_decl(self, name):
        c = self.score.crcs.get(name) or STD.get(name)
        if c is None:
            raise CompileError("E-NAMES", f"unknown crc '{name}'")
        return c

    def out_pin(self, wire) -> int:
        o = self.bind.get(wire, (None, None))[1]
        if o is None:
            raise CompileError("E-BIND", f"wire '{wire}' is driven by {self.role} and needs an output pin O<k>")
        return o

    @property
    def msb(self) -> bool:
        return self.order == "msb"

    def tap_text(self):
        ts = ["-", "-", "-"]
        for t in self.taps:
            ts[t.idx] = str(t.T)
        return " ".join(ts)

    def tap_of(self, wire, frac):
        return next(t for t in self.taps if t.frac == frac)


def emit_out_pins(ctx: Ctx, line: int):
    for w in ctx.txp.wires:
        o = ctx.out_pin(w)
        lut, oe = pin_tables(ctx.score, ctx.txp, w, o < 8)
        sel = ctx.txp.sel[w]
        lines = [f"line {line}", f"sel {sel[0]} {sel[1]} {sel[2]}", f"lutraw 0x{lut:08X}"]
        if o < 8:
            lines.append(f"oeraw 0x{oe:08X}")
        ctx.b.block(f".out O{o}                        ; wire '{w}'", lines)


def emit_threads(ctx: Ctx, threads: list):
    """threads: [(n, core, line, trigger, start_label)]"""
    for n, core, line, trig, start in threads:
        ctx.b.block(f".thread {n}", [f"core {core}", f"line {line}", f"trigger {trig}", f"start {start}"])


def emit_init_thread(ctx: Ctx, tn: int, core: int = 1, line: int = 0):
    """One-time setup (shifter lengths, LFSR initial values) as a thread that stops itself."""
    if not ctx.init_moves:
        return False
    ctx.b.block(f".thread {tn}", [f"core {core}", f"line {line}", "trigger ALWAYS", "start init"])
    c = ctx.b.cores[core]
    c.label("init")
    # one move per instruction: moves target different groups, but immediates differ; keep it simple and obvious
    for mv in ctx.init_moves:
        c.i([mv])
    c.i(["ZERO -> T.STOP"], pause=True, goto="init")
    return True
