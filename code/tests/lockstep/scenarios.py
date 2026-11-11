"""Lockstep scenarios: per-cycle pin stimulus for tt_um_brentius_metronome and the reference model.

The SPI encoder here is written from wiki/SPEC.md section 9 and is independent of the reference model's helpers.
Pins: ui[0]=SCK, ui[1]=CS_N, ui[2]=MOSI, ui[7:3] protocol inputs P8..P12; uio_in = P0..P7.
"""
from __future__ import annotations

import random
from dataclasses import dataclass, field
from typing import Callable

import machine as m
from encode import Insn, Move, encode

HALF = 8   # SCK half period in clocks (SPEC: SCK <= clk/16)


@dataclass
class Scenario:
    cycles: list[tuple[int, int, int]] = field(default_factory=list)   # (ui_in, uio_in, rst_n)
    compare_from: int = 2
    check: Callable | None = None
    reads: list[tuple[int, int]] = field(default_factory=list)          # (cycle index of first read bit, address)

    # --- low level -------------------------------------------------------------------------------------------
    def idle(self, n: int, ui_hi: int = 0, uio: int = 0, rst_n: int = 1):
        for _ in range(n):
            self.cycles.append(((ui_hi & 0xF8) | 0b010, uio & 0xFF, rst_n))   # CS_N high, SCK low

    def reset(self, n: int = 4):
        self.idle(n, rst_n=0)
        self.idle(4)

    def _spi(self, tx: list[int], ui_hi: int = 0, uio: int = 0) -> list[int]:
        """One CS-low transaction; returns the cycle index at which each byte's first SCK rise happens."""
        starts = []
        base = ui_hi & 0xF8
        for _ in range(HALF):                      # CS low, SCK low setup
            self.cycles.append((base | 0b000, uio, 1))
        for byte in tx:
            starts.append(len(self.cycles) + HALF)
            for k in range(7, -1, -1):
                mosi = (byte >> k) & 1
                for _ in range(HALF):
                    self.cycles.append((base | (mosi << 2) | 0b000, uio, 1))     # SCK low, data valid
                for _ in range(HALF):
                    self.cycles.append((base | (mosi << 2) | 0b001, uio, 1))     # SCK high (sampled on rise)
        for _ in range(HALF):
            self.cycles.append((base | 0b000, uio, 1))
        self.idle(2 * HALF, ui_hi, uio)
        return starts

    # --- host operations -------------------------------------------------------------------------------------
    def write(self, addr: int, data: bytes | list[int]):
        self._spi([0x02, addr >> 8, addr & 0xFF, *list(data)])

    def read(self, addr: int, n: int = 1):
        starts = self._spi([0x03, addr >> 8, addr & 0xFF] + [0] * n)
        for k in range(n):
            self.reads.append((starts[3 + k], addr + k))

    def load_program(self, core: int, words: list[int]):
        data = b"".join(w.to_bytes(8, "little") for w in words)
        self.write(m.HOST_MAP["PROG_BASE"] + core * 0x800, data)


def miso_bytes(trace, scen: Scenario, use_model: bool) -> dict[int, int]:
    """Decode read data from the MISO pin (uo_out bit 0) at the SCK rising edges of each read byte."""
    out = {}
    for start, addr in scen.reads:
        v = 0
        for k in range(8):
            t = start + k * 2 * HALF + 2          # a couple of cycles after the rise, MISO has been stable since the fall
            uo = trace[t][4][0] if use_model else trace[t][3][0]
            v = (v << 1) | (uo & 1)
        out[addr] = v
    return out


# ------------------------------------------------------------------------------------------------------------
def reg(base: str, idx: int, stride: int, off_name: str, table: dict) -> int:
    off = {n: o for o, (n, _) in table.items()}[off_name]
    return m.HOST_MAP[base] + idx * stride + off


def bg_reg(g, name):
    return reg("BG_BASE", g, 0x20, name, m.BG_REGS)


def eng_reg(e, name):
    return reg("ENG_BASE", e, 0x20, name, m.ENG_REGS)


def out_reg(o, name):
    return reg("OUT_BASE", o, 0x08, name, m.OUT_REGS)


def ctrl_reg(name):
    return reg("CTRL_BASE", 0, 0, name, m.CTRL_REGS)


def le16(v):
    return [v & 0xFF, (v >> 8) & 0xFF]


# ------------------------------------------------------------------------------------------------------------
def smoke() -> Scenario:
    s = Scenario()
    s.reset()
    s.idle(20)
    s.read(ctrl_reg("ID"))

    def check(trace):
        got = miso_bytes(trace, s, use_model=False)[ctrl_reg("ID")]
        assert got == 0xA0 | m.VERSION, f"ID read {got:#x}"
    s.check = check
    return s


def regs() -> Scenario:
    """Write registers and read them back over SPI: readable state registers return the value, write-only
    configuration registers (D14) read 0."""
    s = Scenario()
    s.reset()
    s.write(bg_reg(1, "INC"), le16(0x1234) + le16(0xBEEF))   # write-only
    s.write(bg_reg(1, "PHASE"), le16(0x0BCD) + [0b0100])      # PHASE + CTL (REN only, not running)
    s.write(eng_reg(3, "PC"), [0x5A, 0x07])                   # PC readable, CFG write-only
    s.write(out_reg(9, "LUT"), le16(0xC3A5))                  # write-only
    s.read(bg_reg(1, "INC"), 2)
    s.read(bg_reg(1, "PHASE"), 3)
    s.read(eng_reg(3, "PC"), 2)
    s.read(out_reg(9, "LUT"), 1)

    def check(trace):
        got = miso_bytes(trace, s, use_model=False)
        b, p, e = bg_reg(1, "INC"), bg_reg(1, "PHASE"), eng_reg(3, "PC")
        exp = {b: 0, b + 1: 0, p: 0xCD, p + 1: 0x0B, p + 2: 0b0100, e: 0x5A, e + 1: 0, out_reg(9, "LUT"): 0}
        assert got == exp, (got, exp)
    s.check = check
    return s


def blink() -> Scenario:
    """Engine 0 on BG0 (beat every 8 cycles) toggles its symbol each beat; O8 (uo_out[2]) shows symbol bit 0."""
    s = Scenario()
    s.reset()
    prog = [encode(Insn((Move("IMM", "ACC.XOR"),), imm=1)),
            encode(Insn((Move("ACC", "E.SYM"),), jmode="always", imm=0, pause=True))]
    s.load_program(0, prog)
    s.write(bg_reg(0, "INC"), le16(1) + le16(8))
    s.write(eng_reg(0, "CFG"), [0b0001])                       # EN, core 0, BG 0
    s.write(eng_reg(0, "TRIG"), [m.TRIG_ID["BG0.BEAT"]])
    s.write(out_reg(8, "ENG"), [0])
    s.write(out_reg(8, "LUT"), le16(0xAAAA))                  # level = sym bit 0 for every segment
    s.write(bg_reg(0, "CTL"), [0b0001])                        # RUN
    s.write(ctrl_reg("RUN"), [1])
    s.idle(400)

    def check(trace):
        lv = [tr[3][0] >> 2 & 1 for tr in trace[-300:]]
        edges = sum(1 for a, b in zip(lv, lv[1:]) if a != b)
        assert 30 <= edges <= 40, f"expected a toggle every 8 cycles, saw {edges} edges in 300 cycles"
    s.check = check
    return s


def random_program(seed: int, words: int = 24, run_cycles: int = 3000) -> Scenario:
    """Random configuration, random programs on both cores, random pin stimulus, then read back state over SPI."""
    rng = random.Random(seed)
    s = Scenario()
    s.reset()
    srcs = [p.name for p in m.SRC]
    dsts = [p.name for p in m.DST]
    conds = [p.name for p in m.GUARD_CONDS]
    for core in range(m.N_CORES):
        prog = []
        for _ in range(words):
            mv = tuple(Move(rng.choice(srcs), rng.choice(dsts), rng.choice(["always", "if", "ifnot", "never"]))
                       for _ in range(rng.randint(0, 3)))
            jm = rng.choice(["next", "next", "always", "if", "ifnot"])
            if len(prog) == words - 1:
                jm = "always"     # never fall off the loaded words: unloaded program SRAM is undefined on silicon
            prog.append(encode(Insn(mv, rng.choice(conds), jm, rng.randrange(words), rng.random() < 0.35)))
        s.load_program(core, prog)
    for g in range(m.N_BEATGENS):
        mod = rng.randint(4, 40)
        taps = sorted(rng.randrange(mod + 2) for _ in range(3))
        cfg = le16(rng.randint(1, 3)) + le16(mod)
        for t in taps:
            cfg += le16(t)
        cfg += le16(rng.randrange(mod)) + le16(rng.randrange(mod)) + le16(rng.randrange(mod)) + le16(0)
        cfg += [rng.choice([0b0001, 0b0101, 0b1101, 0b0010]), rng.randrange(13) | (rng.randrange(4) << 4)]
        s.write(bg_reg(g, "INC"), cfg)
    for e in range(m.N_ENGINES):
        cfg = [1 | (rng.randrange(m.N_CORES) << 1) | (rng.randrange(m.N_BEATGENS) << 2)]
        trig = rng.choice([n for n in m.TRIGGERS if n not in ("NONE",)])
        body = [rng.randrange(words), *cfg, m.TRIG_ID[trig], rng.randrange(256),
                *le16(rng.randrange(1 << 16)), *le16(rng.randrange(1 << 16)),
                rng.choice([0, rng.randrange(len(conds))]), rng.randrange(words),
                rng.choice([0, rng.randrange(len(conds))]), rng.randrange(words)]
        s.write(eng_reg(e, "PC"), body)
    for o in range(m.N_OUT_PINS):
        s.write(out_reg(o, "ENG"), [rng.randrange(8)])
        s.write(out_reg(o, "LUT"), le16(rng.randrange(1 << 16)) + le16(rng.randrange(1 << 16)))
    for k in range(m.N_LFSRS):
        s.write(m.HOST_MAP["UNIT_BASE"] + 8 * k, list(rng.randbytes(4)))
    s.write(ctrl_reg("IRQEN"), [3])
    s.write(ctrl_reg("RUN"), [1])
    uio, hi = 0, 0
    for t in range(run_cycles):
        if rng.random() < 0.05:
            uio ^= 1 << rng.randrange(8)
        if rng.random() < 0.02:
            hi ^= 1 << rng.randrange(3, 8)
        s.idle(1, ui_hi=hi, uio=uio)
    s.write(ctrl_reg("RUN"), [0])
    s.idle(200)
    for e in range(m.N_ENGINES):
        s.read(eng_reg(e, "PC"), 1)
        s.read(eng_reg(e, "SYM"), 2)
    s.read(ctrl_reg("STICKY"), 1)
    for g in range(m.N_BEATGENS):
        s.read(bg_reg(g, "PHASE"), 3)
    return s


def build(name: str) -> Scenario:
    if name.startswith("random"):
        return random_program(int(name.split("_")[1]) if "_" in name else 1)
    if name.startswith("proto_"):
        import proto_scenarios
        return getattr(proto_scenarios, name[len("proto_"):])()
    return {"smoke": smoke, "regs": regs, "blink": blink}[name]()
