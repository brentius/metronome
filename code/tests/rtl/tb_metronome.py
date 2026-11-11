"""Directed cocotb tests for tt_um_metronome through the Tiny Tapeout pins (wiki/SPEC.md).

Sampling convention: the monitor records every value at the falling edge in the middle of cycle t (registers hold
their cycle-t value and combinational nets have settled), so "cycle t" matches SPEC 1. Inputs are changed on falling
edges after the sample, so a pin change made in cycle t is first seen by the synchroniser at the end of cycle t. The host link is driven as an SPI controller at SCK = clk/16 (SPEC 9).
"""
from __future__ import annotations

import sys
import zlib
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "code" / "md"))
import machine as m  # noqa: E402
from encode import Insn, Move, encode  # noqa: E402

SCK, CS_N, MOSI = 0, 1, 2
HALF = 8  # SCK half period in clk cycles (clk/16)


def _inv(regs):
    return {name: off for off, (name, _n) in regs.items()}


BG = _inv(m.BG_REGS)
ENG = _inv(m.ENG_REGS)
OUT = _inv(m.OUT_REGS)
CTRL = _inv(m.CTRL_REGS)
HM = m.HOST_MAP


def a_bg(g, name):
    return HM["BG_BASE"] + 0x20 * g + BG[name]


def a_eng(e, name):
    return HM["ENG_BASE"] + 0x20 * e + ENG[name]


def a_out(o, name):
    return HM["OUT_BASE"] + 0x08 * o + OUT[name]


def a_ctrl(name):
    return HM["CTRL_BASE"] + CTRL[name]


def le16(v):
    return [v & 0xFF, (v >> 8) & 0xFF]


class TB:
    def __init__(self, dut):
        self.dut = dut
        self.ui = 1 << CS_N
        self.uio = 0
        self.t = 0
        self.log = None          # list of per-cycle samples while recording
        self.probes = {}

    async def start(self):
        cocotb.start_soon(Clock(self.dut.clk, 10, unit="ns").start())
        cocotb.start_soon(self._monitor())
        self.dut.ena.value = 1
        self.dut.ui_in.value = self.ui
        self.dut.uio_in.value = 0
        self.dut.rst_n.value = 0
        await self.cycles(5)
        self.dut.rst_n.value = 1
        await self.cycles(5)

    async def _monitor(self):
        while True:
            await FallingEdge(self.dut.clk)
            if self.log is not None:
                s = {"t": self.t, "uo": int(self.dut.uo_out.value), "uio": int(self.dut.uio_out.value),
                     "oe": int(self.dut.uio_oe.value), "h_we": int(self.dut.h_we.value),
                     "h_waddr": int(self.dut.h_waddr.value)}
                for k, h in self.probes.items():
                    s[k] = int(h.value)
                self.log.append(s)
            self.t += 1

    async def cycles(self, n):
        for _ in range(n):
            await FallingEdge(self.dut.clk)

    def _drive(self):
        self.dut.ui_in.value = self.ui

    def _set(self, bit, v):
        self.ui = (self.ui & ~(1 << bit)) | ((v & 1) << bit)

    async def spi(self, tx):
        rx = []
        await FallingEdge(self.dut.clk)
        self._set(SCK, 0)
        self._set(CS_N, 0)
        self._drive()
        await self.cycles(HALF)
        for b in tx:
            r = 0
            for i in range(7, -1, -1):
                self._set(MOSI, (b >> i) & 1)
                self._set(SCK, 0)
                self._drive()
                await self.cycles(HALF)
                r = (r << 1) | (int(self.dut.uo_out.value) & 1)     # sample MISO before the rising edge
                self._set(SCK, 1)
                self._drive()
                await self.cycles(HALF)
            rx.append(r)
        self._set(SCK, 0)
        self._drive()
        await self.cycles(HALF)
        self._set(CS_N, 1)
        self._drive()
        await self.cycles(2 * HALF)
        return rx

    async def write(self, addr, data):
        await self.spi([0x02, addr >> 8, addr & 0xFF] + list(data))

    async def read(self, addr, n=1):
        rx = await self.spi([0x03, addr >> 8, addr & 0xFF] + [0] * n)
        return rx[3:]

    async def load(self, core, words, base=0):
        data = []
        for w in words:
            data += list(int(w).to_bytes(8, "little"))
        await self.write(HM["PROG_BASE"] + core * m.PROG_WORDS * 8 + base * 8, data)

    async def engine(self, e, *, en=1, core=0, bg=0, trig="NONE", pc=0, pins=0):
        await self.write(a_eng(e, "PC"), [pc, en | (core << 1) | (bg << 2), m.TRIGGERS.index(trig), pins])


def I(*moves, cond="TRUE", jmode="next", imm=0, pause=False):
    return encode(Insn(tuple(Move(*mv) for mv in moves), cond, jmode, imm, pause))


async def _round_robin_fairness(dut, core):
    """Two recurring peers must not starve a doorbell engine (seven-cycle checker bound)."""
    tb = TB(dut)
    await tb.start()
    await tb.load(core, [I(), I(pause=True, jmode="always", imm=0),
                         I(), I(pause=True, jmode="always", imm=2),
                         I(("IMM", "HOST.OUT"), imm=0xA5),
                         I(pause=True, jmode="always", imm=4)])
    for engine, pc, trig in ((0, 0, "ALWAYS"), (1, 2, "ALWAYS"), (2, 4, "NONE")):
        await tb.engine(engine, core=core, pc=pc, trig=trig)
    await tb.write(a_ctrl("RUN"), [1])
    tb.probes = {"doorbell": dut.doorbell, "ho_we": dut.ho_we, "ho_d": dut.ho_d,
                 "pause": getattr(dut, f"c{core}_pause"), "xe": getattr(dut, f"c{core}_xe")}
    tb.log = []
    await tb.write(a_ctrl("DOORBELL"), [4])
    await tb.cycles(20)
    trigger = next(row["t"] for row in tb.log if row["doorbell"] & 4)
    writes = [row for row in tb.log if row["ho_we"]]
    assert writes, f"core {core}: ready engine 2 was starved by recurring engines 0 and 1"
    assert writes[0]["ho_d"] == 0xA5
    assert 2 <= writes[0]["t"] - trigger <= 7, (trigger, writes[0])
    completed = [row for row in tb.log if row["pause"] and row["xe"] == 2 and row["t"] >= trigger]
    assert completed and completed[0]["t"] - trigger <= 7, (trigger, completed)
    dut._log.info(f"core {core}: doorbell to last instruction {completed[0]['t'] - trigger} cycles (bound 7)")
    assert await tb.read(a_ctrl("HOSTOUT")) == [0xA5]


@cocotb.test()
async def test_round_robin_fairness_core0(dut):
    await _round_robin_fairness(dut, 0)


@cocotb.test()
async def test_round_robin_fairness_core1(dut):
    await _round_robin_fairness(dut, 1)


# ------------------------------------------------------------------------------------------------------------------
@cocotb.test()
async def test_host_registers(dut):
    """SPI register access: readable registers read back (BG PHASE/CTL, ENG PC/SYM/STAT, CTRL); configuration
    registers are write-only and read 0 (D14); ID, unmapped and program-memory reads; ignored commands."""
    tb = TB(dut)
    await tb.start()
    assert await tb.read(a_ctrl("ID")) == [0xA0 | m.VERSION]
    # write-only configuration (D14): multi-byte auto-increment writes, reads return 0
    vals = [0x34, 0x12, 0x78, 0x56, 0x01, 0x00, 0xFF, 0xEE, 0x80, 0x7F]
    await tb.write(a_bg(2, "INC"), vals)
    assert await tb.read(a_bg(2, "INC"), len(vals)) == [0] * len(vals)
    await tb.write(a_bg(2, "EDGE"), [0xFF])
    assert await tb.read(a_bg(2, "EDGE")) == [0]
    # readable beat-generator state: PHASE (generator stopped, so PH holds) and CTL (RUN=0, ARM, REN, WEN)
    await tb.write(a_bg(2, "PHASE"), [0xCD, 0xAB, 0xFE])
    assert await tb.read(a_bg(2, "PHASE"), 3) == [0xCD, 0xAB, 0x0E]
    await tb.write(a_eng(5, "PC"), [0xAB, 0xFE, 0xFF, 0x9C, 0x11, 0x22, 0x33, 0x44, 0xFF, 0x55, 0x3E, 0x66])
    assert await tb.read(a_eng(5, "PC"), 14) == [0xAB] + [0] * 13      # PC; CFG..W1H read 0; SYM, STAT = 0
    await tb.write(a_out(13, "ENG"), [0x07, 0x00, 0xCD, 0xAB, 0x12, 0x34])
    assert await tb.read(a_out(13, "ENG"), 6) == [0] * 6
    await tb.write(HM["UNIT_BASE"] + 8, [0x20, 0x83, 0xB8, 0xED])
    assert await tb.read(HM["UNIT_BASE"] + 8, 4) == [0] * 4
    await tb.write(a_ctrl("RUN"), [0xFF, 0x00, 0xFF])
    assert await tb.read(a_ctrl("RUN"), 3) == [0x01, 0x00, 0x03]
    await tb.write(a_ctrl("HOSTIN"), [0x77])
    assert await tb.read(a_ctrl("HOSTIN"), 3) == [0x77, 0x00, 0x01]     # HOSTIN, HOSTOUT, HOSTSTAT{OUTV,INV}
    assert await tb.read(0x2480, 2) == [0, 0]                            # unmapped
    assert await tb.read(0x0000, 2) == [0, 0]                            # program memory reads 0
    # a non-read/write command is ignored
    await tb.spi([0x55, a_eng(5, "PC") >> 8, a_eng(5, "PC") & 0xFF, 0x00])
    assert await tb.read(a_eng(5, "PC"), 1) == [0xAB]


@cocotb.test()
async def test_program_load(dut):
    """Program bytes collect into a staging word; byte 7 writes the word to the addressed core's memory."""
    tb = TB(dut)
    await tb.start()
    w = [0x0123456789ABCDEF, 0xFEDCBA9876543210]
    await tb.load(1, w, base=10)
    await tb.load(0, [0x1111222233334444], base=255)
    assert int(dut.u_pmem1.mem[10].value) == w[0]
    assert int(dut.u_pmem1.mem[11].value) == w[1]
    assert int(dut.u_pmem0.mem[255].value) == 0x1111222233334444


@cocotb.test()
async def test_toggle_every_beat(dut):
    """Engine 0 toggles O0 every beat of BG0; output waveform checked cycle-exact against SPEC 3/4/5/8."""
    tb = TB(dut)
    await tb.start()
    M = 24
    prog = [I(("IMM", "E.SYM"), jmode="always", imm=1, pause=True),
            I(("ZERO", "E.SYM"), jmode="always", imm=0, pause=True)]
    await tb.load(0, prog)
    await tb.write(a_bg(0, "INC"), le16(1) + le16(M) + le16(0xFFFF) * 3)
    await tb.engine(0, trig="BG0.BEAT")
    await tb.write(a_out(0, "ENG"), [0, 0, 0xAA, 0xAA, 0xFF, 0xFF])       # O0 = COMMITTED[0], OE always
    await tb.write(a_ctrl("RUN"), [1])
    tb.log = []
    ctl = a_bg(0, "CTL")
    await tb.write(ctl, [0x01])                                            # RUN
    await tb.cycles(8 * M)
    log, tb.log = tb.log, None
    w = next(s["t"] for s in log if s["h_we"] and s["h_waddr"] == ctl)
    beats = [w + k * M for k in range(1, 40)]
    # beat k commits the symbol staged by the burst after beat k-1: 0, 1, 0, 1, ... (beat 1 commits reset 0)
    def expect(t):
        v = 0
        for k, b in enumerate(beats, start=1):
            if b + 2 <= t:
                v = 0 if k == 1 else (k % 2 == 0)
        return int(v)
    checked = 0
    for s in log:
        if s["t"] >= w:
            assert (s["uio"] & 1) == expect(s["t"]), f"cycle {s['t'] - w} after CTL write: O0={s['uio'] & 1}"
            assert s["oe"] & 1 == 1
            checked += 1
    assert checked > 6 * M
    stat = (await tb.read(a_eng(0, "STAT")))[0]
    assert stat & 0x30 == 0, f"unexpected LATE/OVR {stat:#x}"


def bg_model(inc, mod, taps, n):
    """SPEC 3 for a free-running generator started with PH = 0: yields (beat, tap bits, seg) per cycle."""
    ph = 0
    out = []
    for _ in range(n):
        nn = ph + inc
        wrap = nn >= mod
        nx = (nn - mod if wrap else nn) & 0xFFFF
        tp = 0
        for k, t in enumerate(taps):
            if t < mod and ((t > ph or t <= nx) if wrap else (ph < t <= nx)):
                tp |= 1 << k
        seg = sum(1 for t in taps if ph >= t and t < mod)
        out.append((int(wrap), tp, seg))
        ph = nx
    return out


@cocotb.test()
async def test_beatgen_rate_and_taps(dut):
    """BG1 with INC=3, MOD=10, taps 2/5/8: BEAT/TAP pulses and SEG (seen through output cells) per SPEC 3."""
    tb = TB(dut)
    await tb.start()
    inc, mod, taps = 3, 10, (2, 5, 8)
    await tb.write(a_bg(1, "INC"), le16(inc) + le16(mod) + le16(taps[0]) + le16(taps[1]) + le16(taps[2]))
    await tb.engine(2, en=0, bg=1)
    await tb.write(a_out(8, "ENG"), [2, 0, 0xF0, 0xF0])   # O8 = SEG[0]
    await tb.write(a_out(9, "ENG"), [2, 0, 0x00, 0xFF])   # O9 = SEG[1]
    tb.probes = {"beat": dut.g_bg[1].u.beat, "tap": dut.g_bg[1].u.tap}
    tb.log = []
    await tb.write(a_bg(1, "CTL"), [0x01])
    await tb.cycles(120)
    log, tb.log = tb.log, None
    w = next(s["t"] for s in log if s["h_we"] and s["h_waddr"] == a_bg(1, "CTL"))
    run = [s for s in log if s["t"] > w]
    exp = bg_model(inc, mod, taps, len(run))
    nbeats = 0
    for i, s in enumerate(run):
        beat, tp, seg = exp[i]
        assert (s["beat"], s["tap"]) == (beat, tp), f"cycle {i}: beat/tap {s['beat']},{s['tap']} != {beat},{tp}"
        nbeats += beat
        if i >= 1:   # OUT' = LUT[{SEG, COMMITTED}] from the previous cycle's SEG
            got = (s["uo"] >> 2) & 3
            assert got == exp[i - 1][2], f"cycle {i}: SEG out {got} != {exp[i - 1][2]}"
    assert nbeats == (len(run) * inc) // mod or nbeats == (len(run) * inc) // mod + 1


@cocotb.test()
async def test_crc32_lfsr(dut):
    """CRC-32 of b'123456789' with LF0 (reflected Galois, POLY = 0xEDB88320) vs zlib.crc32; mailbox read."""
    tb = TB(dut)
    await tb.start()
    msg = b"123456789"
    prog = [I(("IMM", f"LF0.B{k}"), imm=0xFF) for k in range(4)]      # one LF0 write per cycle (one group)
    for b in msg:
        prog.append(I(("IMM", "SH0.LD"), imm=b))
        here = len(prog)
        prog.append(I(("SH0.O", "LF0.ST", "ifnot"), ("ZERO", "SH0.SH", "ifnot"), cond="SH0.DONE", jmode="ifnot",
                      imm=here))
    prog.append(I(("LF0.B0", "HOST.OUT"), pause=True))
    await tb.load(0, prog)
    await tb.write(HM["UNIT_BASE"], list((0xEDB88320).to_bytes(4, "little")))
    await tb.engine(0)
    await tb.write(a_ctrl("RUN"), [1, 0, 1])           # RUN, STICKY (no-op), IRQEN = OUTV
    assert (int(dut.uo_out.value) >> 1) & 1 == 0
    await tb.write(a_ctrl("DOORBELL"), [0x01])
    await tb.cycles(200)
    s = int(dut.g_lf[0].u.s.value)
    assert s ^ 0xFFFFFFFF == zlib.crc32(msg), f"S={s:#010x}"
    assert (int(dut.uo_out.value) >> 1) & 1 == 1                          # IRQ from OUTV
    assert await tb.read(a_ctrl("HOSTOUT"), 2) == [s & 0xFF, 0x02]       # HOSTOUT, HOSTSTAT (read: no side effect)
    assert await tb.read(a_ctrl("HOSTSTAT")) == [0x02]
    await tb.write(a_ctrl("HOSTSTAT"), [0x02])                            # W1C OUTV
    assert await tb.read(a_ctrl("HOSTSTAT")) == [0x00]
    await tb.cycles(4)
    assert (int(dut.uo_out.value) >> 1) & 1 == 0
    assert await tb.read(a_ctrl("STICKY")) == [0]


@cocotb.test()
async def test_sticky_flags(dut):
    """CONFLICT (two writes to ACC), MEMHAZ (P0.D read with RDY=0), OVR (trigger during burst), LATE (E.SYM after
    the beat boundary), IRQ on sticky errors and write-1-to-clear."""
    tb = TB(dut)
    await tb.start()
    prog = {0: I(("IMM", "ACC.LD"), ("IMM", "ACC.ADD"), imm=0x11),
            1: I(("ACC", "HOST.OUT"), pause=True),
            8: I(("IMM", "P0.AL"), imm=0),
            9: I(("P0.D", "R0"), pause=True),
            16: I(("IMM", "CNT0.HI"), imm=0x10),
            17: I(("ZERO", "CNT0.LO")),
            18: I(("ZERO", "CNT0.DEC"), cond="CNT0.Z", jmode="ifnot", imm=18),
            19: I(("IMM", "E.SYM"), imm=1, pause=True)}
    words = [prog.get(i, 0) for i in range(20)]
    await tb.load(0, words)
    await tb.write(a_bg(0, "INC"), le16(1) + le16(4) + le16(0xFFFF) * 3)
    await tb.write(a_bg(0, "CTL"), [0x01])
    await tb.engine(0)
    await tb.engine(1, pc=8)
    await tb.engine(2, pc=16)
    await tb.write(a_ctrl("RUN"), [1, 0, 2])            # IRQEN = sticky errors
    await tb.write(a_ctrl("DOORBELL"), [0x01])
    await tb.cycles(20)
    assert await tb.read(a_ctrl("STICKY")) == [0x01]
    assert await tb.read(a_ctrl("HOSTOUT")) == [0x11]                     # LD (move 0) won
    assert (int(dut.uo_out.value) >> 1) & 1 == 1
    await tb.write(a_ctrl("STICKY"), [0x01])
    assert await tb.read(a_ctrl("STICKY")) == [0x00]
    await tb.cycles(4)
    assert (int(dut.uo_out.value) >> 1) & 1 == 0
    await tb.write(a_ctrl("DOORBELL"), [0x02])
    await tb.cycles(20)
    assert await tb.read(a_ctrl("STICKY")) == [0x02]
    await tb.write(a_ctrl("STICKY"), [0x02])
    # engine 2: long burst; a second doorbell during it overruns; the final E.SYM is late
    await tb.write(a_ctrl("DOORBELL"), [0x04])
    await tb.write(a_ctrl("DOORBELL"), [0x04])
    stat = (await tb.read(a_eng(2, "STAT")))[0]
    assert stat & 0x20 and stat & 0x02 and not stat & 0x10, f"STAT {stat:#x}"
    await tb.cycles(4500)
    assert await tb.read(a_eng(2, "STAT")) == [0x30]
    assert (int(dut.uo_out.value) >> 1) & 1 == 1
    await tb.write(a_eng(2, "STAT"), [0x30])
    assert await tb.read(a_eng(2, "STAT")) == [0x00]
    assert await tb.read(a_ctrl("STICKY")) == [0x00]
    for e in (0, 1):
        assert (await tb.read(a_eng(e, "STAT")))[0] & 0x30 == 0


@cocotb.test()
async def test_data_ram_pointers(dut):
    """Host data-RAM write/read (prefetching reads), pointer fetch/wait-RDY/read-next and pointer write on core 1."""
    tb = TB(dut)
    await tb.start()
    base = HM["DATA_BASE"]
    await tb.write(base + 5, [0xA5, 0x3C])
    assert await tb.read(base + 5, 2) == [0xA5, 0x3C]
    prog = [I(("IMM", "P0.AL"), imm=5),
            I(("ZERO", "P0.AH")),
            I(cond="P0.RDY", jmode="ifnot", imm=2),
            I(("P0.D", "ACC.LD"), ("IMM", "P1.AL"), imm=0x20),
            I(("ZERO", "P1.AH")),
            I(("IMM", "P1.W"), ("ZERO", "P0.R"), imm=0x5A),
            I(cond="P0.RDY", jmode="ifnot", imm=6),
            I(("P0.D", "ACC.ADD")),
            I(("ACC", "HOST.OUT"), pause=True)]
    await tb.load(1, prog)
    await tb.engine(3, core=1)
    await tb.write(a_ctrl("RUN"), [1])
    await tb.write(a_ctrl("DOORBELL"), [0x08])
    await tb.cycles(40)
    assert await tb.read(a_ctrl("HOSTOUT")) == [(0xA5 + 0x3C) & 0xFF]
    assert await tb.read(base + 0x20, 1) == [0x5A]
    assert await tb.read(a_ctrl("STICKY")) == [0x00]
