"""Lockstep scenarios for Metronome v2: per-cycle pin stimulus for tt_um_brentius_metronome and the metronome2 model.

Everything reaches the chip through its pins: configuration, programs and data RAM contents are written over the SPI
host link (wiki/SPEC_V2.md 9), and read-backs over SPI show up on MISO, which the harness compares every cycle like
every other output. Input pins may be a function of the previous cycle's outputs (loopback).

A scenario is a list of steps (ui_in, uio spec, rst_n). The uio spec is an int or a function f(t, outs) of the cycle
index and the model's outputs (uo, uio_out, uio_oe) of the previous cycle.
"""
from __future__ import annotations

import random

from metronome2 import asm, m
from metronome2 import spi

I = asm.insn
HM = m.HOST_MAP
IDLE = spi.IDLE        # ui_in: CS_N high, SCK low


def le(v, n):
    return int(v).to_bytes(n, "little")


def edge(pin, pol, wen=0, follow=0):
    return pin | (pol << 4) | (wen << 6) | (follow << 7)


def tcfg(core=0, line=0, trig="NONE"):
    return core | (line << 1) | (m.TRIG_ID[trig] << 3)


def lut(fn, bits=5):
    return sum((fn(i) & 1) << i for i in range(1 << bits))


def hold_byte(pin, lvl, tap, en=1):
    return pin | (lvl << 4) | (tap << 5) | (en << 7)


def reg_addr(block, i, name):
    base, st, n, regs = m.HOST_BLOCKS[block]
    a0 = HM[base] + (m.HOST_STRIDE[st] * i if st else 0)
    for off, r in regs.items():
        if r[0] == name:
            return a0 + off, r[1]
    raise KeyError(name)


class Scn:
    def __init__(self, name, half=2, pins_hi=0):
        self.name = name
        self.steps = []
        self.half = half            # SCK half period for writes (reads always use 8: SCK = clk/16)
        self.uio = 0
        self.pins_hi = pins_hi      # ui_in[7:3] (P8..P12) level or function, ORed into every frame
        self.compare_from = 0
        self.check = None

    # ---------------------------------------------------------------- raw stimulus
    def _ui(self, f):
        return f, self.pins_hi

    def frames(self, ui_list):
        for f in ui_list:
            self.steps.append((f, self.pins_hi, self.uio, 1))

    def idle(self, n):
        self.frames([IDLE] * n)

    def reset(self, low=3, after=6):
        for _ in range(low):
            self.steps.append((IDLE, self.pins_hi, self.uio, 0))
        self.idle(after)

    # ---------------------------------------------------------------- host link
    def write(self, addr, data, half=None):
        self.frames(spi.write_frames(addr, bytes(data), half or self.half))

    def read(self, addr, n):
        self.frames(spi.read_frames(addr, n, 8))

    def blk(self, block, i=0, **kw):
        """Write named registers of a host block, one SPI transaction per contiguous run."""
        items = sorted(reg_addr(block, i, k) + (v,) for k, v in kw.items())
        run_a, run_b = None, b""
        for a, nb, v in items:
            if run_a is not None and a == run_a + len(run_b):
                run_b += le(v, nb)
            else:
                if run_a is not None:
                    self.write(run_a, run_b)
                run_a, run_b = a, le(v, nb)
        if run_a is not None:
            self.write(run_a, run_b)

    def program(self, core, words, base=0):
        img = b"".join(le(w, 8) for w in words)
        self.write(HM["PROG_BASE"] + core * m.HOST_STRIDE["PROG_CORE"] + 8 * base, img)

    def data(self, off, data):
        self.write(HM["DATA_BASE"] + off, bytes(data))

    def thread(self, t, core=0, line=0, trig="NONE", pc=0, en=1, **kw):
        self.blk("THREAD", t, CFG=tcfg(core, line, trig), **kw)
        self.blk("TRT", t, PC=pc, STAT=en << 3)

    def readback_all(self):
        """Read every runtime register block (values appear on MISO)."""
        for b in ("CTRL", "LRT", "TRT", "SRT"):
            base, st, n, _ = m.HOST_BLOCKS[b]
            span = (m.HOST_STRIDE[st] if st else 0x10) * n
            self.read(HM[base], span)


# ==================================================================================================== directed
def smoke():
    s = Scn("smoke")
    s.reset()
    s.read(HM["CTRL_BASE"] + 7, 1)                                    # ID
    s.data(0x123, [1, 2, 3, 4, 5])
    s.read(HM["DATA_BASE"] + 0x123, 5)
    s.write(HM["LINE_BASE"] + 2, [0x34, 0x12])
    s.read(HM["LINE_BASE"] + 2, 2)                                    # write-only: reads 0
    s.blk("CTRL", IRQEN=1, HOSTIN=0x5A)
    s.read(HM["CTRL_BASE"], 9)
    s.blk("LRT", 1, PHASE=0x0102, CTL=0b110)
    s.blk("TRT", 3, PC=0x77, STAT=0x08)
    s.blk("SRT", 1, CTL=0x81)
    s.readback_all()
    s.read(0xFFF0, 4)                                                 # unmapped
    s.write(0x3000, [9])                                              # unmapped write
    s.idle(20)
    return s


def eth_loopback():
    """10 Mbit/s at 60 MHz (one bit per 6 cycles): TX stream on core 0, RX stream on core 1, O0 looped to P0."""
    s = Scn("eth_loopback")
    s.reset()
    data = [0x55, 0xD5, 0x12, 0xF0, 0x0F, 0xC3]
    s.data(0, data)
    s.blk("STREAM", 0, MODE=0, START=0, LEN=len(data))
    s.blk("SRT", 0, CTL=1)
    s.blk("LINE", 0, INC=1, MOD=6, T0=0, T1=3, T2=0xFFFF)
    s.blk("OUT", 0, BIND=0b100, SEL=0, LUT=lut(lambda i: i & 1), OE=0xFFFFFFFF)
    s.program(0, [I(("S0.BIT", "L.DBIT"), ("ZERO", "S0.ADV"), pause=1, jmode="always", imm=0)])
    s.thread(0, core=0, line=0, trig="L0.BEAT")
    nrx = len(data) + 1
    s.blk("STREAM", 1, MODE=1, START=0x400, LEN=nrx)
    s.blk("SRT", 1, CTL=1)
    s.blk("LINE", 1, INC=1, MOD=6, T0=5, T1=0xFFFF, T2=0xFFFF, PINS=0, SNAP=0, LUT0=lut(lambda i: i & 1))
    s.program(1, [I(("L.IN", "S1.RX"), pause=1, jmode="always", imm=0)])
    s.thread(1, core=1, line=1, trig="L1.TAP0")
    s.blk("CTRL", RUN=1)
    s.uio = lambda t, o: o[1] & 1                                      # loopback O0 -> P0
    # start both lines with one host transaction each; they start 128 cycles apart, which is fine for a loopback
    s.blk("LRT", 0, CTL=1)
    s.blk("LRT", 1, CTL=1)
    s.idle(6 * 8 * nrx + 60)
    s.read(HM["DATA_BASE"] + 0x400, nrx)
    s.readback_all()
    return s


def follower():
    """Follower-mode SPI target: boundary on SCK fall (P0), edge-sourced tap 0 on SCK rise captures MOSI (P1); the
    thread on tap 0 echoes the sampled bit to O0 and counts bits in CNT0; the clock period varies, then stops."""
    s = Scn("follower")
    s.reset()
    s.blk("LINE", 0, INC=1, MOD=200, T1=0xFFFF, T2=0xFFFF, PRE=0, EDGE=edge(0, 2, follow=1),
          T0EDGE=edge(0, 1) | 0x40, PINS=1, SNAP=0, LUT0=lut(lambda i: i & 1), LUT1=lut(lambda i: (i >> 4) & 1))
    s.blk("OUT", 0, BIND=0b100, SEL=0, LUT=lut(lambda i: i & 1), OE=0xFFFFFFFF)
    s.blk("OUT", 9, BIND=0b100, SEL=0, LUT=lut(lambda i: (i >> 3) & 1))     # SEG bit 0 on O9
    s.program(0, [I(("L.IN", "L.DBIT"), ("ZERO", "CNT0.DEC"), ("L.CAP", "HOST.OUT"), pause=1, jmode="always",
                    imm=0)])
    s.thread(0, core=0, line=0, trig="L0.TAP0")
    s.blk("CTRL", RUN=1, IRQEN=1)
    s.blk("LRT", 0, CTL=0b101)
    rnd = random.Random(1)
    wave = []
    for _ in range(40):
        bit = rnd.randint(0, 1)
        half = rnd.randint(4, 12)
        wave += [(bit << 1)] * half + [1 | (bit << 1)] * half
    wave += [0] * 450                                                 # clock stops: a wrap with no edge clears SYNC
    s.uio = lambda t, o, w=wave, t0=[None]: w[min(len(w) - 1, _rel(t0, t))]
    s.idle(len(wave))
    s.uio = 0
    s.readback_all()
    return s


def spi_target():
    """SPI target on lines (D28). P0 = SCK, P1 = MOSI, P2 = CS_N; O0 = MISO from line 0's committed symbol.
    Mode 0 (line 0): boundary on SCK fall commits, edge-sourced tap 0 on SCK rise captures. A thread triggered by
    CS_N falling (line 1, a follower on P2) stages the first bit and starts line 0 with a move, so the start commit
    puts bit 0 on MISO before the first clock edge; it stages bit 1 next. A boundary thread stages each later bit.
    TX and RX streams are MSB first. Mode 1 (line 2): boundary on SCK rise, tap 0 on SCK fall, so its first boundary
    comes before any capture edge: no TAPMISS in the starting beat (FIRST). SEG of line 2 shows on O8."""
    s = Scn("spi_target")
    s.reset()
    s.data(0, [0xA5, 0x3C, 0x96, 0x0F, 0x81, 0x7E])
    s.blk("STREAM", 0, MODE=0b10, START=0, LEN=6)
    s.blk("SRT", 0, CTL=1)
    s.blk("STREAM", 1, MODE=0b11, START=0x100, LEN=6)
    s.blk("SRT", 1, CTL=1)
    s.blk("LINE", 0, INC=1, MOD=200, T1=0xFFFF, T2=0xFFFF, PRE=0, EDGE=edge(0, 2, follow=1),
          T0EDGE=edge(0, 1) | 0x40, PINS=1, SNAP=0, LUT0=lut(lambda i: i & 1))
    s.blk("LINE", 1, INC=1, MOD=60000, T1=0xFFFF, T2=0xFFFF, EDGE=edge(2, 2, follow=1), T0EDGE=edge(2, 2) | 0x40)
    s.blk("LINE", 2, INC=1, MOD=200, T1=0xFFFF, T2=0xFFFF, EDGE=edge(0, 1, follow=1), T0EDGE=edge(0, 2) | 0x40,
          PINS=1, SNAP=0, LUT0=lut(lambda i: i & 1))
    s.blk("OUT", 0, BIND=0b100, SEL=0, LUT=lut(lambda i: i & 1), OE=0xFFFFFFFF)
    s.blk("OUT", 8, BIND=0b100 | 2, LUT=lut(lambda i: (i >> 3) & 1))
    s.program(0, [
        I(("S0.BIT", "L.DBIT"), ("ZERO", "S0.ADV"), ("IMM", "L0.CTL"), imm=0b101),      # 0: CS fall: bit 0, start
        I(("S0.BIT", "L.DBIT"), ("ZERO", "S0.ADV"), pause=1, jmode="always", imm=0),    # 1: bit 1
        I(("S0.BIT", "L.DBIT"), ("ZERO", "S0.ADV"), pause=1, jmode="always", imm=2),    # 2: boundary: next bit
    ])
    s.program(1, [I(("L.IN", "S1.RX"), pause=1, jmode="always", imm=0)])              # capture (core 1)
    s.thread(0, core=0, line=0, trig="L1.TAP0", pc=0)
    s.thread(1, core=0, line=0, trig="L0.BEAT", pc=2)
    s.thread(2, core=1, line=0, trig="L0.TAP0", pc=0)
    s.blk("CTRL", RUN=1, IRQEN=2)
    s.blk("LRT", 1, CTL=0b101)
    s.blk("LRT", 2, CTL=0b101)
    rnd = random.Random(5)
    wave = [0b100] * 20
    for nbits in (16, 8):
        wave += [0b000] * rnd.randint(8, 20)                       # CS_N falls; MISO must show bit 0 here
        for _ in range(nbits):
            b = rnd.randint(0, 1) << 1
            h = rnd.randint(6, 12)
            wave += [b] * h + [b | 1] * h
        wave += [0b000] * 10 + [0b100] * 40
    s.uio = lambda t, o, w=wave, t0=[None]: w[min(len(w) - 1, _rel(t0, t))]
    s.idle(len(wave))
    s.uio = 0b100
    s.read(HM["DATA_BASE"] + 0x100, 6)
    s.readback_all()
    return s


def _rel(t0, t):
    if t0[0] is None:
        t0[0] = t
    return t - t0[0]


def hold():
    """Hold (SPEC 3.2a): line 0 holds before tap 1 until P0 reads 1; SEG and the phase-parity table show on O8..O10;
    the host reads CTL (HELD) during the hold. Then the pin toggles, so the beat stretches and resumes."""
    s = Scn("hold")
    s.reset()
    s.blk("LINE", 0, INC=1, MOD=8, T0=0, T1=4, T2=6, HOLD=hold_byte(0, 1, 1))
    s.blk("LINE", 1, INC=1, MOD=10, T0=2, T1=5, T2=0xFFFF, HOLD=hold_byte(1, 0, 2))   # HTAP 2 disabled tap: no hold
    s.blk("LINE", 2, INC=3, MOD=11, T0=1, T1=7, T2=9, HOLD=hold_byte(2, 0, 0))
    s.blk("LINE", 3, INC=1, MOD=9, T0=3, T1=6, T2=0, T0EDGE=edge(3, 3) | 0x40, HOLD=hold_byte(3, 1, 0))  # T0SRC
    for o, ln in ((8, 0), (9, 1), (10, 2), (11, 3)):
        s.blk("OUT", o, BIND=0b100 | ln, LUT=lut(lambda i: ((i >> 3) & 1) ^ ((i >> 4) & 1)))
    s.blk("OUT", 0, BIND=0b100, LUT=lut(lambda i: (i >> 4) & 1), OE=lut(lambda i: (i >> 3) & 1))
    s.program(0, [I(("ZERO", "CNT0.DEC"), pause=1, jmode="always", imm=0)])
    s.thread(0, core=0, line=0, trig="L0.TAP2")
    s.blk("CTRL", RUN=1)
    s.uio = 0
    for ln in range(4):
        s.blk("LRT", ln, CTL=1)
    s.idle(60)
    s.read(HM["LRT_BASE"] + 2, 1)                                     # HELD in bit 7
    s.uio = 0b0001                                                    # release P0
    s.idle(60)
    s.uio = lambda t, o: (t // 7) & 0b1111                            # pins toggle: beats stretch irregularly
    s.idle(400)
    s.readback_all()
    return s


def taps():
    """Taps, fired bits, TAPMISS and SEG: generated beats; host PHASE writes jump over taps; window re-alignment on
    a recovered clock; snapshot at the boundary; TAPMISS read and cleared."""
    s = Scn("taps")
    s.reset()
    s.blk("LINE", 0, INC=1, MOD=12, T0=1, T1=5, T2=9, SNAP=3, PINS=0x10, LUT0=lut(lambda i: i), LUT1=lut(lambda i: i >> 3))
    s.blk("LINE", 1, INC=1, MOD=16, T0=2, T1=10, T2=13, PRE=6, WLO=4, WHI=8, EDGE=edge(2, 3, wen=1), SNAP=1, PINS=2)
    s.blk("LINE", 2, INC=5, MOD=23, T0=0, T1=0, T2=0, SNAP=2)
    s.blk("LINE", 3, INC=2, MOD=30, T0=29, T1=1, T2=40, PRE=20, EDGE=edge(4, 1), SNAP=0, PINS=4)
    for o in range(14):
        ln = o % 4
        s.blk("OUT", o, BIND=0b100 | ln, SEL=(o % 4) | ((o // 4) % 4) << 2, LUT=0x9A5C3F61 ^ (o * 0x01010101),
              **({"OE": 0x5A5AA5A5 ^ o} if o < 8 else {}))
    s.blk("CTRL", RUN=1)
    s.uio = lambda t, o: ((t // 11) & 1) << 2 | ((t // 9) & 1) | ((t // 5) & 1) << 4
    s.blk("LRT", 0, CTL=1)
    s.blk("LRT", 1, CTL=0b110)                                        # ARM + REN: edge start, re-align
    s.blk("LRT", 3, CTL=0b010)
    s.blk("LRT", 2, CTL=1)
    s.idle(100)
    s.blk("LRT", 0, PHASE=10)                                         # jump over T2: TAPMISS
    s.idle(40)
    s.blk("LRT", 2, PHASE=0x0102)
    s.idle(30)
    s.readback_all()
    s.blk("LRT", 0, STAT=1)
    s.blk("LRT", 1, CTL=0)
    s.blk("LRT", 1, CTL=0b111)
    s.idle(200)
    s.readback_all()
    return s


def units():
    """Core and units: jumps on jcond, watchers, round-robin, T.STOP, conflict, late, overrun, flags rise triggers,
    ALWAYS, doorbells, mailbox, accumulator, shifters, counters, LFSRs, pointer reads/writes, ERRSUM and IRQ."""
    s = Scn("units")
    s.reset()
    s.data(0x40, list(range(0x10, 0x30)))
    s.blk("LFSR", 0, POLY=0xEDB88320)
    s.blk("LFSR", 1, POLY=0x8408)
    s.blk("LINE", 0, INC=1, MOD=20, T0=3, T1=9, T2=15)
    s.blk("OUT", 8, BIND=0b100, SEL=0 | 1 << 2 | 2 << 4, LUT=0xF0F0CCAA)
    s.blk("OUT", 9, BIND=0b100, SEL=3 | 3 << 2 | 3 << 4, LUT=0xFF00FF00)
    p0 = [
        # 0: doorbell thread 0: set up units, then loop on CNT0
        I(("IMM", "SH0.CFG"), ("IMM", "CNT0.LO"), ("IMM", "ACC.LD"), imm=0x13),
        I(("IMM", "SH0.LD"), ("IMM", "P0.AL"), ("IMM", "LF0.B0"), imm=0x45),
        I(("SH0.O", "SH0.SH"), ("ACC", "ACC.ADD"), ("ZERO", "CNT0.DEC"), cond="CNT0.Z", jmode="ifnot", jcond="CNT0.Z",
          imm=2),
        I(("P0.D", "R0"), ("SH0.D", "LF0.ST"), ("ZERO", "P0.R"), cond="P0.RDY"),
        I(("P0.D", "ACC.XOR"), ("LF0.B1", "HOST.OUT"), ("IMM", "FLAGS.SET"), imm=3),
        I(("ACC", "P0.W"), ("CNT0.HI", "ACC.SUB"), ("IMM", "FLAGS.SET"), imm=1, pause=1),
        # 6: flag-1 rise thread 1: conflict on ACC with core 1, symbol writes (late: not line-triggered)
        I(("IMM", "L.SYM"), ("IMM", "ACC.CMP"), ("FLAGS.LO", "R1"), imm=0x5),
        I(("IMM", "L.XOR"), ("R1", "L.DBIT"), ("IMM", "FLAGS.CLR"), imm=1),
        I(("LF0.O", "CNT1.HI"), ("ACC", "ACC.AND"), ("IMM", "FLAGS.SET"), imm=8, pause=1),
        # 9: line-0 tap thread 2: on-time symbol writes, mailbox read
        I(("HOST.IN", "R2"), ("R2", "L.SYM"), cond="HOST.INV"),
        I(("R2", "ACC.OR"), ("PINS.LO", "R3"), ("CNT1.HI", "LF1.B2"), jmode="if", jcond="ACC.N", imm=12),
        I(("IMM", "SH1.CFG"), imm=0x18, pause=1),
        I(("ACC", "SH1.LD"), ("R3", "LF1.ST"), pause=1, jmode="always", imm=9),
        # 13: thread 3 (doorbell): a pointer move in the serve cycle makes the landing stale (SPEC v1 9a.3), so
        # P0.RDY stays 0 and the guarded HOST.OUT does not happen; then it stops itself and writes CNT2
        I(("IMM", "P0.AL"), imm=0x41),
        I(("ZERO", "P0.R")),
        I(("ZERO", "NULL")),
        I(("P0.D", "HOST.OUT", "if"), cond="P0.RDY"),
        I(("P0.D", "HOST.OUT", "if"), cond="P0.RDY"),
        I(("IMM", "CNT2.LO"), ("ZERO", "T.STOP"), ("IMM", "FLAGS.SET"), imm=9, pause=1),
    ]
    p1 = [
        # 0: flag-1 rise thread 4 on core 1 (same cycle as thread 1 on core 0 when both dispatch together)
        I(("IMM", "ACC.LD"), ("IMM", "L.SYM"), ("SH1.D", "R3"), imm=0x0A),
        I(("ACC", "HOST.OUT"), ("LF1.B0", "ACC.ADD"), ("IMM", "FLAGS.CLR"), imm=3, pause=1),
        # 2: ALWAYS thread 5 with a watcher (F8 -> handler 4)
        I(("CNT2.LO", "R0"), ("IMM", "FLAGS.SET"), imm=10, pause=1),
        I(("ZERO", "NULL"), pause=1),
        I(("IMM", "FLAGS.CLR"), imm=8, pause=1),                       # PC becomes 5
        I(pause=1, jmode="always", imm=2),
    ]
    s.program(0, p0)
    s.program(1, p1)
    s.thread(0, core=0, line=0, trig="NONE", pc=0)
    s.thread(1, core=0, line=0, trig="FLAG1.RISE", pc=6)
    s.thread(2, core=0, line=0, trig="L0.TAP1", pc=9)
    s.thread(3, core=0, line=0, trig="NONE", pc=13)
    s.thread(4, core=1, line=0, trig="FLAG1.RISE", pc=0)
    s.thread(5, core=1, line=1, trig="ALWAYS", pc=2, W0C=m.GUARD_ID["F8"], W0H=4, W1C=m.GUARD_ID["L.PINA"], W1H=3)
    s.blk("CTRL", RUN=1, IRQEN=3)
    s.blk("LRT", 0, CTL=1)
    s.uio = lambda t, o: (t // 13) & 0xFF
    s.blk("CTRL", DOORBELL=0b1001)
    s.idle(80)
    s.blk("CTRL", HOSTIN=0x81)
    s.idle(60)
    s.blk("CTRL", DOORBELL=0b0001)
    s.idle(40)
    s.blk("CTRL", DOORBELL=0b0001)                                    # overrun while running
    s.idle(100)
    s.readback_all()
    s.blk("CTRL", STICKY=3, HOSTSTAT=2)
    s.blk("TRT", 1, STAT=0x38)
    s.blk("TRT", 4, STAT=0x38)
    s.readback_all()
    s.blk("CTRL", RUN=0)
    s.idle(20)
    s.readback_all()
    return s


def reset_mid():
    """A reset in the middle of a run clears every register and the configuration; memories keep their contents."""
    s = eth_loopback()
    s.name = "reset_mid"
    s.reset(low=5, after=4)
    s.readback_all()
    s.read(HM["DATA_BASE"], 8)
    s.blk("LRT", 0, CTL=1)
    s.idle(40)
    return s


def shifter_parallel():
    """Both cores exercise independent CFG and LD/SH groups, exposing data and count on MISO."""
    s = Scn("shifter_parallel")
    s.reset()
    for core in range(2):
        words = []
        for k in range(2):
            for op in ("LD", "SH"):
                for cfg_first in (False, True):
                    words += [I(("IMM", f"SH{k}.CFG"), imm=3),
                              I(("IMM", f"SH{k}.LD"), imm=0x81)]
                    moves = [("IMM", f"SH{k}.CFG"), ("IMM", f"SH{k}.{op}")]
                    if not cfg_first:
                        moves.reverse()
                    words += [I(*moves, imm=0x12),
                              I((f"SH{k}.D", "HOST.OUT"), pause=1),
                              I(("ZERO", f"SH{k}.SH")),
                              I(("ZERO", f"SH{k}.SH")),
                              I(("IMM", "HOST.OUT", "if"), cond=f"SH{k}.DONE", imm=0x5A),
                              I(("IMM", "HOST.OUT", "ifnot"), cond=f"SH{k}.DONE", imm=0xA5, pause=1)]
        s.program(core, words)
        s.thread(core, core=core, trig="NONE")
        s.blk("CTRL", RUN=1)
        for _ in range(16):
            s.blk("CTRL", DOORBELL=1 << core)
            s.idle(20)
            s.read(HM["CTRL_BASE"] + 4, 2)
        s.blk("TRT", core, STAT=0)
    return s


# ==================================================================================================== random
GROUP_OF = {d: g for g, ds in m.WRITE_GROUPS.items() for d in ds}


def random_scn(seed, run_cycles=3000):
    rnd = random.Random(seed)
    s = Scn(f"random_{seed}")
    s.pins_hi = 0
    s.reset()
    # ---------------- data RAM and streams
    for _ in range(3):
        off = rnd.randrange(0, m.DATA_BYTES - 40)
        s.data(off, [rnd.randrange(256) for _ in range(rnd.randint(4, 24))])
    for k in range(m.N_STREAMS):
        s.blk("STREAM", k, MODE=rnd.randrange(4), START=rnd.randrange(2048), LEN=rnd.choice([0, 1, 3, 8, 40, 2048]),
              MARK=rnd.randrange(12))
        s.blk("SRT", k, CTL=1)
    for k in range(m.N_LFSRS):
        s.blk("LFSR", k, POLY=rnd.getrandbits(32))
    # ---------------- lines
    for ln in range(m.N_LINES):
        mod = rnd.randint(3, 40)
        inc = 1 if rnd.random() < 0.7 else rnd.randint(1, mod - 1)
        tap = lambda: rnd.choice([rnd.randrange(mod), rnd.randrange(mod), rnd.randrange(mod), mod + rnd.randrange(3)])
        wlo, whi = rnd.randrange(mod), rnd.randrange(mod)
        kw = dict(INC=inc, MOD=mod, T0=tap(), T1=tap(), T2=tap(), PRE=rnd.randrange(mod), WLO=wlo, WHI=whi,
                  EDGE=edge(rnd.randrange(16), rnd.randrange(4), rnd.randrange(2), int(rnd.random() < 0.25)),
                  T0EDGE=edge(rnd.randrange(16), rnd.randrange(4)) | (0x40 if rnd.random() < 0.25 else 0),
                  PINS=rnd.randrange(256), SNAP=rnd.randrange(4), LUT0=rnd.getrandbits(32), LUT1=rnd.getrandbits(32))
        if rnd.random() < 0.5:
            hpin = rnd.randrange(13)
            kw["HOLD"] = hold_byte(hpin, rnd.randrange(2), rnd.randrange(4), 1)
        s.blk("LINE", ln, **kw)
    # ---------------- output pins
    for o in range(m.N_OUT_PINS):
        kw = dict(BIND=rnd.randrange(8), SEL=rnd.randrange(64), LUT=rnd.getrandbits(32))
        if o < m.N_OE_PINS:
            kw["OE"] = rnd.getrandbits(32)
        s.blk("OUT", o, **kw)
    # ---------------- programs: bursts ending in a pause
    srcs = [p.name for p in m.SRC]
    dsts = [p.name for p in m.DST]
    guards = [p.name for p in m.GUARD_CONDS]
    starts = {0: [], 1: []}
    for c in range(m.N_CORES):
        words = []
        nb = rnd.randint(3, 6)
        for b in range(nb):
            starts[c].append(len(words))
            ln = rnd.randint(1, 5)
            for i in range(ln):
                moves = []
                for _ in range(3):
                    d = rnd.choice(dsts)
                    if d == "T.STOP" and rnd.random() < 0.8:
                        d = "NULL"
                    if d.endswith(".CTL") and d.startswith("L") and rnd.random() < 0.7:
                        d = "NULL"
                    moves.append((rnd.choice(srcs), d, rnd.choice(["always", "always", "if", "ifnot", "never"])))
                last = i == ln - 1
                jm = rnd.choice(["next", "next", "next", "always", "if", "ifnot"])
                w = I(*moves, cond=rnd.choice(guards), jmode=jm, jcond=rnd.choice(m.JUMP_GUARDS), imm=0,
                      pause=int(last))
                # jump targets: forward within the burst, or (on the pause) any burst start
                f = m.FIELD["imm"]
                if last:
                    tgt = rnd.choice(starts[c]) if starts[c] else 0
                else:
                    tgt = len(words) + rnd.randint(1, ln - i)
                w |= (tgt & 0xFF) << f.lsb
                words.append(w)
        # the last burst's forward jumps may point one past the end: pad with a pausing NOP
        words.append(I(pause=1))
        # occasionally an out-of-table src/dst/cond (9a.1)
        if rnd.random() < 0.5:
            j = rnd.randrange(len(words))
            words[j] |= (63 << m.FIELD["m1_src"].lsb) | (63 << m.FIELD["m2_dst"].lsb)
        s.program(c, words)
    # ---------------- threads
    trigs = m.TRIGGERS + ["31"]
    for t in range(m.N_THREADS):
        c = rnd.randrange(2)
        tr = rnd.choice(trigs)
        code = int(tr) if tr == "31" else m.TRIG_ID[tr]
        st = starts[c]
        s.blk("THREAD", t, CFG=c | (rnd.randrange(4) << 1) | (code << 3),
              W0C=rnd.choice([0, 0, rnd.randrange(64)]), W1C=rnd.choice([0, rnd.randrange(64)]),
              W0H=rnd.choice(st), W1H=rnd.choice(st))
        s.blk("TRT", t, PC=rnd.choice(st), STAT=0x08 if rnd.random() < 0.85 else 0)
    s.blk("CTRL", RUN=1, IRQEN=rnd.randrange(4))
    # ---------------- run with random input activity and host traffic
    p = [rnd.choice([0, 3, 7, 20, 60]) for _ in range(16)]
    state = {"v": rnd.getrandbits(16)}

    def pins(t, o, p=p, st=state, r=random.Random(seed * 7 + 1)):
        v = st["v"]
        for b in range(16):
            if p[b] and r.randrange(p[b]) == 0:
                v ^= 1 << b
        st["v"] = v
        return v & 0xFF

    s.uio = pins
    s.pins_hi = lambda t, o, st=state: ((st["v"] >> 8) & 0x1F) << 3
    for ln in range(m.N_LINES):
        s.blk("LRT", ln, CTL=rnd.randrange(8))
    s.blk("CTRL", DOORBELL=rnd.getrandbits(6))
    done = 0
    while done < run_cycles:
        n = rnd.randint(50, 400)
        s.idle(n)
        done += n
        r = rnd.random()
        if r < 0.15:
            s.blk("CTRL", DOORBELL=rnd.getrandbits(6))
        elif r < 0.25:
            s.blk("LRT", rnd.randrange(4), CTL=rnd.randrange(8))
        elif r < 0.32:
            s.blk("LRT", rnd.randrange(4), PHASE=rnd.randrange(40))
        elif r < 0.40:
            s.blk("TRT", rnd.randrange(6), STAT=rnd.choice([0x08, 0x38, 0x30, 0x00]))
        elif r < 0.45:
            s.blk("TRT", rnd.randrange(6), PC=rnd.randrange(16))
        elif r < 0.52:
            s.blk("CTRL", HOSTIN=rnd.randrange(256))
        elif r < 0.58:
            s.blk("CTRL", STICKY=3, HOSTSTAT=2)
        elif r < 0.64:
            s.blk("SRT", rnd.randrange(2), CTL=rnd.choice([1, 2, 0x80, 0x83]))
        elif r < 0.70:
            s.blk("LINE", rnd.randrange(4), LUT0=rnd.getrandbits(32))
        elif r < 0.85:
            s.read(rnd.choice([HM["CTRL_BASE"], HM["LRT_BASE"], HM["TRT_BASE"], HM["SRT_BASE"]]), rnd.randint(1, 12))
        else:
            s.read(HM["DATA_BASE"] + rnd.randrange(2048), rnd.randint(1, 4))
    s.readback_all()
    return s


DIRECTED = {"smoke": smoke, "eth_loopback": eth_loopback, "follower": follower, "hold": hold, "taps": taps,
            "units": units, "reset_mid": reset_mid, "spi_target": spi_target, "shifter_parallel": shifter_parallel}


def build(name: str) -> Scn:
    if name.startswith("random_"):
        return random_scn(int(name.split("_")[1]))
    return DIRECTED[name]()
