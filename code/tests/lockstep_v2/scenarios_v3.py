"""v3 lockstep scenarios (wiki/SPEC_V2.md section 12): live-pin table inputs, the execution digest, freeze/step and
debug readback, edge capture into S0, and random runs with the v3 features mixed in.

Every v3 value the harness can check goes out on MISO: the digest (MISR), the debug readback block and the captured
records in data RAM are read over SPI and compared cycle by cycle with the model, like every pin.
"""
from __future__ import annotations

import random

from metronome2 import m

from scenarios import HM, I, Scn, edge, lut, random_scn

DBG_SPAN = 0x14


def readback_dbg(s):
    s.read(HM["DBG_BASE"], DBG_SPAN)


def busy_programs(s):
    """Line 0 (8-cycle beat) with a counting thread on core 0 and a pointer read loop; line 1 (3-cycle beat) with
    transmit stream S0 shown on O9 by a thread on core 1."""
    s.data(0x00, [0x5A, 0xC3, 0x0F, 0x99, 0x24, 0x81, 0x7E, 0x3C] * 2)
    s.blk("STREAM", 0, MODE=0, START=0, LEN=16)
    s.blk("SRT", 0, CTL=1)
    s.blk("LINE", 0, INC=1, MOD=8, T0=0, T1=4, T2=6, PINS=0x10)
    s.blk("LINE", 1, INC=1, MOD=3, T0=1, T1=0xFFFF, T2=0xFFFF)
    for o in (8, 10, 11, 12, 13):
        s.blk("OUT", o, BIND=0b100, SEL=(o % 4) | ((o + 1) % 4) << 2 | ((o + 2) % 4) << 4,
              LUT=0x9A5C3F61 ^ (o * 0x01110111))
    s.blk("OUT", 9, BIND=0b101, LUT=lut(lambda i: i & 1))
    s.program(0, [I(("IMM", "ACC.ADD"), ("ACC", "L.SYM"), ("ZERO", "P0.R"), imm=3),
                  I(("P0.D", "R1"), ("IMM", "FLAGS.SET"), ("ACC", "R2"), imm=1, pause=1),
                  I(("IMM", "FLAGS.CLR"), ("R1", "HOST.OUT"), imm=1, pause=1)])
    # core 1, pc 1..: a 10-word burst for doorbell thread 3 whose LFSR result depends on every word executing once in
    # order (a freeze or step inside it must hold IR, XV, RV and FPC), reported through HOST.OUT
    burst = [I(("IMM", "LF1.ST"), ("IMM", "ACC.XOR"), imm=(0x35 * k + 1) & 0xFF) for k in range(9)]
    s.program(1, [I(("S0.BIT", "L.DBIT"), ("ZERO", "S0.ADV"), pause=1)] + burst
              + [I(("LF1.B0", "ACC.XOR"), ("LF1.B1", "R3"), pause=1, jmode="always", imm=1)])
    s.blk("LFSR", 1, POLY=0xEDB88320)
    s.thread(0, core=0, line=0, trig="L0.BEAT", pc=0)
    s.thread(1, core=0, line=0, trig="FLAG0.RISE", pc=2)
    s.thread(2, core=1, line=1, trig="L1.TAP0", pc=0)
    s.thread(3, core=1, line=0, trig="NONE", pc=1)


# ==================================================================================================== 12.1 + 12.2
def v3_live_misr():
    """Live-pin tables on a wired-AND loopback (read-back, collision flag, pass-through), with the digest enabled,
    read, cleared, paused and read again."""
    s = Scn("v3_live_misr")
    s.reset()
    s.blk("DBG", MCTL=1)                                   # digest on from the start (all pins idle)
    s.blk("LINE", 0, INC=1, MOD=8, T0=0, T1=4, T2=6, PINS=0 | (1 << 4))     # PINA = P0, PINB = P1
    # O0: open-drain data bit (COMMITTED[0]); drive low only when the data bit is 0 (OE), never drive high
    s.blk("OUT", 0, BIND=0b100 | (1 << 3), SEL=0, LUT=0, OE=lut(lambda i: 1 - (i & 1)))
    # O1: collision: data bit 1 (released) but the wire reads low -> drive 1 (b2 = live PINA)
    s.blk("OUT", 1, BIND=0b100 | (1 << 3), SEL=0, LUT=lut(lambda i: (i & 1) & (1 - ((i >> 2) & 1))), OE=0xFFFFFFFF)
    # O8: pass-through of P1 (b1 = live PINB); O9: both live bits plus SEG
    s.blk("OUT", 8, BIND=0b100 | (2 << 3), LUT=lut(lambda i: (i >> 1) & 1))
    s.blk("OUT", 9, BIND=0b100 | (3 << 3), LUT=lut(lambda i: ((i >> 1) ^ (i >> 2) ^ (i >> 3)) & 1))
    s.blk("OUT", 2, BIND=0b100, SEL=1, LUT=lut(lambda i: i & 1), OE=0xFFFFFFFF)             # LIVE = 0 reference
    s.program(0, [I(("IMM", "ACC.ADD"), ("ACC", "L.SYM"), imm=5, pause=1)])
    s.thread(0, core=0, line=0, trig="L0.BEAT", pc=0)
    s.blk("CTRL", RUN=1)
    s.blk("LRT", 0, CTL=1)
    rnd = random.Random(31)
    ext = {"p0": 1, "p1": 0}

    def pins(t, o, r=rnd, st=ext):
        _, uio_out, uio_oe = o
        if r.randrange(9) == 0:
            st["p0"] ^= 1                                  # another device pulls the wire low at times
        if r.randrange(5) == 0:
            st["p1"] ^= 1
        wire = st["p0"] & (0 if ((uio_oe & 1) and not (uio_out & 1)) else 1)
        return wire | (st["p1"] << 1)
    s.uio = pins
    s.idle(400)
    s.read(HM["DBG_BASE"] + 4, 4)                          # MISR mid-run
    s.blk("DBG", MCTL=0)                                   # pause
    s.idle(97)
    s.read(HM["DBG_BASE"] + 4, 4)
    s.blk("DBG", MCTL=1)
    s.idle(300)
    s.blk("DBG", MCTL=3)                                   # clear and keep running
    s.idle(211)
    readback_dbg(s)
    s.readback_all()
    return s


# ==================================================================================================== 12.3
def v3_freeze():
    """Freeze over SPI while lines, threads, a transmit stream and a pointer loop run; while frozen: debug readback,
    host data RAM reads and writes, a PHASE write, a doorbell (held), configuration writes; then single steps
    (each followed by a CST/FPC read), unfreeze, and the digest over the whole run."""
    s = Scn("v3_freeze")
    s.reset()
    busy_programs(s)
    s.blk("DBG", MCTL=1)
    s.blk("CTRL", RUN=1)
    s.blk("LRT", 0, CTL=1)
    s.blk("LRT", 1, CTL=1)
    s.uio = lambda t, o: ((t // 7) & 0x10) | ((t // 11) & 0x04)
    s.idle(150)
    for rnd_n in range(3):
        s.blk("DBG", DBG=1)                                # freeze
        readback_dbg(s)
        s.read(HM["DATA_BASE"], 6)                         # host RAM read while frozen
        s.data(0x08 + rnd_n, [0xA0 + rnd_n])               # host RAM write while frozen
        s.blk("CTRL", DOORBELL=1 << 3)                     # held until the first unfrozen cycle
        if rnd_n == 1:
            s.blk("LRT", 0, PHASE=2)
            s.blk("OUT", 12, LUT=0x12345678)               # configuration still latches (W+2)
        for _ in range((4, 14, 6)[rnd_n]):              # round 1 steps through thread 3's whole burst
            s.blk("DBG", DBG=3)                            # step one cycle
            s.read(HM["DBG_BASE"] + 0x0E, 4)               # CST, FPC
        s.read(HM["LRT_BASE"], 6)
        s.blk("DBG", DBG=0)                                # resume
        s.idle(37 + 23 * rnd_n)
    s.idle(100)
    readback_dbg(s)
    s.readback_all()
    s.read(HM["DATA_BASE"], 16)
    return s


# ==================================================================================================== 12.4
def v3_ecap():
    """Edge capture on S0 with a receive stream on S1 and pointer reads competing for the RAM: a burst of edges
    every cycle, simultaneous edges, masked pins, edges during a freeze, END; then the records and POS read back."""
    s = Scn("v3_ecap")
    s.reset()
    s.blk("STREAM", 0, MODE=1, START=0x200, LEN=4 * 48)
    s.blk("STREAM", 1, MODE=1, START=0x600, LEN=40)
    s.blk("SRT", 0, CTL=1)
    s.blk("SRT", 1, CTL=1)
    s.blk("LINE", 1, INC=1, MOD=3, T0=1, T1=0xFFFF, T2=0xFFFF, PINS=4)
    s.program(1, [I(("PINS.LO", "S1.RX"), ("ZERO", "P0.R"), ("P0.D", "R0"), pause=1)])
    s.thread(0, core=1, line=1, trig="L1.TAP0", pc=0)
    s.blk("DBG", EMASK=0b00111, ECTL=1, MCTL=1)            # P0, P1, P2; P3 and up masked
    s.blk("SRT", 0, CTL=1)                                 # rewind with CEN set (12.4)
    s.blk("CTRL", RUN=1)
    s.blk("LRT", 1, CTL=1)
    st = {"v": 0, "t": 0}
    plan = {}
    for t in range(20, 36):
        plan[t] = 0b1                                      # P0 every cycle for 16 cycles
    plan.update({60: 0b11, 61: 0b100, 75: 0b1000, 76: 0b1000, 90: 0b101, 200: 0b10, 1300: 0b1})

    def pins(t, o, st=st):
        k = st["t"]
        st["t"] += 1
        st["v"] ^= plan.get(k - 400, 0) if k >= 400 else 0
        if 400 <= k and (k - 400) % 53 == 0 and k < 1200:
            st["v"] ^= 0b1100                              # P2 and P3 together: one record
        return st["v"] & 0xFF
    s.uio = pins
    s.idle(700)
    s.blk("DBG", DBG=1)
    s.idle(30)                                             # edges here are not seen
    s.blk("DBG", DBG=0)
    s.idle(600)
    s.read(HM["SRT_BASE"], 2)
    s.read(HM["DATA_BASE"] + 0x200, 4 * 48)
    s.read(HM["SRT_BASE"] + 4, 2)
    s.blk("SRT", 0, CTL=0x81)                              # rewind, clear STARVED
    s.idle(40)
    readback_dbg(s)
    s.readback_all()
    return s


def random3_scn(seed):
    """random_scn with v3 features mixed in from a separate generator (the v2 draws are unchanged): LIVE bits on
    every pin, the digest on, edge capture on S0 with a random mask, and random freezes with single steps."""
    s = random_scn(seed, run_cycles=0)
    s.name = f"random3_{seed}"
    r3 = random.Random(seed * 1009 + 7)
    for o in range(m.N_OUT_PINS):
        s.blk("OUT", o, BIND=r3.randrange(32))
    s.blk("DBG", MCTL=1, EMASK=r3.getrandbits(13), ECTL=int(r3.random() < 0.7))
    s.blk("SRT", 0, CTL=1)
    done = 0
    while done < 3000:
        n = r3.randint(40, 300)
        s.idle(n)
        done += n
        r = r3.random()
        if r < 0.3:
            s.blk("DBG", DBG=1)
            s.idle(r3.randint(0, 30))
            for _ in range(r3.randint(0, 4)):
                s.blk("DBG", DBG=3)
            if r3.random() < 0.5:
                s.read(HM["DATA_BASE"] + r3.randrange(2048), r3.randint(1, 4))
            readback_dbg(s)
            s.blk("DBG", DBG=0)
        elif r < 0.45:
            s.read(HM["DBG_BASE"] + 4, 4)
        elif r < 0.55:
            s.blk("OUT", r3.randrange(14), BIND=r3.randrange(32))
        elif r < 0.62:
            s.blk("CTRL", DOORBELL=r3.getrandbits(6))
        elif r < 0.7:
            s.blk("SRT", 0, CTL=r3.choice([1, 0x81]))
    readback_dbg(s)
    s.readback_all()
    return s


def v3_freeze2():
    """Short freeze edge cases (review follow-up): a pointer read served in a step cycle lands in the following frozen
    cycle while a host RAM read replaces the RAM output (landing exception, 12.3); MISR read while frozen, after a
    step and after more frozen cycles (12.2); CEN toggled and S0 rewound inside the freeze, DC restart (12.4)."""
    s = Scn("v3_freeze2")
    s.reset()
    s.data(0x000, [(0x11 * i + 3) & 0xFF for i in range(256)])
    s.data(0x700, [0xE7, 0x5D, 0xB2, 0x49])
    s.blk("LINE", 0, INC=1, MOD=5, T0=0, T1=2, T2=0xFFFF)
    for o in (8, 9, 10):
        s.blk("OUT", o, BIND=0b100, LUT=lut(lambda i, o=o: ((i >> 3) + o) & 1))
    s.blk("OUT", 0, BIND=0b100, LUT=lut(lambda i: (i >> 4) & 1), OE=lut(lambda i: (i >> 3) & 1))
    # ALWAYS thread: P0 read every burst, landed byte folded into ACC (visible through DBG.ACC)
    s.program(0, [I(("P0.D", "ACC.XOR"), ("ACC", "P0.AL"), ("ACC", "R0"), pause=1, jmode="always", imm=0)])
    s.thread(0, core=0, line=0, trig="ALWAYS", pc=0)
    s.blk("STREAM", 0, MODE=1, START=0x400, LEN=4 * 16)
    s.blk("DBG", MCTL=1, EMASK=1, ECTL=1)
    s.blk("SRT", 0, CTL=1)
    s.blk("CTRL", RUN=1)
    s.blk("LRT", 0, CTL=1)
    s.uio = lambda t, o: (t // 9) & 1
    s.idle(60)
    s.blk("DBG", DBG=1)                                    # freeze
    s.read(HM["DBG_BASE"] + 4, 4)                          # MISR frozen
    s.idle(40)
    s.read(HM["DBG_BASE"] + 4, 4)                          # unchanged
    for k in range(12):
        s.blk("DBG", DBG=3)                                # one cycle; may serve a P0 read
        s.read(HM["DATA_BASE"] + 0x700 + (k & 3), 1)       # host read replaces the RAM output while frozen
        if k % 4 == 3:
            s.read(HM["DBG_BASE"] + 4, 4)                  # MISR after steps
            s.read(HM["DBG_BASE"] + 0x0A, 1)               # ACC
    s.blk("DBG", ECTL=0)                                   # CEN off and on, S0 rewound, all inside the freeze
    s.blk("DBG", ECTL=1)
    s.blk("SRT", 0, CTL=1)
    s.blk("DBG", DBG=0)
    s.idle(120)
    s.read(HM["DBG_BASE"] + 4, 8)                          # MISR, EMASK
    s.read(HM["DBG_BASE"] + 0x0A, 1)
    s.read(HM["SRT_BASE"], 2)
    s.read(HM["DATA_BASE"] + 0x400, 24)
    return s


DIRECTED_V3 = {"v3_live_misr": v3_live_misr, "v3_freeze": v3_freeze, "v3_ecap": v3_ecap, "v3_freeze2": v3_freeze2}
