"""Receiver template for roles whose beat is made from the chip clock and started or re-aligned by edges
(`started by`, `recovered from`; SPEC A 5.2, B 3.2): UART receive, Manchester receive.

One thread, one burst per received beat, walking the frame as a state machine.  Two ways to be woken:

* `started`   the thread is triggered by the sample tap; `L.IN` is the snapshot taken in that very cycle.
* `recovered` the thread is triggered by the beat boundary with the snapshot taken *at the boundary*, so it reads
  the sample of the beat that just ended; `L.SYNC` says whether an edge was accepted during that beat, which is how
  "no edge for one beat" (end of frame) is recognised.  The first beat after the starting edge has no `SYNC`
  history, and the compiled frame never consults it there (the frame starts with a fixed-length part).
"""
from __future__ import annotations

import random

from score.model import DATA_SYMBOL

from .ctx import CONST_BASE, RX_BASE, Ctx, emit_init_thread, emit_threads
from .emit import imm
from .flatten import Step, crc_range, field_bits
from .plan import CompileError, plan_rx

F_MISMATCH, F_VIOL, F_CRC = 0, 1, 2     # flag numbers; flag 0 is the one `ZERO` names, used in the tightest burst


def _rev(v, w):
    return int(f"{v:0{w}b}"[::-1], 2)


SIG_POLY = 0x04C11DB7


def sig_state(bits):
    """Register of the signature LFSR (LFSR 1, reflected Galois over SIG_POLY, loaded with 0) after `bits`."""
    pol, s = _rev(SIG_POLY, 32), 0
    for b in bits:
        s = (s >> 1) ^ (pol if ((s ^ b) & 1) else 0)
    return s


def lfsr_residue(width, poly, init, xorout, nbits=64):
    """State of the bit-serial reflected-Galois LFSR (SPEC B 6.1, as the assembler loads it) after it has been fed a
    message followed by that message's own crc as transmitted.  Constant for the supported crcs: asserted."""
    pol, st0 = _rev(poly, width), _rev(init, width)
    full = (1 << width) - 1
    outs = set()
    for seed in range(4):
        rng = random.Random(seed)
        s = st0
        for _ in range(nbits):
            b = rng.randrange(2)
            s = (s >> 1) ^ (pol if ((s ^ b) & 1) else 0)
        xo = _rev(xorout, width)
        t, crcbits = s, []
        for i in range(width):                      # shift the state out; bit i is S[0] ^ (reflected xorout)[i]
            crcbits.append((t & 1) ^ ((xo >> i) & 1))
            t >>= 1
        for b in crcbits:
            s = (s >> 1) ^ (pol if ((s ^ b) & 1) else 0)
        outs.add(s & full)
    if len(outs) != 1:
        raise CompileError("E-UNSUPPORTED", "crc residue is not a constant")
    return outs.pop()


def recovered_params(x: Ctx, rc):
    """Re-alignment parameters of a recovered line (SPEC A 5.2, SPEC B 3.2 and 10.4).

    Mid-beat edges arrive s cycles apart, s between S_MIN and S_MAX (the beat, plus or minus the clock tolerance, plus
    one cycle of quantisation).  Each accepted edge loads PRE, so with PH(a+1) = PRE after an edge seen in cycle a, the
    next edge, seen in cycle a+s, finds PH = PRE + (s-1)*INC - MOD (the generator wraps once in between, which is the
    BEAT).  Taking PRE = MOD - (S_MIN-1)*INC puts the earliest edge at phase 0, so the window is
    [0, (S_MAX-S_MIN)*INC].  The sample tap sits K cycles after the accepted edge, T = PRE + K*INC, and SPEC B 10.4
    needs T > WHI + INC, that is MOD > INC*(S_MAX-K).  The generator is therefore made a little longer than the
    sender's beat (MOD = INC*(S_MAX-K)+1); the window, not the beat length, is what follows the sender.
    Edges between equal Manchester cells (half a beat after a mid-beat edge) arrive at phase PRE + (s/2-1)*INC, above
    the window, and are ignored."""
    import math
    clk = x.clk
    clock = x.score.clock_for()
    P = float(clk.period)
    a, b = rc.win
    center = (float(a) + float(b if b >= a else b + 1)) / 2.0
    samp = float(next(t for t in x.taps if "sample" in t.why).frac)
    m = max(1, math.ceil(P * float(clock.tolerance)))
    s_min, s_max = int(math.floor(P)) - m, int(math.ceil(P)) + m
    k = max(1, int(math.floor(((samp - center) % 1.0) * P)))
    inc = 16
    mod = inc * (s_max - k) + 1
    pre = mod - (s_min - 1) * inc
    wlo, whi = 0, (s_max - s_min) * inc
    T = pre + k * inc
    if s_min < 3 or mod > 0xFFFF or T >= mod:
        raise CompileError("E-FIT-TAP", f"clock: a beat of {P:g} cycles is too short to re-align on edges {m} cycle(s) "
                                        f"either side of nominal and still sample {k} cycle(s) after the edge "
                                        f"(SPEC B 10.4: the capture tap must follow the window)")
    note = (f"re-alignment: edges {s_min}..{s_max} cycles apart accepted (window phase {wlo}..{whi} of MOD {mod}), "
            f"generator beat {mod / inc:.4f} cycles, sample {k} cycle(s) after the accepted edge "
            f"(asked {((samp - center) % 1.0) * P:.2f})")
    return pre, wlo, whi, T, inc, mod, note


class RxGen:
    def __init__(self, x: Ctx):
        self.x = x
        self.c = x.b.cores[0]
        self.n = 0
        self.crc = None
        self.covered: set = set()
        self.rxs = 0                 # receive stream index
        self.const_bytes = b""
        self.const_bits: list = []
        self.used_flags: set = set()

    def lab(self, tag=""):
        self.n += 1
        return f"R{self.n}{tag}"

    def setflag(self, f):
        self.used_flags.add(f)
        return imm(f, "FLAGS.SET")

    def rx_stream(self, name):
        x = self.x
        if x.host["rx_stream"] is None:
            x.host["rx_stream"] = {"stream": self.rxs, "base": RX_BASE, "fields": []}
        x.host["rx_stream"]["fields"].append(name)

    # ---- steps --------------------------------------------------------------------------------------------------
    def sym_expect(self, s: Step, last_inline=False):
        x, c = self.x, self.c
        rxp = x.rxp
        if s.name != DATA_SYMBOL or rxp.data_param is None:
            raise CompileError("E-UNSUPPORTED", f"receive of symbol '{s.name}' as a grammar terminal")
        if s.count > 1:
            raise CompileError("E-UNSUPPORTED", f"expect '{s.name}' repeated {s.count} times")
        v = s.args[rxp.data_param]
        c.label(self.lab())
        # a violation unless IN == v: IN0 != v, or (when the tables can report one) IN1 set
        c.i([f"{'?' if v == 0 else '!'} {self.setflag(F_VIOL)}"], when="L.IN0", note=f"expect {s.name}({v})")
        if rxp.lut1:
            c.i([f"? {self.setflag(F_VIOL)}"], when="L.IN1")
        if not last_inline:
            c.i([], pause=True)

    def field_capture(self, s: Step, w, feed):
        c = self.c
        c.label(self.lab())
        self.rx_stream(s.f.name)
        S = self.rxs
        mv = [f"L.IN -> S{S}.RX"] + ([f"L.IN -> LF{feed}.ST"] if feed is not None else [])
        if w == 1:
            c.i(mv, pause=True, note=f"capture {s.f.name}")
            return
        c.i(mv + [imm(w - 2, "CNT0.LO")], pause=True, note=f"capture {s.f.name}: bit 1 of {w}")
        ll = self.lab("l")
        c.label(ll)
        c.i(mv + ["ZERO -> CNT0.DEC"], goto=ll, jmode="ifnot", jcond="CNT0.Z", pause=True)

    def const_expect(self, s: Step):
        """A constant prefix (preamble, sync word) is checked by signature: every received bit steps LFSR 1 (a 32-bit
        CRC register, loaded with 0), and after the frame the register must equal the signature of the expected
        bits.  One instruction per beat, so it fits beats of 5-6 cycles; a wrong bit survives with probability
        2^-32 (calculated)."""
        c, x = self.c, self.x
        if not s.data:
            raise CompileError("E-UNSUPPORTED", "const bits other than whole bytes in a receive frame")
        order = x.order
        for byte in s.data:
            self.const_bits += [(byte >> i) & 1 for i in (range(8) if order == "lsb" else range(7, -1, -1))]
        n = len(s.data) * 8
        c.label(self.lab())
        mv = ["L.IN -> LF1.ST"]
        if n == 1:
            c.i(mv, pause=True, note="const: bit into the signature register")
            return
        c.i(mv + [imm(n - 2, "CNT0.LO")], pause=True, note=f"const {n} bits: bit 1 into the signature register")
        ll = self.lab("l")
        c.label(ll)
        c.i(mv + ["ZERO -> CNT0.DEC"], goto=ll, jmode="ifnot", jcond="CNT0.Z", pause=True)

    def bytes_until_eof(self, s: Step, feed):
        x, c = self.x, self.c
        if x.clk.mode != "recovered":
            raise CompileError("E-UNSUPPORTED", "'bytes until' needs an end-of-frame event; only 'no edge for N beats' "
                                                "on a recovered clock is compiled")
        c.label(self.lab())
        self.rx_stream(s.f.name)
        S = self.rxs
        mv = [f"? L.IN -> S{S}.RX"] + ([f"? L.IN -> LF{feed}.ST"] if feed is not None else [])
        ll = self.lab("l")
        c.label(ll)
        c.i(mv, when="L.SYNC", goto=ll, jmode="if", jcond="L.SYNC", pause=True,
            note=f"{s.f.name}: until a beat with no edge")


def _taps_text(x):
    ts = ["-", "-", "-"]
    for t in x.taps:
        ts[t.idx] = str(t.T)
    return " ".join(ts)


def _close_loop(c, first):
    """End of the receive tail: one more instruction, in the same burst as the last one, returns to the first state."""
    for i in range(len(c.items) - 1, -1, -1):
        kind, v = c.items[i]
        if kind == "insn":
            v.pause = False
            break
    c.i([], goto=first, pause=True)


def compile_rx(x: Ctx):
    clk, score = x.clk, x.score
    rc = score.clock_for().roles[x.role]
    wire = rc.wire
    if wire not in x.bind or x.bind[wire][0] is None:
        raise CompileError("E-BIND", f"wire '{wire}' (the clock of role {x.role}) needs an input pin P<k>")
    pin = x.bind[wire][0]
    mode = clk.mode
    sample_taps = [t for t in x.taps if "sample" in t.why]
    if len(sample_taps) != 1 or len(x.slots) < 3:
        raise CompileError("E-UNSUPPORTED", "receive template needs exactly one sample point on one wire")
    g = RxGen(x)
    c = g.c
    inc, mod = clk.inc, clk.mod
    frame = x.frame
    crc_steps = [s for s in frame if s.kind == "field" and s.f.type.kind == "crc"]
    if crc_steps:
        d = x.crc_decl(crc_steps[0].f.type.crc)
        if not (d.refin == d.refout == (x.order == "lsb")):
            raise CompileError("E-UNSUPPORTED", f"crc '{d.name}': refin/refout must equal the bit order to run bit-serially")
        g.crc = d
        g.covered = crc_range(frame, crc_steps[0].f)
    has_const = any(s.kind == "const" for s in frame)
    g.rxs = 0
    st = sample_taps[0]
    wlo = whi = None
    if mode == "started":
        pre = 3 * inc
    else:
        pre, wlo, whi, T, inc, mod, note = recovered_params(x, rc)
        st.T = T
        x.notes.append(note)
    rx_snap = f"tap{st.idx}" if mode == "started" else "beat"
    x.rxp = plan_rx(score, x.role, x.taps, x.slots, x.bind, rx_snap)
    r = x.rxp
    inline_tail = mode == "started"
    active = [s for s in frame if not (s.kind == "gap" or (s.kind == "field" and s.f.type.kind == "crc"))]
    cut = len(active)                                  # steps after the until-eof field are not observed
    for i, s in enumerate(active):
        if s.kind == "field" and s.f.type.kind == "bytes" and s.f.type.until:
            cut = i + 1
    active = active[:cut]
    for i, s in enumerate(active):
        last = i == len(active) - 1
        if s.kind == "sym":
            g.sym_expect(s, last_inline=inline_tail and last)
        elif s.kind == "const":
            g.const_expect(s)
        elif s.kind == "field":
            t = s.f.type
            if s.f.value is not None:
                raise CompileError("E-UNSUPPORTED", f"field '{s.f.name}': a computed value on the receive side")
            feed = 0 if (g.crc and (s.f.name in g.covered)) else None
            w = field_bits(s)
            if t.kind == "bytes" and t.until:
                g.bytes_until_eof(s, 0 if g.crc else None)
            elif w is not None:
                g.field_capture(s, w, feed)
            else:
                raise CompileError("E-UNSUPPORTED", f"field '{s.f.name}': variable length without an end event")
        else:
            raise CompileError("E-UNSUPPORTED", f"step '{s.describe()}' in a receive frame")
    # ---- frame end: crc check, status to the host, re-arm, housekeeping.  With short beats every burst is cut to a
    # few instructions (one per beat); the line keeps running for the beats it needs, well inside the inter-frame gap.
    ctl_arm = 2 if mode == "started" else 6
    x.host["mailbox_out"].append("frame status byte (bit0 const mismatch, bit1 violation, bit2 crc error), 0 = frame ok")
    short = (not inline_tail) and clk.period is not None and float(clk.period) < 40
    c.label("end")
    tail_beats = 0

    def emit(moves, **kw):
        nonlocal tail_beats
        c.i(moves, pause=short or kw.pop("pause", False), **kw)
        tail_beats += 1 if short else 0

    if g.crc:
        d = g.crc
        res = lfsr_residue(d.width, d.poly, d.init, d.xorout)
        for k in range((d.width + 7) // 8):
            emit([f"LF0.B{k} -> ACC.LD"])
            emit([imm((res >> (8 * k)) & 0xFF, "ACC.XOR")])
            emit([f"! {imm(F_CRC, 'FLAGS.SET')}"], when="ACC.Z", note="LFSR state != residue: crc error")
            g.used_flags.add(F_CRC)
    if has_const:
        sig = sig_state(g.const_bits)
        for k in range(4):
            emit([f"LF1.B{k} -> ACC.LD"])
            emit([imm((sig >> (8 * k)) & 0xFF, "ACC.XOR")])
            emit([f"! {g.setflag(F_MISMATCH)}"], when="ACC.Z", note="signature of the received const bits != expected")
    emit(["? FLAGS.LO -> HOST.OUT"], when="HOST.OUTE", note="frame status to the host mailbox")
    hk = []
    if g.crc:
        init = _rev(g.crc.init, g.crc.width)
        for k in range((g.crc.width + 7) // 8):
            hk.append(imm((init >> (8 * k)) & 0xFF, f"LF0.B{k}"))
    if has_const:
        for k in range(4):
            hk.append(f"ZERO -> LF1.B{k}")
    for f in sorted(g.used_flags):
        hk.append(imm(f, "FLAGS.CLR"))
    for mv in hk:
        emit([mv])
    emit([imm(ctl_arm, "L0.CTL")], note="stop the line and re-arm for the next start edge (last: the line must keep "
                                          "running, it is what wakes the thread for every tail burst)")
    x.notes.append(f"end-of-frame work: {tail_beats if short else 'one burst'} beats after the frame" if short else
                   "end-of-frame work runs in the burst of the last beat")
    _close_loop(c, "R1")
    # ---- configuration
    line = [f"inc {inc}", f"mod {mod}", f"taps {_taps_text(x)}", f"preset {pre}"]
    pol = rc.edge if mode == "started" else "both"
    line.append(f"edge P{pin} {pol}")
    if mode == "recovered":
        line.append(f"window {wlo} {whi}")
    line.append(f"pins A=P{r.pina}" + (f" B=P{r.pinb}" if r.pinb is not None else ""))
    line.append(f"lut0 0x{r.lut0:08X}")
    line.append(f"lut1 0x{r.lut1:08X}")
    line.append(f"snap {rx_snap}")
    line.append("ctl arm" if mode == "started" else "ctl arm ren")
    x.b.block(".line 0", line)
    trig = f"L0.TAP{st.idx}" if mode == "started" else "L0.BEAT"
    S = g.rxs
    x.b.block(f".stream {S}", ["mode rx", f"order {'msb' if x.msb else 'lsb'}", f"start {RX_BASE}",
                               f"len {CONST_BASE - RX_BASE}"])
    if has_const:
        x.b.cfg.append(f".lfsr 1 poly=0x{SIG_POLY:X} width=32 init=0")
    if g.crc:
        d = g.crc
        x.b.cfg.append(f".lfsr 0 poly=0x{d.poly:X} width={d.width} init=0x{d.init:X}")
        init = _rev(d.init, d.width)
        for k in range((d.width + 7) // 8):
            x.init_moves.append(imm((init >> (8 * k)) & 0xFF, f"LF0.B{k}"))
    x.b.cfg.append("")
    emit_threads(x, [(0, 0, 0, trig, "R1")])
    emit_init_thread(x, 5)
    if x.host["rx_stream"]:
        x.host["rx_stream"]["capacity_bytes"] = CONST_BASE - RX_BASE
