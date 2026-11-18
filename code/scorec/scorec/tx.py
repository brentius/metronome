"""Sender template: a generated beat clock and one thread per beat walking the frame as a state machine.

Timing model of every burst (SPEC B 5, 10): the burst triggered by boundary k stages the symbol of beat k+1, which is
committed at boundary k+1.  Each step of the frame has an *enter* burst (stages the step's first beat, sets counters
up) and, for a multi-beat step, loop bursts, one per further beat.  A loop is checked with a jump on the state its own
burst produced (`pause goto L ifnot COND`), so a loop of n beats costs n bursts and the exit falls through into the
next step, whose enter burst stages the first beat after the loop.
"""
from __future__ import annotations

from score.model import DATA_SYMBOL

from .ctx import CONST_BASE, RX_BASE, TX_BASE, Ctx, emit_init_thread, emit_out_pins, emit_threads
from .emit import imm
from .flatten import Step, crc_range, field_bits, gap_beats
from .plan import CompileError


def _rev(v, w):
    r = 0
    for i in range(w):
        if v >> i & 1:
            r |= 1 << (w - 1 - i)
    return r


class TxGen:
    def __init__(self, x: Ctx):
        self.x = x
        self.c = x.b.cores[0]
        self.n = 0
        self.kind_bit = False        # does the staged symbol already carry the data family's kind?
        self.gate = 0                # beats of capture-gate bookkeeping owed after a full-duplex loop
        # Runtime shifter state.  Reset LEN=0 means eight bits, LSB first.
        self.cfg_sh: dict = {"SH0": (8, False)}
        self.crc = None              # CrcDecl of the frame's crc field
        self.covered: set = set()    # field names fed to the LFSR
        self.stream_tx = False
        self.const_bytes = b""
        self.mailbox = False
        self.dup = None              # (own field step, peer field step) of a || pair
        self.hk: list = []           # housekeeping moves, one per idle beat after the frame
        self.fuse_first = False

    # ---- helpers ------------------------------------------------------------------------------------------------
    def lab(self, tag=""):
        self.n += 1
        return f"S{self.n}{tag}"

    def codes(self):
        t = self.x.txp
        if not t.family_codes:
            raise CompileError("E-NAMES", f"role {self.x.role}: no data symbol '{DATA_SYMBOL}' to carry coded bits")
        if t.family_k != 1:
            raise CompileError("E-UNSUPPORTED", f"role {self.x.role}: the data symbol '{DATA_SYMBOL}' carries "
                                                f"{t.family_k} relevant data bits per beat; the sender drives exactly one")
        return t.family_codes[(0,)], t.family_codes[(1,)]

    def cnt(self, p):
        c = self.c
        c.i([imm(p & 0xFF, "CNT0.LO")])
        if p > 255:
            c.i([imm(p >> 8, "CNT0.HI")])

    def gate_move(self):
        """Capture-gate bookkeeping owed to this burst (flag 0, the gate of the full-duplex capture thread)."""
        if self.gate == 2:
            self.gate -= 1
            return ["ZERO -> FLAGS.SET"]
        if self.gate == 1:
            self.gate -= 1
            return ["ZERO -> FLAGS.CLR"]
        return []

    def stage(self, src, guard, extra=(), invert=False, loop_label=None):
        """Instructions that stage the coded bit read from port `src` (`guard`: the same bit as a condition).

        L.DBIT writes symbol bit 0 only, so it is used when the two data codes differ in that bit alone and the
        staged symbol already has the data kind; otherwise the code of bit 0 is written and L.XOR flips it."""
        c = self.c
        c0, c1 = self.codes()
        invert = bool(invert) ^ bool(self.x.score.bits.invert)   # `bits ..., invert` complements every coded bit (6)
        a, b = (c1, c0) if invert else (c0, c1)           # staged code for bit value 0 / 1
        # the inverted single-bit form costs two moves; with two extra moves it would exceed 3 per instruction
        if (a ^ b) == 1 and not ((a & 1) and len(extra) > 1):
            if not self.kind_bit:
                c.i([imm(a, "L.SYM")])
                self.kind_bit = True
            if loop_label:
                c.label(loop_label)
            if (a & 1) == 0:                      # bit value 1 stages symbol bit 0 = 1: copy the bit
                c.i([f"{src} -> L.DBIT", *extra])
            else:                                 # inverted: the bit value 0 stages symbol bit 0 = 1
                c.i(["? ZERO -> L.DBIT", "! #1 -> L.DBIT", *extra], when=guard)
        else:
            if loop_label:
                c.label(loop_label)
            c.i([imm(a, "L.SYM")])
            c.i([f"? {imm(a ^ b, 'L.XOR')}", *extra], when=guard)
            self.kind_bit = True

    def check(self, label, jcond=None, counter=False):
        c = self.c
        if counter:
            c.i(["ZERO -> CNT0.DEC"], goto=label, jmode="ifnot", jcond="CNT0.Z", pause=True)
        else:
            c.i([], goto=label, jmode="ifnot", jcond=jcond, pause=True)

    # ---- steps --------------------------------------------------------------------------------------------------
    def sym(self, s: Step):
        x, c = self.x, self.c
        name = f"{s.name}({','.join(map(str, s.args))})" if s.args else s.name
        code = x.txp.code_of[name]
        c.label(self.lab())
        g = self.gate_move()
        if s.count == 1:
            c.i([imm(code, "L.SYM"), *g], pause=True, note=f"stage {name}")
        else:
            c.i([imm(code, "L.SYM"), *g], note=f"stage {name} x{s.count}")
            self.cnt(s.count - 1)
            ll = self.lab("l")
            c.label(ll)
            self.check(ll, counter=True)
        self.kind_bit = s.name == DATA_SYMBOL

    def mailbox_field(self, s: Step, w, feed):
        x, c = self.x, self.c
        c.label(self.lab())
        self.mailbox = True
        x.host["mailbox_in"].append(s.f.name)
        if x.msb and w < 8:
            # Host bytes are right-aligned; shift them into the MSB positions after loading.
            cfg = (8, True)
        else:
            cfg = (w, x.msb)
        if self.cfg_sh["SH0"] != cfg:
            # Runtime CFG commits on this instruction's write edge. D31 makes a
            # simultaneous LD consume the old configuration, so LD follows in
            # the next instruction; no idle instructions are needed here.
            c.i([imm((cfg[0] & 0xF) | (0x10 if cfg[1] else 0), "SH0.CFG")],
                note=f"configure {s.f.name} shifter width")
            self.cfg_sh["SH0"] = cfg
        c.i(["HOST.IN -> SH0.LD"], note=f"{s.f.name}: byte from the host mailbox")
        if x.msb and w < 8:
            # MSB mode shifts out from bit 7, but the host writes the value right-aligned: shift it up first.  LEN is
            # 8 so DONE comes after the (8 - w) alignment shifts plus the w data shifts.
            for _ in range(8 - w):
                c.i(["ZERO -> SH0.SH"], note="align a narrow msb-first field")
        ll = self.lab("l")
        extra = ["ZERO -> SH0.SH"] + ([f"SH0.O -> LF{feed}.ST"] if feed is not None else [])
        self.stage("SH0.O", "SH0.OUT", extra, loop_label=ll)
        self.check(ll, jcond="SH0.DONE")

    def stream_field(self, s: Step, w, feed, variable):
        x, c = self.x, self.c
        c.label(self.lab())
        self.stream_tx = True
        if x.host["tx_stream"] is None:
            x.host["tx_stream"] = {"stream": 0, "base": TX_BASE, "fields": []}
        x.host["tx_stream"]["fields"].append(s.f.name)
        ll = self.lab("l")
        extra = ["ZERO -> S0.ADV"] + ([f"S0.BIT -> LF{feed}.ST"] if feed is not None else [])
        if variable:
            self.stage("S0.BIT", "S0.BIT", extra, loop_label=ll)
            self.check(ll, jcond="S0.END")
        else:
            p = w - 1
            if p:
                self.cnt(p)
            self.stage("S0.BIT", "S0.BIT", extra, loop_label=ll)
            if p:
                self.check(ll, counter=True)
            else:
                c.i([], pause=True)

    def star_duplex(self, s: Step):
        """`{ own || peer }*`: one stream bit staged per beat until the stream ends; the capture thread (core 1) is
        gated by flag 0, which this state machine keeps equal to 'the beat on the wire carries a data bit'."""
        x, c = self.x, self.c
        if len(s.body) != 1 or s.body[0].kind != "dup":
            raise CompileError("E-UNSUPPORTED", "a repeated block must be one '||' pair of byte fields")
        side = s.body[0].sides
        own = [t for t in side if len(t) == 1 and t[0].kind == "field" and t[0].owner == x.role]
        peer = [t for t in side if len(t) == 1 and t[0].kind == "field" and t[0].owner != x.role]
        if not own or not peer:
            raise CompileError("E-UNSUPPORTED", "'||' sides must be one field each")
        f_own, f_peer = own[0][0], peer[0][0]
        if (field_bits(f_own) or 0) % 8:
            raise CompileError("E-UNSUPPORTED", "'||' fields must be a whole number of bytes")
        self.dup = (f_own, f_peer)
        self.stream_tx = True
        x.host["tx_stream"] = {"stream": 0, "base": TX_BASE, "fields": [f_own.f.name]}
        x.host["rx_stream"] = {"stream": 1, "base": RX_BASE, "fields": [f_peer.f.name]}
        c.label(self.lab())
        # enter: stage the first bit (the previous beat is not a data beat)
        self.stage("S0.BIT", "S0.BIT", ["ZERO -> S0.ADV"])
        ll = self.lab("l")
        self.check(ll, jcond="S0.END")        # loops when the stream goes on; falls through when it ends after one bit
        # loop: the previous beat was a data beat
        saved = self.kind_bit
        self.stage("S0.BIT", "S0.BIT", ["ZERO -> S0.ADV", "ZERO -> FLAGS.SET"], loop_label=ll)
        self.check(ll, jcond="S0.END")
        self.kind_bit = True
        self.gate = 2

    def const_step(self, s: Step):
        x, c = self.x, self.c
        if not s.data or s.bits:
            raise CompileError("E-UNSUPPORTED", "const bits other than whole bytes are not compiled yet")
        self.const_bytes += s.data
        c.label(self.lab())
        ll = self.lab("l")
        self.stage("S1.BIT", "S1.BIT", ["ZERO -> S1.ADV"], loop_label=ll)
        self.check(ll, jcond="S1.END")

    def crc_step(self, s: Step):
        x, c = self.x, self.c
        d = self.crc
        inv = d.xorout == (1 << d.width) - 1
        c.label(self.lab())
        self.cnt(d.width - 1)
        ll = self.lab("l")
        self.stage("LF0.O", "LF0.OUT", ["LF0.O -> LF0.ST"], invert=inv, loop_label=ll)
        self.check(ll, counter=True)

    def gap_step(self, s: Step):
        """Idle beats.  Housekeeping moves (LFSR reload, stream rewind) take one of the first idle beats each."""
        x, c = self.x, self.c
        n = gap_beats(s, x.clk.period)
        hk = self.hk
        if n == 0 and not hk:
            return
        c.label(self.lab("g"))
        c.i(["ZERO -> L.SYM"], note="idle")
        self.kind_bit = False
        if hk:
            c.i([hk[0]], pause=True, note="housekeeping")
            for mv in hk[1:]:
                c.label(self.lab("h"))
                c.i([mv], pause=True, note="housekeeping")
            rest = n - len(hk)
            if rest > 0:
                c.label(self.lab("c"))
                if rest > 1:
                    self.cnt(rest - 1)
                ll = self.lab("l")
                c.label(ll)
                self.check(ll, counter=True)
        else:
            if n == 1:
                c.i([], pause=True)
            else:
                self.cnt(n - 1)
                ll = self.lab("l")
                c.label(ll)
                self.check(ll, counter=True)
        self.hk = []


def prepass(x: Ctx, g: TxGen):
    frame = x.frame
    crc_steps = [s for s in frame if s.kind == "field" and s.f.type.kind == "crc"]
    par_steps = [s for s in frame if s.kind == "field" and s.f.type.kind == "parity"]
    if len(crc_steps) + len(par_steps) > 1:
        raise CompileError("E-UNSUPPORTED", "more than one crc or parity field in a frame (one LFSR is used)")
    if x.score.bits.invert and (x.rxp is not None or any(s.kind == "star" for s in frame)):
        raise CompileError("E-UNSUPPORTED", "'invert' with a sampled input (full duplex) is not compiled yet")
    if par_steps:
        # Parity is a width-1 CRC: poly 1 makes the LFSR a running XOR of the covered bits.  Shifting the parity bit
        # out through LF0.ST returns the register to 0, so no reload is needed between frames.  Odd = xorout 1.
        from score.ast import CrcDecl
        s = par_steps[0]
        lsb = x.order == "lsb"
        g.crc = CrcDecl(f"parity_{s.f.type.parity}", 1, 1, 0, lsb, lsb, 1 if s.f.type.parity == "odd" else 0)
        g.covered = crc_range(frame, s.f)
        if not g.covered:
            raise CompileError("E-UNSUPPORTED", f"parity '{s.f.name}': covered fields not found in the frame")
    if crc_steps:
        s = crc_steps[0]
        d = x.crc_decl(s.f.type.crc)
        if not (d.refin == d.refout == (x.order == "lsb")):
            raise CompileError("E-UNSUPPORTED", f"crc '{d.name}': refin/refout must equal the bit order "
                                                f"({x.order} first) to run on the LFSR bit-serially")
        full = (1 << d.width) - 1
        if d.xorout not in (0, full):
            raise CompileError("E-UNSUPPORTED", f"crc '{d.name}': xorout {d.xorout:#x} is neither 0 nor all ones")
        g.crc = d
        g.covered = crc_range(frame, s.f)
        init = _rev(d.init, d.width)
        for k in range((d.width + 7) // 8):
            byte = (init >> (8 * k)) & 0xFF
            g.hk.append(imm(byte, f"LF0.B{k}"))
            x.init_moves.append(imm(byte, f"LF0.B{k}"))
    if any(s.kind == "const" for s in frame):
        g.hk.append("#1 -> S1.CTL")


def gen_tx(x: Ctx) -> TxGen:
    g = TxGen(x)
    prepass(x, g)
    c = g.c
    steps = x.frame
    # The first field can be reached both after reset and after the frame
    # loop. A reset default is only a safe entry fact when the last field
    # leaves that same configuration behind.
    mailbox_widths = [field_bits(s) for s in steps if s.kind == "field"
                      and s.f.type.kind not in ("crc", "parity", "bytes")
                      and field_bits(s) is not None and field_bits(s) <= 8]
    if mailbox_widths:
        last = mailbox_widths[-1]
        final_cfg = (8 if x.msb and last < 8 else last, x.msb)
        if final_cfg != (8, False):
            g.cfg_sh["SH0"] = None
    mailbox_frame = any(s.kind == "field" and s.f.type.kind not in ("crc", "parity", "bytes")
                        and (field_bits(s) or 99) <= 8 for s in steps)
    first = steps[0] if steps else None
    g.fuse_first = bool(first and first.kind == "sym" and first.count == 1 and mailbox_frame)
    c.label("frame")
    for i, s in enumerate(steps):
        if s.owner != x.role and s.kind not in ("gap", "star"):
            raise CompileError("E-UNSUPPORTED", f"step '{s.describe()}' is owned by {s.owner}; the sender template "
                                                f"transmits only its own steps")
        if i == 1 and g.fuse_first:
            c.label("after0")
        if s.kind == "sym":
            g.sym(s)
        elif s.kind == "const":
            g.const_step(s)
        elif s.kind == "gap":
            g.gap_step(s)
        elif s.kind == "star":
            g.star_duplex(s)
        elif s.kind == "field":
            t = s.f.type
            if t.kind in ("crc", "parity"):
                g.crc_step(s)
            elif s.f.value is not None or s.f.expect is not None:
                raise CompileError("E-UNSUPPORTED", f"field '{s.f.name}': computed or checked values are not compiled yet")
            else:
                feed = 0 if s.f.name in g.covered else None
                w = field_bits(s)
                if t.kind == "bytes":
                    if t.until is None and w is None:
                        raise CompileError("E-UNSUPPORTED", f"field '{s.f.name}': bytes[N] with a computed length")
                    g.stream_field(s, w, feed, variable=w is None)
                elif w is not None and w <= 8:
                    g.mailbox_field(s, w, feed)
                else:
                    g.stream_field(s, w, feed, variable=False)
        else:
            raise CompileError("E-UNSUPPORTED", f"step '{s.describe()}' in a sender frame")
    if g.hk:
        c.i(["ZERO -> L.SYM"], note="idle (housekeeping beats)")
        c.i([g.hk[0]], pause=True, note="housekeeping")
        for mv in g.hk[1:]:
            c.i([mv], pause=True, note="housekeeping")
        g.hk = []
    return g


def finish_tx(x: Ctx, g: TxGen):
    """Idle state, init thread, line, pins, streams, LFSR: everything outside the frame steps."""
    c = g.c
    t = x.txp
    needs_go = not g.mailbox
    c.label("idle")
    clr = ["ZERO -> FLAGS.CLR"] if g.dup else []
    if g.fuse_first:
        first = x.frame[0]
        name = f"{first.name}({','.join(map(str, first.args))})" if first.args else first.name
        code = t.code_of[name]
        # HOST.INV is sampled ONCE, by one instruction that both stages the symbol and jumps.  The old pair
        # "stage if INV; jump if INV" sampled it twice: a mailbox byte landing between the two was consumed with the
        # first symbol never staged, and the byte was lost (12-cycle idle loop at 10 Mbaud).  The symbol comes from
        # R0 (loaded by the init thread) because an immediate would share the instruction's imm field with the jump
        # target.
        x.init_moves.append(imm(code, "R0"))
        c.i(["? R0 -> L.SYM", "! ZERO -> L.SYM", *clr], when="HOST.INV", goto="after0", jmode="if", jcond="HOST.INV",
            pause=True, note="idle / first symbol (one sample of the mailbox)")
        c.i([], goto="idle", pause=True, note="idle, second beat (the not-taken path falls here)")
    else:
        mv = ["ZERO -> L.SYM", *clr]
        if needs_go:
            mv.append("? HOST.IN -> NULL")
        # the jump reads the state before the go byte is consumed, so it shares the instruction with the read
        c.i(mv, when="HOST.INV" if needs_go else None, goto="frame", jmode="if", jcond="HOST.INV", pause=True,
            note="idle: stage idle, consume the go byte, start the frame")
        c.i([], goto="idle", pause=True, note="idle, second beat (the not-taken path falls here)")
    clk = x.clk
    taps = x.tap_text()
    line = [f"inc {clk.inc}", f"mod {clk.mod}", f"taps {taps}"]
    if x.rxp:
        r = x.rxp
        line.append(f"pins A=P{r.pina}" + (f" B=P{r.pinb}" if r.pinb is not None else ""))
        line.append(f"lut0 0x{r.lut0:08X}")
        line.append(f"lut1 0x{r.lut1:08X}")
        samp = [tp for tp in x.taps if "sample" in tp.why]
        line.append(f"snap tap{samp[-1].idx}")
    line.append("ctl run")
    x.b.block(".line 0", line)
    emit_out_pins(x, 0)
    threads = [(0, 0, 0, "L0.BEAT", "idle")]
    if g.stream_tx:
        x.b.block(".stream 0", ["mode tx", f"order {'msb' if x.msb else 'lsb'}", f"start {TX_BASE}", "len 0"])
    if g.const_bytes:
        x.b.block(".stream 1", ["mode tx", f"order {'msb' if x.msb else 'lsb'}", f"start {CONST_BASE}",
                                f"len {len(g.const_bytes)}"])
        x.b.cfg.append(f".data {CONST_BASE} " + " ".join(f"0x{b:02X}" for b in g.const_bytes))
        x.host["const_stream"] = {"stream": 1, "base": CONST_BASE, "len": len(g.const_bytes)}
    if g.dup:
        x.b.block(".stream 1", ["mode rx", f"order {'msb' if x.msb else 'lsb'}", f"start {RX_BASE}", "len 0"])
        samp = [tp for tp in x.taps if "sample" in tp.why][-1]
        x.b.cores[1].label("rx")
        x.b.cores[1].i(["? L.IN -> S1.RX"], when="F0", pause=True, goto="rx", note="capture while flag 0 (data beats)")
        threads.append((1, 1, 0, f"L0.TAP{samp.idx}", "rx"))
    if g.crc:
        d = g.crc
        x.b.cfg.append(f".lfsr 0 poly=0x{d.poly:X} width={d.width} init=0x{d.init:X}")
    x.b.cfg.append("")
    emit_threads(x, threads)
    emit_init_thread(x, 5)
