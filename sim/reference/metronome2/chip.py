"""Whole-chip cycle-level model of Metronome v2 behind the tt_um pins (SPEC v2).

Each `step` is one clock cycle in two phases. Phase 1 evaluates every combinational value and every decision from
cycle-t state. Phase 2 commits next state. Host register writes are applied last, which gives them priority over
moves and hardware updates (SPEC v2 9). Configuration written by the host in cycle W becomes visible in W+2.
"""
from .md import m
from . import regs
from .core import Core, Thread, DST_INFO, DST_GROUP, guard_vector, line_guards
from .host import Host
from .line import Line
from .memory import Memory
from .units import Acc, Counter, Flags, Lfsr, Shifter

N_PIN = m.N_IN_PINS
PIN_BIT = [k if k < 8 else k + 3 for k in range(N_PIN)]   # raw vector: bits 0..7 uio_in, 8..15 ui_in


class Ctrl:
    def __init__(self):
        self.reset()

    def reset(self):
        self.RUN = self.IRQEN = self.CONFLICT = self.MEMHAZ = 0


class OutPin:
    STRIDE = m.HOST_STRIDE["OUT"]

    def __init__(self, o):
        self.o = o
        self.cfg = bytearray(self.STRIDE)
        self.reset()

    def decode(self):
        b = self.cfg
        self.LINE, self.BOUND = b[0] & 3, (b[0] >> 2) & 1
        self.SEL = [b[1] & 3, (b[1] >> 2) & 3, (b[1] >> 4) & 3]
        self.LUT = int.from_bytes(bytes(b[4:8]), "little")
        self.OE = int.from_bytes(bytes(b[8:12]), "little") if self.o < m.N_OE_PINS else 0

    def reset(self):
        self.cfg[:] = bytes(self.STRIDE)
        self.decode()
        self.OUT = self.OEN = 0

    def compute(self, ch):
        if self.BOUND:
            ln = ch.lines[self.LINE]
            c = ln.COMMITTED
            idx = (ln.SEG << 3) | (((c >> self.SEL[2]) & 1) << 2) | (((c >> self.SEL[1]) & 1) << 1) \
                | ((c >> self.SEL[0]) & 1)
        else:
            idx = 0
        return (self.LUT >> idx) & 1, (self.OE >> idx) & 1


class LfsrCfg:
    STRIDE = m.HOST_STRIDE["LFSR"]

    def __init__(self, lf):
        self.lf = lf
        self.cfg = bytearray(self.STRIDE)

    def decode(self):
        self.lf.POLY = int.from_bytes(bytes(self.cfg[0:4]), "little")

    def reset(self):
        self.cfg[:] = bytes(self.STRIDE)
        self.decode()


class Chip:
    def __init__(self):
        self.lines = [Line(l) for l in range(m.N_LINES)]
        self.threads = [Thread(t) for t in range(m.N_THREADS)]
        self.cores = [Core(c) for c in range(m.N_CORES)]
        self.flags = Flags()
        self.acc = Acc()
        self.sh = [Shifter() for _ in range(m.N_SHIFTERS)]
        self.cnt = [Counter() for _ in range(m.N_COUNTERS)]
        self.lf = [Lfsr() for _ in range(m.N_LFSRS)]
        self.lf_cfg = [LfsrCfg(lf) for lf in self.lf]
        self.mem = Memory()
        self.host = Host()
        self.out = [OutPin(o) for o in range(m.N_OUT_PINS)]
        self.ctrl = Ctrl()
        self.cycle = 0
        self.trace = []            # (cycle, core, thread, pc) of every executed instruction
        self.reset()
        self.rst_hold = 0

    # ------------------------------------------------------------------------------------------------------------
    def reset(self):
        """Every register and all configuration to 0; program and data memories keep their contents."""
        self.s1 = self.s2 = self.sp = 0
        for blk in (self.flags, self.acc, self.mem, self.host, self.ctrl):
            blk.reset()
        for lst in (self.lines, self.threads, self.sh, self.cnt, self.lf, self.lf_cfg, self.out):
            for b in lst:
                b.reset()
        for c in self.cores:
            c.reset()
        self.cfg_pipe = []         # [(addr, value)] written in the previous cycle, visible from the next
        self.DB = 0
        self.lv = self.rs = self.fl = 0

    def exec_trace(self, c, t, pc):
        self.trace.append((self.cycle, c, t, pc))

    def outputs(self):
        uo = self.host.MISO | (self.host.IRQ << 1)
        for j in range(6):
            uo |= self.out[8 + j].OUT << (2 + j)
        uio_out = sum(self.out[i].OUT << i for i in range(8))
        uio_oe = sum(self.out[i].OEN << i for i in range(8))
        return uo, uio_out, uio_oe

    def _levels(self):
        lv = rs = fl = 0
        for k, b in enumerate(PIN_BIT):
            c, p = (self.s2 >> b) & 1, (self.sp >> b) & 1
            lv |= c << k
            rs |= (c & (p ^ 1)) << k
            fl |= ((c ^ 1) & p) << k
        return lv, rs, fl

    # ------------------------------------------------------------------------------------------------------------
    def step(self, ui_in, uio_in=0, rst_n=1):
        if not rst_n:
            self.reset()
            self.rst_hold = 2
            self.cycle += 1
            return self.outputs()
        if self.rst_hold:                       # rst_q = rst_n delayed by two rising edges (SPEC v2 1)
            self.reset()
            self.rst_hold -= 1
            self.cycle += 1
            return self.outputs()
        raw = ((ui_in & 0xFF) << 8) | (uio_in & 0xFF)
        host, ctrl = self.host, self.ctrl
        self.events = set()
        # ---------------- phase 1 ----------------
        self.lv, self.rs, self.fl = self._levels()
        for ln in self.lines:
            ln.comb(self.lv, self.rs, self.fl)
        base = guard_vector(self)
        cache = {}

        def line_gv(l):
            if l not in cache:
                cache[l] = line_guards(self, base, l)
            return cache[l]

        for c in self.cores:
            c.plan(self, base, line_gv)
        host.comb(self, self.s2, self.sp)
        # write groups: lowest (core, move index) wins; late symbol writes judged per move
        winners, conflict, late = {}, False, set()
        for c in self.cores:
            for (i, d, val, t, l) in c.moves:
                kind, k, op = DST_INFO[d]
                if kind == "NULL":
                    continue
                if kind == "LSYM":
                    key = ("LSYM", l)
                    if not self.threads[t].ARMED:
                        late.add(t)
                elif kind == "TSTOP":
                    key = ("TSTOP", t)
                else:
                    key = DST_GROUP[d]
                if key in winners:
                    conflict = True
                else:
                    winners[key] = (kind, k, op, val, t, l)
        inv_clear = memhaz = False
        for c in self.cores:
            for eff in c.effects:
                if eff == "hostin":
                    inv_clear = True
                elif not self.mem.ptr.RDY:
                    memhaz = True
        trig = [th.EN and (th.event(self) or (self.DB >> th.t) & 1) for th in self.threads]
        self.mem.arbitrate()
        out_next = [o.compute(self) for o in self.out]
        err = (ctrl.CONFLICT or ctrl.MEMHAZ or any(t.LATE or t.OVR for t in self.threads)
               or any(ln.TAPMISS for ln in self.lines) or any(s.STARVED for s in self.mem.streams))
        irq_next = int(bool((ctrl.IRQEN & 1 and host.OUTV) or (ctrl.IRQEN & 2 and err)))
        hw = host.wr_now
        hdec = regs.decode(hw[0]) if hw else None
        # ---------------- phase 2 ----------------
        self.sp, self.s2, self.s1 = self.s2, self.s1, raw
        for l, ln in enumerate(self.lines):
            ctl = winners.get(f"L{l}.CTL")
            sw = winners.get(("LSYM", l))
            sym = ln.sym_value(sw[2], sw[3]) if sw else None
            ln.commit(ctl[3] if ctl else None, sym)
            if ln.tapmiss_ev:
                self.events.add(("TAPMISS", l))
        disp = {c.dispatch[0]: c for c in self.cores if c.dispatch is not None}
        paused = {c.pause[0]: c.pause[1] for c in self.cores if c.pause is not None}
        for th in self.threads:
            t = th.t
            busy = th.READY or th.RUNNING
            acc = trig[t] and not busy
            if trig[t] and busy:
                th.OVR = 1
                self.events.add(("OVR", t))
            if t in disp:
                th.READY, th.RUNNING = 0, 1
            elif acc:
                th.READY = 1
            if t in paused:
                th.RUNNING = 0
                th.PC = paused[t]
            if acc:
                th.ARMED = 1
            elif self.lines[th.LINE].beat:
                th.ARMED = 0
            if t in late:
                th.LATE = 1
                self.events.add(("LATE", t))
            if ("TSTOP", t) in winners:
                th.EN = 0
        hpw = None
        if hdec is not None and hdec[0] == "prog":
            hpw = (hdec[2], hdec[3], hw[1])
        for c in self.cores:
            c.commit(self, hpw if (hpw is not None and hdec[1] == c.c) else None)
        self.flags.FP = self.flags.F
        host.INVP = host.INV
        if inv_clear:
            host.INV = 0
        hland, sword = self.mem.commit(host.newreq)
        srt_ctl = {}
        if hdec is not None and hdec[0] == "SRT" and hdec[4][0] == "CTL":
            srt_ctl[hdec[1]] = hw[1]
        for k, s in enumerate(self.mem.streams):
            g = self.mem.served == ("S", k)
            wk = winners.get(f"S{k}")
            mv_adv = wk is not None and wk[2] == "ADV"
            mv_rx = wk[3] & 1 if (wk is not None and wk[2] == "RX") else None
            ctl = None
            if wk is not None and wk[2] == "CTL":
                ctl = wk[3] & 3
            if k in srt_ctl:
                ctl = (ctl or 0) | (srt_ctl[k] & 0x83)
            if s.commit(g, sword if g else 0, mv_adv, mv_rx, ctl):
                self.events.add(("STARVED", k))
        for key, (kind, k, op, v, t, l) in winners.items():
            if kind == "FLAGS":
                n = v & 0xF
                self.flags.F = (self.flags.F | (1 << n)) if op == "SET" else (self.flags.F & ~(1 << n))
            elif kind == "ACC":
                self.acc.op(op, v)
            elif kind == "R":
                self.acc.R[k] = v
            elif kind == "SHLS":
                (self.sh[k].ld if op == "LD" else self.sh[k].sh)(v)
            elif kind == "SHCFG":
                self.sh[k].cfg(v)
            elif kind == "CNT":
                self.cnt[k].op(op, v)
            elif kind == "LF":
                if op == "ST":
                    self.lf[k].step(v)
                else:
                    self.lf[k].set_byte(op, v)
            elif kind == "P":
                if self.mem.ptr.op(op, v, self.mem.served == "P"):
                    memhaz = True
            elif kind == "HOSTOUT":
                host.OUTB, host.OUTV = v, 1
                self.events.add("HOSTOUT")
        if memhaz:
            ctrl.MEMHAZ = 1
            self.events.add("MEMHAZ")
        if conflict:
            ctrl.CONFLICT = 1
            self.events.add("CONFLICT")
        for o, (v, oe) in zip(self.out, out_next):
            o.OUT, o.OEN = v, oe
        host.commit(hland)
        host.IRQ = irq_next
        self.DB = 0
        self.db_next = 0
        # configuration written in W is latched at the end of W+1 and seen from W+2 (SPEC v2 1)
        for a, v in self.cfg_pipe:
            regs.apply_config(self, a, v)
        self.cfg_pipe = []
        # host write last (priority)
        if hw is not None and hdec is not None and hdec[0] not in ("prog", "data"):
            if hdec[0] in regs.CONFIG_BLOCKS:
                self.cfg_pipe.append(hw)
            else:
                regs.write_runtime(self, hw[0], hw[1])
        self.DB = self.db_next
        self.cycle += 1
        return self.outputs()

    # ------------------------------------------------------------------------------------------------------------
    def run(self, ui_frames, uio_in=0):
        return [self.step(u, uio_in) for u in ui_frames]

    def backdoor_write(self, addr, data):
        """Instant host-equivalent writes of bytes at addr, addr+1, ... (not cycle-accurate)."""
        for i, b in enumerate(bytes(data)):
            a = (addr + i) & 0xFFFF
            d = regs.decode(a)
            if d is None:
                continue
            if d[0] == "prog":
                c = self.cores[d[1]]
                c.prog[d[2]] = (c.prog[d[2]] & ~(0xFF << 8 * d[3])) | (b << 8 * d[3])
            elif d[0] == "data":
                self.mem.data[d[2]] = b
            elif d[0] in regs.CONFIG_BLOCKS:
                regs.apply_config(self, a, b)
            elif d[0] == "SRT":
                if b & 0x80:
                    self.mem.streams[d[1]].STARVED = 0
                if b & 1:
                    s = self.mem.streams[d[1]]
                    s.POS = s.BIDX = 0
                    s.BA = s.START
                    s.CUR = s.CV = s.WV = s.RQ = s.LD = s.PV = 0
            else:
                self.events = set()
                for ln in self.lines:
                    ln.run_t = ln.RUN
                self.db_next = self.DB
                regs.write_runtime(self, a, b)
                self.DB = self.db_next

    def backdoor_read(self, addr):
        d = regs.decode(addr)
        if d is not None and d[0] == "data":
            return self.mem.data[d[2]]
        return regs.read(self, addr)

    def load_program(self, core, words, base=0):
        for i, w in enumerate(words):
            self.cores[core].prog[base + i] = w & ((1 << 64) - 1)
