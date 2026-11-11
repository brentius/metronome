"""Whole-chip cycle-level model behind the tt_um pins (SPEC 1).

Each `step` is two-phase: phase 1 evaluates every combinational value and decides every write from the current
(register) state without mutating any block that another block reads; phase 2 commits next state. Host register
writes are applied last, which gives them priority over moves (SPEC 9).
"""
import machine as m

from . import pins as P
from . import regs
from .beatgen import BeatGen
from .core import Core, DST_INFO
from .engine import Engine, OutCell
from .host import Host
from .memory import Memory
from .units import Acc, Counter, Flags, Lfsr, Shifter


class Ctrl:
    def __init__(self):
        self.reset()

    def reset(self):
        self.RUN = 0
        self.IRQEN = 0
        self.CONFLICT = 0
        self.MEMHAZ = 0


class Chip:
    def __init__(self):
        self.pins = P.Pins()
        self.bg = [BeatGen(g) for g in range(m.N_BEATGENS)]
        self.eng = [Engine(e) for e in range(m.N_ENGINES)]
        self.cores = [Core(c) for c in range(m.N_CORES)]
        self.flags = Flags()
        self.acc = Acc()
        self.sh = [Shifter() for _ in range(m.N_SHIFTERS)]
        self.cnt = [Counter() for _ in range(m.N_COUNTERS)]
        self.lf = [Lfsr() for _ in range(m.N_LFSRS)]
        self.mem = Memory()
        self.host = Host()
        self.out = [OutCell(o) for o in range(m.N_OUT_PINS)]
        self.ctrl = Ctrl()
        self.lv = 0
        self._instant = False
        self.cycle = 0
        self.reset()

    # ------------------------------------------------------------------------------------------------------------
    def reset(self):
        """Synchronous reset: every register to 0; program and data memories keep their contents."""
        for blk in (self.pins, self.flags, self.acc, self.mem, self.host, self.ctrl):
            blk.reset()
        for lst in (self.bg, self.eng, self.cores, self.sh, self.cnt, self.lf, self.out):
            for b in lst:
                b.reset()
        self.lv = 0

    def src_effect(self, eff):
        if eff[0] == "hostin":
            self._inv_clear = True
        elif not self.mem.ptrs[eff[1]].RDY:
            self._memhaz = True

    def mem_host_write(self, off, b):
        if self._instant:
            self.mem.data[off] = b
        else:
            self.mem.host_req = ("W", off, b)

    # ------------------------------------------------------------------------------------------------------------
    def outputs(self):
        uo = self.host.MISO | (self.host.IRQ << 1)
        for j in range(6):
            uo |= self.out[8 + j].OUT << (2 + j)
        uio_out = sum(self.out[i].OUT << i for i in range(8))
        uio_oe = sum(self.out[i].OEN << i for i in range(8))
        return uo, uio_out, uio_oe

    def step(self, ui_in, uio_in, rst_n=1):
        if not rst_n:
            self.reset()
            self.cycle += 1
            return self.outputs()
        raw = ((ui_in & 0xFF) << 8) | (uio_in & 0xFF)
        pins, host, ctrl = self.pins, self.host, self.ctrl
        # ---------------- phase 1: combinational evaluation on cycle-t state ----------------
        self.lv, rs, fl = pins.levels()
        lv, s2, sp = self.lv, pins.s2, pins.sp
        self._inv_clear = False
        self._memhaz = False
        for g in self.bg:
            g.comb(rs, fl)
        for c in self.cores:
            c.plan(self)
        sck = (s2 >> P.SCK_BIT) & 1
        spk = (sp >> P.SCK_BIT) & 1
        host.comb(self, sck and not spk, spk and not sck, s2)
        doorbell = 0
        if host.wr is not None and regs.doorbell_addr(host.wr[0]):
            doorbell = host.wr[1]
        # resolve write groups: lowest (core, move index) wins
        winners = {}
        conflict = False
        for c in self.cores:
            for (_c, _i, dst, val, e) in c.moves:
                kind, k, op = DST_INFO[dst]
                if kind == "NULL":
                    continue
                key = (kind, e if kind in ("ESYM", "ESTOP") else k)
                if key in winners:
                    conflict = True
                else:
                    winners[key] = (kind, k, op, val, e)
        for e, eng in enumerate(self.eng):
            eng.dispatched = False
            eng.paused_npc = None
            eng.trig = eng.event(self, rs, fl, lv, (doorbell >> e) & 1)
        for c in self.cores:
            if c.dispatch is not None:
                self.eng[c.dispatch].dispatched = True
            if c.pause is not None:
                self.eng[c.pause[0]].paused_npc = c.pause[1]
        self.mem.arbitrate()
        out_next = [oc.compute(self) for oc in self.out]
        sticky_any = ctrl.CONFLICT or ctrl.MEMHAZ or any(en.LATE or en.OVR for en in self.eng)
        irq_next = int(bool((ctrl.IRQEN & 1 and host.OUTV) or (ctrl.IRQEN & 2 and sticky_any)))
        # ---------------- phase 2: commit ----------------
        pins.shift(raw)
        for g in self.bg:
            mv = winners.get(("BG", g.g))
            g.commit(mv[3] if mv else None)
        for e, eng in enumerate(self.eng):
            mv = winners.get(("ESYM", e))
            eng.commit(self, lv, mv[3] if mv else None)
            if ("ESTOP", e) in winners:
                eng.EN = 0
        for c in self.cores:
            c.commit()
        self.flags.FP = self.flags.F
        host.INVP = host.INV
        if self._inv_clear:
            host.INV = 0
        if host.rd_effect:
            host.OUTV = 0            # SPEC-AMBIGUITY: a HOST.OUT move in the same cycle wins (the byte is not lost)
        hland = self.mem.commit(host.newreq)
        if hland is not None:
            host.HRD = hland
        if host.hrd_next is not None:
            host.HRD = host.hrd_next
        for key, (kind, k, op, v, e) in winners.items():
            self._apply(kind, k, op, v)
        ctrl.MEMHAZ |= int(self._memhaz)
        ctrl.CONFLICT |= int(conflict)
        for oc, (o, oe) in zip(self.out, out_next):
            oc.OUT = o
            oc.OEN = oe if oc.o < m.N_OE_PINS else 0
        host.MISO = host.MISO_next
        host.IRQ = irq_next
        # host register write last: priority over moves
        self._hostout_moved = any(k[0] == "HOSTOUT" for k in winners)
        if host.wr is not None:
            regs.write(self, host.wr[0], host.wr[1])
        self.cycle += 1
        return self.outputs()

    def _apply(self, kind, k, op, v):
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
            if self.mem.ptrs[k].op(op, v, self.mem.served == k):
                self._memhaz = True
        elif kind == "HOSTOUT":
            self.host.OUTB = v
            self.host.OUTV = 1
        # BG, ESYM, ESTOP handled in step

    # ------------------------------------------------------------------------------------------------------------
    # Convenience: bulk stepping, instant host access, state introspection
    # ------------------------------------------------------------------------------------------------------------
    def run(self, ui_frames, uio_in=0):
        """Step through a list of ui_in values; returns the list of (uo, uio_out, uio_oe) per step."""
        return [self.step(u, uio_in) for u in ui_frames]

    def backdoor_write(self, addr, data):
        """Instant host write of bytes at addr, addr+1, ... (SPEC 9 semantics; not cycle-accurate)."""
        self._instant = True
        try:
            for i, b in enumerate(bytes(data)):
                regs.write(self, addr + i, b, instant=True)
        finally:
            self._instant = False

    def backdoor_read(self, addr):
        d = regs.decode(addr)
        if d is not None and d[0] == "data":
            return self.mem.data[d[2]]
        v = regs.read(self, addr)
        if regs.read_effect(self, addr):
            self.host.OUTV = 0
        return v

    @property
    def state(self):
        """Snapshot of every architectural register as a nested dict (for debugging and lockstep diffs)."""
        h = self.host
        return {
            "pins": dict(s1=self.pins.s1, s2=self.pins.s2, sp=self.pins.sp),
            "bg": [{k: getattr(g, k) for k in ("INC", "MOD", "T0", "T1", "T2", "PRE", "WLO", "WHI", "WEN", "EDGE_PIN",
                                                "EDGE_POL", "PH", "RUN", "ARM", "REN", "SC", "SP")} for g in self.bg],
            "eng": [{k: getattr(e, k) for k in ("EN", "CORE", "BG", "TRIG", "PINA", "PINB", "LUT0", "LUT1", "W0C", "W0H",
                                                 "W1C", "W1H", "PC", "READY", "RUNNING", "ARMED", "STAGED", "COMMITTED",
                                                 "CAP", "LATE", "OVR")} for e in self.eng],
            "core": [dict(XV=c.XV, XE=c.XE, XPC=c.XPC, iaddr=c.iaddr) for c in self.cores],
            "flags": dict(F=self.flags.F, FP=self.flags.FP),
            "acc": dict(A=self.acc.A, Z=self.acc.Z, C=self.acc.C, N=self.acc.N, R=list(self.acc.R)),
            "sh": [dict(D=s.D, CNT=s.CNT, LEN=s.LEN, MSB=s.MSB) for s in self.sh],
            "cnt": [c.V for c in self.cnt],
            "lf": [dict(S=l.S, POLY=l.POLY) for l in self.lf],
            "ptr": [dict(PTR=p.PTR, D=p.D, RDY=p.RDY, req=p.req, pipe=p.pipe) for p in self.mem.ptrs],
            "host": {k: getattr(h, k) for k in ("INB", "OUTB", "INV", "OUTV", "INVP", "RX", "TX", "bitcnt", "bytecnt", "cmd",
                                                 "ADDR", "HRD", "txpend", "MISO", "IRQ")},
            "ctrl": dict(RUN=self.ctrl.RUN, IRQEN=self.ctrl.IRQEN, CONFLICT=self.ctrl.CONFLICT, MEMHAZ=self.ctrl.MEMHAZ),
            "out": [dict(ENG=o.ENG, LUT=o.LUT, OE=o.OE, OUT=o.OUT, OEN=o.OEN) for o in self.out],
        }
