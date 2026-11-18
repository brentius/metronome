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
        self.CWOVR = 0             # v4 (SPEC v2 13.1)


class OutPin:
    STRIDE = m.HOST_STRIDE["OUT"]

    def __init__(self, o):
        self.o = o
        self.cfg = bytearray(self.STRIDE)
        self.reset()

    def decode(self):
        b = self.cfg
        self.LINE, self.BOUND = b[0] & 3, (b[0] >> 2) & 1
        self.LIVE = (b[0] >> 3) & 3          # v3 (SPEC v2 12.1): bit 0 b2 := PIN[PINA], bit 1 b1 := PIN[PINB]
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
            b2, b1 = (c >> self.SEL[2]) & 1, (c >> self.SEL[1]) & 1
            if self.LIVE:
                pin = lambda s: (ch.lv >> s) & 1 if s < m.N_IN_PINS else 0
                if self.LIVE & 1:
                    b2 = pin(ln.PINA)
                if self.LIVE & 2:
                    b1 = pin(ln.PINB)
            idx = (ln.SEG << 3) | (b2 << 2) | (b1 << 1) | ((c >> self.SEL[0]) & 1)
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
        self.contract_violations = []   # v3 (SPEC v2 12.5): (cycle, address, reason); kept across resets
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
        # v3 (SPEC v2 12): debug freeze, execution digest, edge capture; all 0 = v2 behaviour
        self.FREEZE = self.FRZ = self.FRZD = 0
        self.MEN = self.MISR = 0
        self.CEN = self.EMASK = self.DC = 0
        self.dbg_write = None      # (FREEZE, STEP) of a host DBG write in this cycle
        # v4 (SPEC v2 13): configuration written by the cores, edge replay; all 0 = v3 behaviour
        self.CWA = self.CWV = 0    # config-write address, pending write valid
        self.CWQ = (0, 0)          # pending (address, byte)
        self.BWP = 0               # the configuration latch bank was written in the previous cycle
        self.HH = None             # host configuration write held one cycle by the spacing rule
        self.RPL = self.RLV = self.RLVP = 0

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
        if self.RPL:                            # v4 replay (SPEC v2 13.2): masked pins read RLV
            mk, c, p = self.EMASK, self.RLV, self.RLVP
            lv = (lv & ~mk) | (c & mk)
            rs = (rs & ~mk) | (c & ~p & mk)
            fl = (fl & ~mk) | (~c & p & mk)
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
        self.dbg_write = None
        if self.FRZ:
            return self._step_frozen(raw)
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
        err = (ctrl.CONFLICT or ctrl.MEMHAZ or ctrl.CWOVR or any(t.LATE or t.OVR for t in self.threads)
               or any(ln.TAPMISS for ln in self.lines) or any(s.STARVED for s in self.mem.streams))
        irq_next = int(bool((ctrl.IRQEN & 1 and host.OUTV) or (ctrl.IRQEN & 2 and err)))
        hw = host.wr_now
        hdec = regs.decode(hw[0]) if hw else None
        self._contract(hdec, hw)
        # v3 edge capture (SPEC v2 12.4) and digest input (12.2), from cycle-t state
        cev = bool(self.CEN and not self.RPL and ((self.rs | self.fl) & self.EMASK & 0x1FFF))
        # v4 replay (SPEC v2 13.2): apply the record in S0.WB when DC + 1 reaches its interval
        s0 = self.mem.streams[0]
        rapply = bool(self.RPL and s0.WV and self.DC + 1 >= (s0.WB >> 13))
        rlate = rapply and self.DC + 1 > (s0.WB >> 13)
        rlv_next = ((self.RLV & ~self.EMASK) | (s0.WB & self.EMASK)) & 0x1FFF if rapply else self.RLV
        # v4 configuration writes (SPEC v2 13.1): bank port arbitration and the pending core write, cycle-t state
        bank, cw_rt, cw_drain = self._bank(hw, hdec, core_ok=True)
        rec = ((self.DC << 13) | (self.lv & 0x1FFF)) if cev else None
        misr_d = self._pins_word()
        # ---------------- phase 2 ----------------
        self.sp, self.s2, self.s1 = self.s2, self.s1, raw
        for l, ln in enumerate(self.lines):
            ctl = winners.get(f"L{l}.CTL")
            ctl_value = ctl[3] if ctl else None
            # Resolve host priority before applying effects of a RUN transition.
            # A host stop suppresses a simultaneous edge/move start (SPEC 3.2, 3.4).
            if hdec is not None and hdec[0] == "LRT" and hdec[1] == l and hdec[4][0] == "CTL":
                ctl_value = hw[1]
            sw = winners.get(("LSYM", l))
            sym = ln.sym_value(sw[2], sw[3]) if sw else None
            ln.commit(ctl_value, sym)
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
            s.CEN = (self.CEN and not self.RPL) if k == 0 else 0
            s.RPL = self.RPL if k == 0 else 0
            g = self.mem.served == ("S", k)
            wk = winners.get(f"S{k}")
            mv_adv = wk is not None and wk[2] == "ADV"
            mv_rx = wk[3] & 1 if (wk is not None and wk[2] == "RX") else None
            ctl = None
            if wk is not None and wk[2] == "CTL":
                ctl = wk[3] & 3
            if k in srt_ctl:
                ctl = (ctl or 0) | (srt_ctl[k] & 0x83)
            if s.commit(g, sword if g else 0, mv_adv, mv_rx, ctl, rec if k == 0 else None,
                        (rapply, rlate) if k == 0 else None):
                self.events.add(("STARVED", k))
        sh_cfg = []
        cw_new = False
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
                sh_cfg.append((k, v))
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
            elif kind == "CW":                  # v4 (SPEC v2 13.1)
                if op == "AL":
                    self.CWA = (self.CWA & 0xFF00) | v
                elif op == "AH":
                    self.CWA = (self.CWA & 0x00FF) | (v << 8)
                elif self.CWV and not cw_drain:
                    ctrl.CWOVR = 1
                    self.events.add("CWOVR")
                else:
                    self.CWQ, cw_new = (self.CWA, v), True
                    self.CWA = (self.CWA + 1) & 0xFFFF
        # LD/SH and CFG have independent write groups, but LD/SH must use cycle-t
        # LEN/MSB regardless of the winning moves' insertion order (SPEC v2 6).
        for k, v in sh_cfg:
            self.sh[k].cfg(v)
        if cw_drain or cw_new:
            self.CWV = int(cw_new)
        if memhaz:
            ctrl.MEMHAZ = 1
            self.events.add("MEMHAZ")
        if conflict:
            ctrl.CONFLICT = 1
            self.events.add("CONFLICT")
        for o, (v, oe) in zip(self.out, out_next):
            o.OUT, o.OEN = v, oe
        if self.MEN:
            self.MISR = self._misr_next(self.MISR, misr_d)
        dmax = (1 << m.ECAP_DC_BITS) - 1
        if self.RPL:
            self.DC = 0 if rapply else min(self.DC + 1, dmax)
        else:
            self.DC = 0 if not self.CEN else (1 if cev else min(self.DC + 1, dmax))
        self.RLVP, self.RLV = self.RLV, rlv_next
        host.commit(hland)
        host.IRQ = irq_next
        self.DB = 0
        self.db_next = 0
        # configuration written in W is latched at the end of W+1 and seen from W+2 (SPEC v2 1)
        for a, v in self.cfg_pipe:
            regs.apply_config(self, a, v)
        self.cfg_pipe = [bank] if bank is not None else []
        if cw_rt is not None:                   # v4: a core write to a DBG runtime register, before the host's
            regs.write_runtime(self, *cw_rt)
        # host write last (priority)
        if hw is not None and hdec is not None and hdec[0] not in ("prog", "data"):
            if hdec[0] not in regs.CONFIG_BLOCKS:
                regs.write_runtime(self, hw[0], hw[1])
        self.DB = self.db_next
        self._freeze_update()
        self.cycle += 1
        return self.outputs()

    # ------------------------------------------------------------------------------------------------------------
    # v3 (SPEC v2 12)
    def _pins_word(self):
        """D of 12.2: OUT[13:0] in bits 13:0, OEN[7:0] in bits 21:14 (the pin registers in this cycle)."""
        d = 0
        for o in self.out:
            d |= o.OUT << o.o
            if o.o < m.N_OE_PINS:
                d |= o.OEN << (14 + o.o)
        return d

    @staticmethod
    def _misr_next(mv, d):
        nx = (mv << 1) & 0xFFFFFFFF
        if mv >> 31:
            nx ^= m.MISR_POLY
        return nx ^ d

    def _freeze_update(self):
        """FRZ' and FRZD' (12.3), after this cycle's host write."""
        self.FRZD = self.FRZ
        if self.dbg_write is not None:
            fz, stp = self.dbg_write
            self.FRZ = int(fz and not stp)
        else:
            self.FRZ = self.FREEZE

    CW_RUNTIME = {"ECTL", "EMASK", "RLV"}

    def _bank(self, hw, hdec, core_ok):
        """v4 (SPEC v2 13.1): the configuration latch bank's single write port, from cycle-t state. The bank is
        never written in two consecutive cycles (md2_cfg_bank write spacing rule): a host configuration write
        that meets a bank write in the previous cycle is held one cycle (HH); the host has priority over a
        pending core write. Returns (bank write (addr, value) or None, core runtime write or None, core write
        drained this cycle). Updates HH and BWP."""
        host_bank = None
        if self.HH is not None:
            host_bank, self.HH = self.HH, None
        if hw is not None and hdec is not None and hdec[0] in regs.CONFIG_BLOCKS:
            assert host_bank is None, "two host configuration writes within two cycles"
            if self.BWP:
                self.HH = hw
            else:
                host_bank = hw
        bank, cw_rt, drain = host_bank, None, False
        if core_ok and self.CWV:
            a, v = self.CWQ
            d = regs.decode(a)
            if d is not None and d[0] in regs.CONFIG_BLOCKS:
                if not self.BWP and host_bank is None:
                    bank, drain = (a, v), True
                    self._contract(d, (a, v), who="core")
            else:
                drain = True
                if d is not None and d[0] == "DBG" and d[4][0] in self.CW_RUNTIME:
                    cw_rt = (a, v)
        self.BWP = int(bank is not None)
        return bank, cw_rt, drain

    def _contract(self, hdec, hw, who="host"):
        """12.5: record a host write issued in this cycle that breaks the program-load contract (model only).
        v4: also a core configuration write, checked in the cycle it reaches the bank (reason prefixed "core")."""
        if hdec is None:
            return
        b, i = hdec[0], hdec[1]
        why = None
        if b == "LINE":
            ln = self.lines[i]
            if ln.RUN or ln.ARM:
                why = f"line {i} configuration written while RUN/ARM"
        elif b == "OUT":
            o = self.out[i]
            ln = self.lines[o.LINE]
            if o.BOUND and (ln.RUN or ln.ARM):
                why = f"pin O{i} configuration written while bound to running line {o.LINE}"
        elif b == "THREAD":
            t = self.threads[i]
            if t.EN or t.READY or t.RUNNING:
                why = f"thread {i} configuration written while EN/READY/RUNNING"
        elif b == "LFSR":
            if self.ctrl.RUN:
                why = f"LFSR {i} polynomial written while RUN_global"
        elif b == "prog":
            c = self.cores[i]
            if self.ctrl.RUN or c.XV or c.RV:
                why = f"core {i} program written while RUN_global or a burst is in flight"
        if why:
            self.contract_violations.append((self.cycle, hw[0], why if who == "host" else f"core: {why}"))

    def _step_frozen(self, raw):
        """A frozen cycle (12.3): only the host link, host writes, host data RAM requests, synchronisers, IRQ and
        configuration latches act. FP, INVP, HELD, pin registers, MISR and DC hold; a doorbell pulse is held."""
        host, ctrl = self.host, self.ctrl
        self.lv, self.rs, self.fl = self._levels()
        host.comb(self, self.s2, self.sp)
        err = (ctrl.CONFLICT or ctrl.MEMHAZ or ctrl.CWOVR or any(t.LATE or t.OVR for t in self.threads)
               or any(ln.TAPMISS for ln in self.lines) or any(s.STARVED for s in self.mem.streams))
        irq_next = int(bool((ctrl.IRQEN & 1 and host.OUTV) or (ctrl.IRQEN & 2 and err)))
        hw = host.wr_now
        hdec = regs.decode(hw[0]) if hw else None
        self._contract(hdec, hw)
        self.sp, self.s2, self.s1 = self.s2, self.s1, raw
        hland = self.mem.commit_frozen(host.newreq, self.FRZD)
        host.commit(hland)
        host.IRQ = irq_next
        db_held = self.DB
        self.db_next = 0
        bank, _, _ = self._bank(hw, hdec, core_ok=False)
        for a, v in self.cfg_pipe:
            regs.apply_config(self, a, v)
        self.cfg_pipe = [bank] if bank is not None else []
        if hw is not None and hdec is not None and hdec[0] not in ("prog", "data"):
            if hdec[0] in regs.CONFIG_BLOCKS:
                pass
            elif hdec[0] == "SRT":
                if hdec[4][0] == "CTL":          # rewind and STARVED clear act; a flush is ignored while frozen
                    s = self.mem.streams[hdec[1]]
                    if hw[1] & 0x80:
                        s.STARVED = 0
                    if hw[1] & 1:
                        s.POS = s.BIDX = 0
                        s.BA = s.START
                        s.CUR = s.CV = s.WV = s.RQ = s.LD = s.PV = 0
            else:
                for ln in self.lines:
                    ln.run_t = ln.RUN
                regs.write_runtime(self, hw[0], hw[1])
        elif hdec is not None and hdec[0] == "prog":
            c = self.cores[hdec[1]]
            w, k = hdec[2], hdec[3]
            c.prog[w] = (c.prog[w] & ~(0xFF << 8 * k)) | (hw[1] << 8 * k)
        self.DB = self.db_next | db_held
        self._freeze_update()
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
                self.dbg_write = None
                regs.write_runtime(self, a, b)
                self.DB = self.db_next
                if self.dbg_write is not None:
                    self.FRZ = self.FREEZE

    def backdoor_read(self, addr):
        d = regs.decode(addr)
        if d is not None and d[0] == "data":
            return self.mem.data[d[2]]
        return regs.read(self, addr)

    def load_program(self, core, words, base=0):
        for i, w in enumerate(words):
            self.cores[core].prog[base + i] = w & ((1 << 64) - 1)
