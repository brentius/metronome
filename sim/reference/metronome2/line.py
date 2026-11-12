"""Lines (SPEC v2 section 3): beat generator, taps and fired bits, capture, snapshot, symbols."""
from .md import m


def _le(b, off, n):
    return int.from_bytes(bytes(b[off:off + n]), "little")


def edge_sel(pin, pol, rs, fl):
    """Polarity-selected synchronised edge of input pin `pin` (0 for pin >= 13 or polarity 0)."""
    if pin >= m.N_IN_PINS or pol == 0:
        return 0
    r, f = (rs >> pin) & 1, (fl >> pin) & 1
    return r if pol == 1 else f if pol == 2 else (r | f)


class Line:
    STRIDE = m.HOST_STRIDE["LINE"]

    def __init__(self, l):
        self.l = l
        self.cfg = bytearray(self.STRIDE)
        self.reset()

    # ---------------------------------------------------------------- configuration
    def decode(self):
        b = self.cfg
        self.INC, self.MOD = _le(b, 0x00, 2), _le(b, 0x02, 2)
        self.T = [_le(b, 0x04, 2), _le(b, 0x06, 2), _le(b, 0x08, 2)]
        self.PRE, self.WLO, self.WHI = _le(b, 0x0A, 2), _le(b, 0x0C, 2), _le(b, 0x0E, 2)
        e = b[0x10]
        self.EDGE_PIN, self.EDGE_POL, self.WEN, self.FOLLOW = e & 15, (e >> 4) & 3, (e >> 6) & 1, (e >> 7) & 1
        e = b[0x11]
        self.T0E_PIN, self.T0E_POL, self.T0SRC = e & 15, (e >> 4) & 3, (e >> 6) & 1
        self.PINA, self.PINB = b[0x12] & 15, b[0x12] >> 4
        self.SNAP = b[0x13] & 3
        self.LUT0, self.LUT1 = _le(b, 0x14, 4), _le(b, 0x18, 4)

    def reset_cfg(self):
        self.cfg[:] = bytes(self.STRIDE)
        self.decode()

    def reset(self):
        self.reset_cfg()
        self.PH = 0
        self.RUN = self.ARM = self.REN = 0
        self.SC = self.SP = 0
        self.FIRED = 0           # bit k = tap k fired in this beat
        self.W = 0               # {B1, A2, A1, A0}
        self.SN = 0
        self.REM = 0
        self.STAGED = self.COMMITTED = 0
        self.TAPMISS = 0
        self.beat = 0
        self.tap = [0, 0, 0]

    # ---------------------------------------------------------------- combinational helpers
    @property
    def SEG(self):
        return bin(self.FIRED).count("1")

    @property
    def IN(self):
        idx = (self.REM << 4) | self.SN
        return (((self.LUT1 >> idx) & 1) << 1) | ((self.LUT0 >> idx) & 1)

    @property
    def CAP(self):
        return (self.REM << 4) | self.SN

    def tap_enabled(self, k):
        if k == 0 and self.T0SRC:
            return self.T0E_POL != 0
        return self.T[k] < self.MOD

    def fired_at_start(self, ph):
        """FIRED when RUN rises (SPEC 3.4): enabled phase taps at or behind the starting phase."""
        f = 0
        for k in range(3):
            if not (k == 0 and self.T0SRC) and self.T[k] < self.MOD and self.T[k] <= ph:
                f |= 1 << k
        return f

    # ---------------------------------------------------------------- phase 1
    def comb(self, lv, rs, fl):
        ph, run = self.PH, self.RUN
        edge = edge_sel(self.EDGE_PIN, self.EDGE_POL, rs, fl)
        e0 = edge_sel(self.T0E_PIN, self.T0E_POL, rs, fl)
        if self.WLO <= self.WHI:
            inwin = self.WLO <= ph <= self.WHI
        else:
            inwin = ph >= self.WLO or ph <= self.WHI
        self.start = bool(edge and self.ARM and not run)
        self.accept = bool(edge and run and self.REN and (not self.WEN or inwin))
        self.adv = bool(run and not self.accept)
        n = ph + self.INC
        over = n >= self.MOD
        self.nx = (n - self.MOD) if over else n
        self.wrap = self.adv and over
        beat = self.accept if self.FOLLOW else self.wrap
        self.beat = int(beat)
        cur_bits = nxt_bits = 0
        miss = False
        tap = [0, 0, 0]
        for k in range(3):
            if k == 0 and self.T0SRC:
                en = self.T0E_POL != 0
                cross = bool(run and e0)
                nxt = cross and beat
            else:
                t = self.T[k]
                en = t < self.MOD
                if over:
                    cross = self.adv and en and (t > ph or t <= self.nx)
                else:
                    cross = self.adv and en and (ph < t <= self.nx)
                nxt = cross and beat and over and t <= self.nx
            cur = cross and not nxt
            fired_k = (self.FIRED >> k) & 1
            tap[k] = int((cur and not fired_k) or nxt)
            cur_bits |= int(cur) << k
            nxt_bits |= int(nxt) << k
            if beat and en and not fired_k and not cur:
                miss = True
        self.tap = tap
        self.tapmiss_ev = miss
        self.fired_next = nxt_bits if beat else (self.FIRED | cur_bits)
        # capture into the working bits
        pa = (lv >> self.PINA) & 1 if self.PINA < m.N_IN_PINS else 0
        pb = (lv >> self.PINB) & 1 if self.PINB < m.N_IN_PINS else 0
        w = self.W
        if tap[0]:
            w = (w & ~0b0001) | pa
        if tap[1]:
            w = (w & ~0b1010) | (pa << 1) | (pb << 3)
        if tap[2]:
            w = (w & ~0b0100) | (pa << 2)
        self.w_next = w
        self.snap = self.beat if self.SNAP == 3 else tap[self.SNAP]

    # ---------------------------------------------------------------- phase 2
    def commit(self, ctl, sym):
        """ctl: L.CTL move value or None. sym: new STAGED value from the winning symbol write, or None."""
        self.run_t = self.RUN
        in1 = self.IN >> 1
        self.PH = self.PRE if (self.start or self.accept) else (self.nx if self.adv else self.PH)
        self.RUN = int(self.RUN or self.start)
        self.ARM = int(self.ARM and not self.start)
        if self.FOLLOW:
            self.SC = 0
            self.SP = 1 if self.beat else (0 if self.wrap else self.SP)
        else:
            self.SP = self.SC if self.beat else self.SP
            self.SC = 1 if self.accept else (0 if self.beat else self.SC)
        if ctl is not None:
            self.RUN, self.ARM, self.REN = ctl & 1, (ctl >> 1) & 1, (ctl >> 2) & 1
        if sym is not None:
            self.STAGED = sym
        if self.beat:
            self.COMMITTED = self.STAGED
        self.FIRED = self.fired_next
        self.fix_fired()
        if self.tapmiss_ev:
            self.TAPMISS = 1
        self.W = self.w_next
        if self.snap:
            self.SN = self.w_next
            self.REM = in1

    def fix_fired(self):
        """Apply the RUN-rising rule of SPEC 3.4 (called again after host writes to PHASE or CTL)."""
        if self.RUN and not self.run_t:
            self.FIRED = self.fired_at_start(self.PH)

    def sym_value(self, op, v):
        if op == "SYM":
            return v & 15
        if op == "DBIT":
            return (self.STAGED & 0xE) | (v & 1)
        return self.STAGED ^ (v & 15)
