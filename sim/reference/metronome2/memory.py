"""Data RAM, arbiter (SPEC v2 6.2), pointer P0 (SPEC v1 6.1 and 9a.2-9a.4) and streams (SPEC v2 6.3)."""
from .md import m

MASK11 = (1 << 11) - 1


def _le(b, off, n):
    return int.from_bytes(bytes(b[off:off + n]), "little")


class Pointer:
    def __init__(self, k):
        self.k = k
        self.reset()

    def reset(self):
        self.PTR = 0
        self.D = 0
        self.RDY = 0
        self.req = None        # None | ("F",) | ("W", addr, data)
        self.pipe = None       # fetched byte in flight, lands at the end of the next cycle
        self.stale = False     # SPEC v1 9a.3

    def request(self):
        if self.req is None:
            return None
        return ("R", self.PTR) if self.req[0] == "F" else self.req

    def op(self, name, v, served):
        """Apply a pointer move; returns True when it overwrote a pending, unserved request (MEMHAZ)."""
        if name == "AL":
            self.PTR = (self.PTR & 0x700) | v
            new = ("F",)
        elif name == "AH":
            self.PTR = (self.PTR & 0x0FF) | ((v & 7) << 8)
            new = ("F",)
        elif name == "W":
            new = ("W", self.PTR, v)
            self.PTR = (self.PTR + 1) & MASK11
        else:  # R
            self.PTR = (self.PTR + 1) & MASK11
            new = ("F",)
        self.RDY = 0
        if self.pipe is not None:
            self.stale = True
        hazard = self.req is not None and not served
        self.req = new
        return hazard


class Stream:
    STRIDE = m.HOST_STRIDE["STREAM"]

    def __init__(self, k):
        self.k = k
        self.cfg = bytearray(self.STRIDE)
        self.reset()

    def decode(self):
        b = self.cfg
        self.MODE, self.MSB = b[0] & 1, (b[0] >> 1) & 1
        self.START = _le(b, 1, 2) & 0x7FF
        self.LEN = _le(b, 3, 2) & 0xFFF
        self.MARK = _le(b, 5, 2) & 0xFFF

    def reset(self):
        self.cfg[:] = bytes(self.STRIDE)
        self.decode()
        self.POS = self.BIDX = self.BA = 0
        self.CUR = self.CV = 0
        self.WB = self.WV = 0
        self.RQ = self.LD = 0
        self.PEND = self.PV = 0
        self.STARVED = 0
        self.rdword = 0          # word read when served, delivered at the end of the next cycle (LD)

    # ---------------------------------------------------------------- sources and guards
    @property
    def END(self):
        return int(self.POS == self.LEN)

    @property
    def BIT(self):
        if self.MODE or not self.CV or self.END:
            return 0
        b = 7 - self.BIDX if self.MSB else self.BIDX
        return (self.CUR >> b) & 1

    @property
    def BYTE(self):
        return self.PEND if self.MODE else self.CUR

    @property
    def G_MARK(self):
        return int(self.POS == self.MARK and self.BIDX == 0)

    @property
    def G_BYTE(self):
        return int(self.BIDX == 0)

    def request(self):
        if self.MODE:
            return ("W", self.BA, self.PEND) if self.PV else None
        return ("R", self.BA) if self.RQ else None

    # ---------------------------------------------------------------- phase 2
    def commit(self, g, word, adv, rx, ctl):
        """g: served this cycle; word: the RAM word read if g and transmit; adv: ADV move; rx: RX move bit or None;
        ctl: OR of CTL requests (move value and host bits) or None. Returns True on a starve event."""
        ctl = ctl or 0
        starve = False
        end = self.POS == self.LEN
        lane = self.BA & 3
        lb = (self.WB >> (8 * lane)) & 0xFF
        b = 7 - self.BIDX if self.MSB else self.BIDX
        if not self.MODE:
            WB, WV, LD, RQ = self.WB, self.WV, self.LD, self.RQ
            if self.LD:
                WB, WV, LD = self.rdword, 1, 0
            if self.RQ and g:
                RQ, LD = 0, 1
                self.rdword = word
            elif not self.WV and not self.RQ and not self.LD:
                RQ = 1
            advance = adv and not end
            CUR, CV, BA, POS, BIDX = self.CUR, self.CV, self.BA, self.POS, self.BIDX
            if advance and not self.CV:
                starve = True
            if not self.CV and self.WV:
                CUR, CV, BA = lb, 1, (self.BA + 1) & MASK11
                if lane == 3:
                    WV = 0
            elif advance and self.CV:
                if self.BIDX != 7:
                    BIDX = self.BIDX + 1
                else:
                    POS, BIDX = (self.POS + 1) & 0xFFF, 0
                    if self.WV:
                        CUR, BA = lb, (self.BA + 1) & MASK11
                        if lane == 3:
                            WV = 0
                    else:
                        CV = 0
                        starve = True
            self.WB, self.WV, self.LD, self.RQ = WB, WV, LD, RQ
            self.CUR, self.CV, self.BA, self.POS, self.BIDX = CUR, CV, BA, POS, BIDX
        else:
            bitin = rx is not None and not end
            flush = bool(ctl & 2) and not end
            nsh = self.CUR | (((rx or 0) & 1 and bitin) << b)
            done = (bitin and self.BIDX == 7) or (flush and (self.BIDX != 0 or bitin))
            PV, BA, CUR, BIDX, POS, PEND = self.PV, self.BA, self.CUR, self.BIDX, self.POS, self.PEND
            if self.PV and g:
                PV, BA = 0, (self.BA + 1) & MASK11
            if bitin and not done:
                CUR, BIDX = nsh, self.BIDX + 1
            if done:
                CUR, BIDX, POS = 0, 0, (self.POS + 1) & 0xFFF
                if self.PV and not g:
                    starve = True
                else:
                    PEND, PV = nsh, 1
            self.PV, self.BA, self.CUR, self.BIDX, self.POS, self.PEND = PV, BA, CUR, BIDX, POS, PEND
        if ctl & 0x80:
            self.STARVED = 0
        if starve:
            self.STARVED = 1
        if ctl & 1:
            self.POS = self.BIDX = 0
            self.BA = self.START
            self.CUR = self.CV = self.WV = self.RQ = self.LD = self.PV = 0
        return starve


class Memory:
    """2048-byte data RAM, one access per cycle, priority S0, S1, P0, host (SPEC v2 6.2)."""

    def __init__(self):
        self.data = bytearray(m.DATA_BYTES)
        self.ptr = Pointer(0)
        self.streams = [Stream(k) for k in range(m.N_STREAMS)]
        self.reset()

    def reset(self):
        self.ptr.reset()
        for s in self.streams:
            s.reset()
        self.host_req = None   # None | ("R", addr) | ("W", addr, data)
        self.hpipe = None
        self.served = None     # ("S", k) | "P" | "H" | None
        self.sreq = None

    def word(self, byte_addr):
        a = byte_addr & ~3 & MASK11
        return int.from_bytes(self.data[a:a + 4], "little")

    def arbitrate(self):
        self.served = None
        self.sreq = None
        for k, s in enumerate(self.streams):
            r = s.request()
            if r is not None:
                self.served, self.sreq = ("S", k), r
                return
        if self.ptr.req is not None:
            self.served = "P"
        elif self.host_req is not None:
            self.served = "H"

    def commit(self, host_newreq):
        """Phase 2 except pointer moves and stream updates. Returns (host landing byte or None, stream read word)."""
        hland, self.hpipe = self.hpipe, None
        p = self.ptr
        land, p.pipe = p.pipe, None
        if land is not None:
            p.D = land
            p.RDY = int(not p.stale)
        p.stale = False
        sword = 0
        if self.served == "P":
            r, p.req = p.req, None
            if r[0] == "W":
                self.data[r[1]] = r[2]
            else:
                p.pipe = self.data[p.PTR]
        elif self.served == "H":
            r, self.host_req = self.host_req, None
            if r[0] == "W":
                self.data[r[1]] = r[2]
            else:
                self.hpipe = self.data[r[1]]
        elif self.served is not None:
            r = self.sreq
            if r[0] == "W":
                self.data[r[1]] = r[2]
            else:
                sword = self.word(r[1])
        if host_newreq is not None:
            self.host_req = host_newreq
        return hland, sword
