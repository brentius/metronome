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
        self.CEN = 0             # v3: edge capture on this stream (S0 only; set by Chip each cycle, SPEC v2 12.4)
        self.RPL = 0             # v4: edge replay from this stream (S0 only; set by Chip each cycle, SPEC v2 13.2)
        self.NB = self.NV = 0    # v4 replay: second record buffer

    # ---------------------------------------------------------------- sources and guards
    @property
    def END(self):
        return int(self.POS == self.LEN)

    @property
    def BIT(self):
        if self.CEN or self.RPL or self.MODE or not self.CV or self.END:
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
        if self.RPL:
            return ("R", self.BA) if self.RQ else None
        if self.CEN:
            return ("WW", self.BA, self.WB) if self.PV else None
        if self.MODE:
            return ("W", self.BA, self.PEND) if self.PV else None
        return ("R", self.BA) if self.RQ else None

    # ---------------------------------------------------------------- phase 2
    def commit(self, g, word, adv, rx, ctl, rec=None, rpl=None):
        """g: served this cycle; word: the RAM word read if g and transmit; adv: ADV move; rx: RX move bit or None;
        ctl: OR of CTL requests (move value and host bits) or None; rec: v3 edge-capture record pushed this cycle
        or None (SPEC v2 12.4). Returns True on a starve event."""
        ctl = ctl or 0
        starve = False
        end = self.POS == self.LEN
        if self.RPL:
            return self._commit_replay(g, word, ctl, end, *(rpl or (False, False)))
        if self.CEN:
            return self._commit_capture(g, rec, ctl, end)
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


def _capture_commit(self, g, rec, ctl, end):
    """Capture mode (SPEC v2 12.4): ADV, RX and flush have no effect; records are whole-word writes."""
    starve = False
    PV, BA, POS, WB = self.PV, self.BA, self.POS, self.WB
    if self.PV and g:
        PV, BA = 0, (self.BA + 4) & MASK11
    if rec is not None and not end:
        if self.PV and not g:
            starve = True
        else:
            WB, PV, POS = rec, 1, (self.POS + 4) & 0xFFF
    self.PV, self.BA, self.POS, self.WB = PV, BA, POS, WB
    if ctl & 0x80:
        self.STARVED = 0
    if starve:
        self.STARVED = 1
    if ctl & 1:
        self.POS = self.BIDX = 0
        self.BA = self.START
        self.CUR = self.CV = self.WV = self.RQ = self.LD = self.PV = 0
    return starve


Stream._commit_capture = _capture_commit


def _replay_commit(self, g, word, ctl, end, consume, late):
    """Replay mode (SPEC v2 13.2): whole-word record reads into a two-deep buffer (WB, then NB); ADV, RX and flush
    have no effect. consume: the record in WB is applied this cycle; late: it was applied after its time."""
    WB, WV, NB, NV, RQ, LD = self.WB, self.WV, self.NB, self.NV, self.RQ, self.LD
    BA, POS = self.BA, self.POS
    if consume:
        WB, WV, NV = NB, NV, 0
    if self.LD:
        if not WV:
            WB, WV = self.rdword, 1
        else:
            NB, NV = self.rdword, 1
        LD = 0
    if self.RQ and g:
        RQ, LD = 0, 1
        self.rdword = word
        BA, POS = (self.BA + 4) & MASK11, (self.POS + 4) & 0xFFF
    elif not self.RQ and not self.LD and not end and not (self.WV and self.NV):
        RQ = 1
    self.WB, self.WV, self.NB, self.NV, self.RQ, self.LD, self.BA, self.POS = WB, WV, NB, NV, RQ, LD, BA, POS
    if ctl & 0x80:
        self.STARVED = 0
    if late:
        self.STARVED = 1
    if ctl & 1:
        self.POS = self.BIDX = 0
        self.BA = self.START
        self.CUR = self.CV = self.WV = self.RQ = self.LD = self.PV = self.NV = 0
    return late


Stream._commit_replay = _replay_commit


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
            elif r[0] == "WW":                     # v3 edge-capture record: one word, all four lanes
                a = r[1] & ~3 & MASK11
                self.data[a:a + 4] = (r[2] & 0xFFFFFFFF).to_bytes(4, "little")
            else:
                sword = self.word(r[1])
        if host_newreq is not None:
            self.host_req = host_newreq
        return hland, sword

    def commit_frozen(self, host_newreq, frzd):
        """A frozen cycle (SPEC v2 12.3): only the host request is served; streams and the pointer hold, except
        that a pointer read served in the last unfrozen cycle has its byte captured into D (the landing exception;
        RDY follows in the first unfrozen cycle). A stream's captured word (WB) is invisible while LD, so the
        model keeps it in rdword."""
        hland, self.hpipe = self.hpipe, None
        p = self.ptr
        if p.pipe is not None and not frzd:
            p.D = p.pipe
        self.served = None
        if self.host_req is not None:
            self.served = "H"
            r, self.host_req = self.host_req, None
            if r[0] == "W":
                self.data[r[1]] = r[2]
            else:
                self.hpipe = self.data[r[1]]
        if host_newreq is not None:
            self.host_req = host_newreq
        return hland
