"""Pointers, data RAM and the memory arbiter (SPEC 6.1)."""
import machine as m

MASK11 = (1 << 11) - 1


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
        self.stale = False     # SPEC 9a.3: a request-setting move in the serve cycle makes the landing stale

    def op(self, name, v, served):
        """Apply a pointer move; returns True when it overwrote a pending, unserved request (MEMHAZ)."""
        hazard = False
        if name == "AL":
            self.PTR = (self.PTR & 0x700) | v
            self.RDY = 0
            new = ("F",)
        elif name == "AH":
            self.PTR = (self.PTR & 0x0FF) | ((v & 7) << 8)
            self.RDY = 0
            new = ("F",)
        elif name == "W":
            new = ("W", self.PTR, v)
            self.PTR = (self.PTR + 1) & MASK11
            self.RDY = 0
        else:  # R
            self.PTR = (self.PTR + 1) & MASK11
            self.RDY = 0
            new = ("F",)
        if self.pipe is not None:      # fetch served this cycle: its landing will not set RDY
            self.stale = True
        # SPEC-AMBIGUITY: a request served in this very cycle is not "pending"; only an unserved one is overwritten.
        if self.req is not None and not served:
            hazard = True
        self.req = new
        return hazard


class Memory:
    """2048-byte data RAM with one access per cycle, priority P0, P1, host."""

    def __init__(self):
        self.data = bytearray(m.DATA_BYTES)
        self.ptrs = [Pointer(k) for k in range(m.N_PTRS)]
        self.reset()

    def reset(self):
        for p in self.ptrs:
            p.reset()
        self.host_req = None   # None | ("R", addr) | ("W", addr, data)
        self.hpipe = None      # byte read for the host, lands in HRD at the end of the next cycle
        self.served = None     # who is served in the current cycle: 0, 1, "H" or None

    def arbitrate(self):
        self.served = None
        for k, p in enumerate(self.ptrs):
            if p.req is not None:
                self.served = k
                return
        if self.host_req is not None:
            self.served = "H"

    def commit(self, host_newreq):
        """Phase 2 for everything except the pointer moves (applied afterwards via Pointer.op)."""
        hland = self.hpipe
        self.hpipe = None
        for k, p in enumerate(self.ptrs):
            land, p.pipe = p.pipe, None
            if land is not None:
                p.D = land
                p.RDY = int(not p.stale)
            p.stale = False
            if self.served == k:
                r, p.req = p.req, None
                if r[0] == "W":
                    self.data[r[1]] = r[2]
                else:
                    p.pipe = self.data[p.PTR]
        if self.served == "H":
            r, self.host_req = self.host_req, None
            if r[0] == "W":
                self.data[r[1]] = r[2]
            else:
                self.hpipe = self.data[r[1]]
        if host_newreq is not None:
            self.host_req = host_newreq
        return hland
