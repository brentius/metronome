"""Host link: SPI target (SPEC 9) and the host mailbox."""
from . import pins as P
from . import regs

NOCMD, WRITE, READ, IGNORE = 0, 1, 2, 3


class Host:
    def __init__(self):
        self.reset()

    def reset(self):
        self.INB = self.OUTB = 0
        self.INV = self.OUTV = self.INVP = 0
        self.RX = self.TX = 0
        self.bitcnt = self.bytecnt = 0
        self.cmd = NOCMD
        self.ADDR = 0
        self.HRD = 0
        self.txpend = 0
        self.MISO = self.IRQ = 0
        # per-cycle scratch
        self.wr = None            # (addr, byte) host register write completing this cycle
        self.rd_effect = False    # a HOSTOUT read happened this cycle
        self.newreq = None        # data-RAM request for the arbiter
        self.hrd_next = None      # new HRD value from a register read

    def _issue_read(self, ch, a):
        d = regs.decode(a)
        if d is not None and d[0] == "data":
            self.newreq = ("R", d[2])
        else:
            self.hrd_next = regs.read(ch, a)
            if regs.read_effect(ch, a):
                self.rd_effect = True

    def comb(self, ch, rs_host, fl_host, s2):
        """Phase 1: advance the link; defer register effects (self.wr / rd_effect / newreq / hrd_next)."""
        self.wr = None
        self.rd_effect = False
        self.newreq = None
        self.hrd_next = None
        cs = not (s2 >> P.CSN_BIT) & 1
        self.MISO_next = 0
        if not cs:
            self.bitcnt = self.bytecnt = 0
            self.TX = 0
            self.cmd = NOCMD
            self.txpend = 0
            return
        self.MISO_next = (self.TX >> 7) & 1
        if rs_host:
            mosi = (s2 >> P.MOSI_BIT) & 1
            val = ((self.RX << 1) | mosi) & 0xFF
            self.RX = val
            self.bitcnt += 1
            if self.bitcnt == 8:
                self.bitcnt = 0
                self._byte(ch, val)
        elif fl_host:
            if self.txpend:
                self.TX = self.HRD
                self.txpend = 0
                self._issue_read(ch, self.ADDR)
                self.ADDR = (self.ADDR + 1) & 0xFFFF
            else:
                self.TX = (self.TX << 1) & 0xFF

    def _byte(self, ch, val):
        i = self.bytecnt
        self.bytecnt = min(i + 1, 255)
        if i == 0:
            self.cmd = WRITE if val == 0x02 else (READ if val == 0x03 else IGNORE)
        elif self.cmd in (NOCMD, IGNORE):
            return
        elif i == 1:
            self.ADDR = (val << 8) | (self.ADDR & 0xFF)
        elif i == 2:
            self.ADDR = (self.ADDR & 0xFF00) | val
            if self.cmd == READ:
                self._issue_read(ch, self.ADDR)
                self.ADDR = (self.ADDR + 1) & 0xFFFF
                self.txpend = 1
        elif self.cmd == WRITE:
            self.wr = (self.ADDR, val)
            self.ADDR = (self.ADDR + 1) & 0xFFFF
        else:
            self.txpend = 1
