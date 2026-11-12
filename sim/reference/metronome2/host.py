"""Host link: SPI target (SPEC v2 9) and the host mailbox registers."""
from . import regs

SCK_BIT, CSN_BIT, MOSI_BIT = 8, 9, 10      # bit positions in the raw 16-bit input vector (ui_in << 8 | uio_in)
CMD, AH, AL, DATA, IGN = range(5)


class Host:
    def __init__(self):
        self.reset()

    def reset(self):
        self.INB = self.OUTB = self.INV = self.OUTV = self.INVP = 0
        self.RX = self.bitcnt = 0
        self.st = CMD
        self.is_rd = 0
        self.ADDR = 0
        self.TX = 0
        self.WR = None        # data byte of a host write in this cycle (cycle W), address ADDR
        self.RD = 0           # a read request at ADDR in this cycle (cycle R)
        self.rack = None      # register value read in R, loaded into TX at the end of R+1
        self.IRQ = 0

    @property
    def MISO(self):
        return (self.TX >> 7) & 1

    def comb(self, ch, s2, sp):
        """Phase 1: decode the strobes of this cycle and the link's next state."""
        self.wr_now = None
        self.newreq = None
        self.rack_next = None
        if self.WR is not None:
            self.wr_now = (self.ADDR, self.WR)
            d = regs.decode(self.ADDR)
            if d is not None and d[0] == "data":
                self.newreq = ("W", d[2], self.WR)
        if self.RD:
            d = regs.decode(self.ADDR)
            if d is not None and d[0] == "data":
                self.newreq = ("R", d[2])
            else:
                self.rack_next = regs.read(ch, self.ADDR)
        cs = not ((s2 >> CSN_BIT) & 1)
        self.sr = cs and ((s2 >> SCK_BIT) & 1) and not ((sp >> SCK_BIT) & 1)
        self.cs = cs
        self.mosi = (s2 >> MOSI_BIT) & 1

    def commit(self, hland):
        """Phase 2 for the link state. hland: data RAM byte landing this cycle (or None)."""
        ack = self.rack if self.rack is not None else hland
        addr = self.ADDR
        if self.WR is not None or ack is not None:
            addr = (self.ADDR + 1) & 0xFFFF
        tx = ack if ack is not None else self.TX
        wr = None
        rd = 0
        if not self.cs:
            self.st, self.bitcnt, tx = CMD, 0, 0
        elif self.sr:
            byte = ((self.RX << 1) | self.mosi) & 0xFF
            self.RX = byte & 0x7F
            if self.bitcnt != 7:
                tx = (self.TX << 1) & 0xFF
                self.bitcnt += 1
            else:
                self.bitcnt = 0
                if self.st == CMD:
                    self.is_rd = int(byte == 0x03)
                    self.st = AH if byte in (0x02, 0x03) else IGN
                elif self.st == AH:
                    addr = (addr & 0x00FF) | (byte << 8)
                    self.st = AL
                elif self.st == AL:
                    addr = (addr & 0xFF00) | byte
                    self.st = DATA
                    rd = self.is_rd
                elif self.st == DATA:
                    if self.is_rd:
                        rd = 1
                    else:
                        wr = byte
        self.ADDR, self.TX, self.WR, self.RD = addr, tx, wr, rd
        self.rack = self.rack_next
