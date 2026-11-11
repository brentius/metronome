"""Input synchronisers (SPEC 2). Raw 16-bit vector: bits 0..7 = uio_in, bits 8..15 = ui_in."""
import machine as m

# bit position inside the raw vector of protocol input pin P_k (k < 13): P0..P7 = uio[0..7], P8..P12 = ui[3..7]
PIN_BIT = [k if k < 8 else k + 3 for k in range(m.N_IN_PINS)]
SCK_BIT, CSN_BIT, MOSI_BIT = 8, 9, 10      # ui_in[0..2]


class Pins:
    def __init__(self):
        self.reset()

    def reset(self):
        self.s1 = self.s2 = self.sp = 0

    def levels(self):
        """Return (LV, RS, FL): bit k = level / rise / fall of protocol pin k (bits 13..15 are always 0)."""
        lv = rs = fl = 0
        s2, sp = self.s2, self.sp
        for k, b in enumerate(PIN_BIT):
            c, p = (s2 >> b) & 1, (sp >> b) & 1
            lv |= c << k
            rs |= (c & ~p & 1) << k
            fl |= ((~c & 1) & p) << k
        return lv, rs, fl

    def shift(self, raw):
        self.sp, self.s2, self.s1 = self.s2, self.s1, raw
