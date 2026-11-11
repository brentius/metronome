"""Datapath units (SPEC 6.1): flags, accumulator, shifter, counter, LFSR."""


class Flags:
    def __init__(self):
        self.F = self.FP = 0

    def reset(self):
        self.__init__()


class Acc:
    def __init__(self):
        self.A = 0
        self.Z = self.C = self.N = 0
        self.R = [0, 0, 0, 0]

    reset = __init__

    def op(self, name, v):
        a = self.A
        if name == "LD":
            res = v
            self.A = v
        elif name == "ADD":
            r = a + v
            res = self.A = r & 0xFF
            self.C = (r >> 8) & 1
        elif name in ("SUB", "CMP"):
            r = (a - v) & 0x1FF
            res = r & 0xFF   # SPEC-AMBIGUITY: Z uses the low 8 bits of r (ADD/SUB/CMP), N is bit 7
            self.C = int(a >= v)
            if name == "SUB":
                self.A = res
        elif name == "AND":
            res = self.A = a & v
        elif name == "OR":
            res = self.A = a | v
        else:  # XOR
            res = self.A = a ^ v
        self.Z = int(res == 0)
        self.N = (res >> 7) & 1


class Shifter:
    def __init__(self):
        self.D = 0
        self.CNT = 0
        self.LEN = 0
        self.MSB = 0

    reset = __init__

    @property
    def out(self):
        return (self.D >> 7) & 1 if self.MSB else self.D & 1

    @property
    def done(self):
        return int(self.CNT == 0)

    def ld(self, v):
        self.D = v
        self.CNT = self.LEN if self.LEN else 8

    def sh(self, v):
        if self.MSB:
            self.D = ((self.D << 1) & 0xFF) | (v & 1)
        else:
            self.D = (self.D >> 1) | ((v & 1) << 7)
        self.CNT = self.CNT - 1 if self.CNT else 0

    def cfg(self, v):
        self.LEN = v & 0xF
        self.MSB = (v >> 4) & 1


class Counter:
    def __init__(self):
        self.V = 0

    reset = __init__

    def op(self, name, v):
        if name == "LO":
            self.V = (self.V & 0xFF00) | v
        elif name == "HI":
            self.V = (self.V & 0x00FF) | (v << 8)
        else:
            self.V = self.V - 1 if self.V else 0


class Lfsr:
    def __init__(self):
        self.S = 0
        self.POLY = 0

    def reset(self):
        self.S = 0
        self.POLY = 0

    def step(self, v):
        fb = (self.S ^ v) & 1
        self.S = (self.S >> 1) ^ (self.POLY if fb else 0)

    def set_byte(self, b, v):
        self.S = (self.S & ~(0xFF << 8 * b)) | (v << 8 * b)
