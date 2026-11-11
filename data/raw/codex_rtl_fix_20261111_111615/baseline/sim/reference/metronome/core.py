"""Cores (SPEC 5), source/destination/guard tables (SPEC 6, 7)."""
import re
import machine as m
import encode

# ----------------------------------------------------------------------------------------------------------------
# Instruction decode (cached per 64-bit word). Out-of-range indices decode like encode.decode: SRC -> ZERO,
# DST -> NULL, guard condition -> TRUE.  # SPEC-AMBIGUITY: SPEC does not define unassigned indices.
# ----------------------------------------------------------------------------------------------------------------
_decode_cache = {}


def decode_word(w):
    d = _decode_cache.get(w)
    if d is None:
        f = encode.fields(w)
        moves = []
        for i in range(m.N_MOVES):
            s, t = f[f"m{i}_src"], f[f"m{i}_dst"]
            moves.append((f[f"m{i}_guard"], s if s < len(m.SRC) else 0, t if t < len(m.DST) else 0))
        c = f["cond"]
        d = (f["pause"], f["jmode"], f["imm"], c if c < len(m.GUARD_CONDS) else len(m.GUARD_CONDS), tuple(moves))
        _decode_cache[w] = d
    return d


# ----------------------------------------------------------------------------------------------------------------
# Sources: SRC_FN[i](ch, e, imm) -> value read in cycle t. SRC_EFFECT[i]: None | ("hostin",) | ("pd", k)
# ----------------------------------------------------------------------------------------------------------------
def _k(pattern, name):
    mt = re.fullmatch(pattern, name)
    return tuple(int(x) for x in mt.groups()) if mt else None


def _build_src():
    fns, eff = [], []
    for p in m.SRC:
        n = p.name
        e_ = None
        if n == "ZERO":
            f = lambda ch, e, imm: 0
        elif n == "IMM":
            f = lambda ch, e, imm: imm
        elif n == "E.IN":
            f = lambda ch, e, imm: ch.eng[e].IN
        elif n == "E.CAP":
            f = lambda ch, e, imm: ch.eng[e].CAP
        elif n == "FLAGS.LO":
            f = lambda ch, e, imm: ch.flags.F & 0xFF
        elif n == "FLAGS.HI":
            f = lambda ch, e, imm: ch.flags.F >> 8
        elif n == "PINS.LO":
            f = lambda ch, e, imm: ch.lv & 0xFF
        elif n == "PINS.HI":
            f = lambda ch, e, imm: (ch.lv >> 8) & 0x1F
        elif n == "ACC":
            f = lambda ch, e, imm: ch.acc.A
        elif (a := _k(r"R(\d)", n)):
            f = (lambda k: lambda ch, e, imm: ch.acc.R[k])(*a)
        elif (a := _k(r"SH(\d)\.D", n)):
            f = (lambda k: lambda ch, e, imm: ch.sh[k].D)(*a)
        elif (a := _k(r"SH(\d)\.O", n)):
            f = (lambda k: lambda ch, e, imm: ch.sh[k].out)(*a)
        elif (a := _k(r"CNT(\d)\.LO", n)):
            f = (lambda k: lambda ch, e, imm: ch.cnt[k].V & 0xFF)(*a)
        elif (a := _k(r"CNT(\d)\.HI", n)):
            f = (lambda k: lambda ch, e, imm: ch.cnt[k].V >> 8)(*a)
        elif (a := _k(r"LF(\d)\.B(\d)", n)):
            f = (lambda k, b: lambda ch, e, imm: (ch.lf[k].S >> 8 * b) & 0xFF)(*a)
        elif (a := _k(r"P(\d)\.D", n)):
            f = (lambda k: lambda ch, e, imm: ch.mem.ptrs[k].D)(*a)
            e_ = ("pd", a[0])
        elif n == "HOST.IN":
            f = lambda ch, e, imm: ch.host.INB
            e_ = ("hostin",)
        else:
            raise AssertionError(n)
        fns.append(f)
        eff.append(e_)
    return fns, eff


SRC_FN, SRC_EFFECT = _build_src()


# ----------------------------------------------------------------------------------------------------------------
# Guards: GUARD_FN[i](ch, e) -> 0/1 evaluated on cycle-t state for engine e
# ----------------------------------------------------------------------------------------------------------------
def _build_guards():
    fns = []
    for p in m.GUARD_CONDS:
        n = p.name
        if n == "TRUE":
            f = lambda ch, e: 1
        elif (a := _k(r"F(\d+)", n)):
            f = (lambda k: lambda ch, e: (ch.flags.F >> k) & 1)(*a)
        elif (a := _k(r"SH(\d)\.DONE", n)):
            f = (lambda k: lambda ch, e: ch.sh[k].done)(*a)
        elif (a := _k(r"SH(\d)\.OUT", n)):
            f = (lambda k: lambda ch, e: ch.sh[k].out)(*a)
        elif (a := _k(r"CNT(\d)\.Z", n)):
            f = (lambda k: lambda ch, e: int(ch.cnt[k].V == 0))(*a)
        elif n == "ACC.Z":
            f = lambda ch, e: ch.acc.Z
        elif n == "ACC.C":
            f = lambda ch, e: ch.acc.C
        elif n == "ACC.N":
            f = lambda ch, e: ch.acc.N
        elif n == "E.IN0":
            f = lambda ch, e: ch.eng[e].IN & 1
        elif n == "E.IN1":
            f = lambda ch, e: (ch.eng[e].IN >> 1) & 1
        elif n == "E.SYNC":
            f = lambda ch, e: ch.bg[ch.eng[e].BG].SP
        elif n == "E.PINA":
            f = lambda ch, e: (ch.lv >> ch.eng[e].PINA) & 1
        elif n == "E.PINB":
            f = lambda ch, e: (ch.lv >> ch.eng[e].PINB) & 1
        elif (a := _k(r"LF(\d)\.OUT", n)):
            f = (lambda k: lambda ch, e: ch.lf[k].S & 1)(*a)
        elif n == "HOST.INV":
            f = lambda ch, e: ch.host.INV
        elif n == "HOST.OUTE":
            f = lambda ch, e: int(not ch.host.OUTV)
        elif (a := _k(r"P(\d)\.RDY", n)):
            f = (lambda k: lambda ch, e: ch.mem.ptrs[k].RDY)(*a)
        elif (a := _k(r"PIN(\d+)", n)):
            f = (lambda k: lambda ch, e: (ch.lv >> k) & 1)(*a)
        elif (a := _k(r"BG(\d)\.RUN", n)):
            f = (lambda k: lambda ch, e: ch.bg[k].RUN)(*a)
        else:
            raise AssertionError(n)
        fns.append(f)
    return fns


GUARD_FN = _build_guards() + [lambda ch, e: 0]   # index len(GUARD_CONDS): unused encodings are false (SPEC 9a.1)


# ----------------------------------------------------------------------------------------------------------------
# Destinations: DST_INFO[i] = (kind, k, op). The write group of a move is (kind, k) -- or (kind, executing engine)
# for E.SYM / E.STOP.
# ----------------------------------------------------------------------------------------------------------------
def _build_dst():
    info = []
    for p in m.DST:
        n = p.name
        if n == "NULL":
            t = ("NULL", 0, "")
        elif n == "E.SYM":
            t = ("ESYM", 0, "")
        elif n == "E.STOP":
            t = ("ESTOP", 0, "")
        elif n in ("FLAGS.SET", "FLAGS.CLR"):
            t = ("FLAGS", 0, n.split(".")[1])
        elif n.startswith("ACC."):
            t = ("ACC", 0, n.split(".")[1])
        elif (a := _k(r"R(\d)", n)):
            t = ("R", a[0], "")
        elif (mt := re.fullmatch(r"SH(\d)\.(LD|SH)", n)):
            t = ("SHLS", int(mt.group(1)), mt.group(2))
        elif (a := _k(r"SH(\d)\.CFG", n)):
            t = ("SHCFG", a[0], "")
        elif (mt := re.fullmatch(r"CNT(\d)\.(LO|HI|DEC)", n)):
            t = ("CNT", int(mt.group(1)), mt.group(2))
        elif (a := _k(r"LF(\d)\.ST", n)):
            t = ("LF", a[0], "ST")
        elif (a := _k(r"LF(\d)\.B(\d)", n)):
            t = ("LF", a[0], a[1])
        elif (mt := re.fullmatch(r"P(\d)\.(AL|AH|W|R)", n)):
            t = ("P", int(mt.group(1)), mt.group(2))
        elif (a := _k(r"BG(\d)\.CTL", n)):
            t = ("BG", a[0], "")
        elif n == "HOST.OUT":
            t = ("HOSTOUT", 0, "")
        else:
            raise AssertionError(n)
        info.append(t)
    return info


DST_INFO = _build_dst()


class Core:
    def __init__(self, c):
        self.c = c
        self.mem = [0] * m.PROG_WORDS
        self.reset()

    def reset(self):
        self.XV = 0
        self.XE = 0
        self.XPC = 0
        self.iaddr = 0       # address registered for the synchronous read of the program memory
        self.moves = []
        self.next = None
        self.dispatch = None
        self.pause = None

    @property
    def I(self):
        return self.mem[self.iaddr]

    def plan(self, ch):
        """Phase 1: enabled moves (with source values read now) and the next core state."""
        self.moves = []
        self.dispatch = None
        self.pause = None
        free = not self.XV
        nxt = (self.XV, self.XPC, self.XE, self.iaddr)
        if self.XV:
            e = self.XE
            pause, jmode, imm, cond, mvs = decode_word(self.mem[self.iaddr])
            C = GUARD_FN[cond](ch, e)
            for i, (g, src, dst) in enumerate(mvs):
                if g == 0 or (g == 1 and C) or (g == 2 and not C):
                    val = SRC_FN[src](ch, e, imm)
                    eff = SRC_EFFECT[src]
                    if eff is not None:
                        ch.src_effect(eff)
                    self.moves.append((self.c, i, dst, val, e))
            taken = jmode == 1 or (jmode == 2 and C) or (jmode == 3 and not C)
            npc = imm if taken else (self.XPC + 1) & 0xFF
            if pause:
                self.pause = (e, npc)
                free = True
            else:
                nxt = (1, npc, e, npc)
        if free:
            nxt = (0, self.XPC, self.XE, self.iaddr)
            if ch.ctrl.RUN:
                for e2, eng in enumerate(ch.eng):
                    if eng.CORE == self.c and eng.READY:
                        # SPEC 9a.1: a watcher guard index beyond the guard table is false
                        w0 = eng.W0C and eng.W0C < len(GUARD_FN) and GUARD_FN[eng.W0C](ch, e2)
                        w1 = eng.W1C and eng.W1C < len(GUARD_FN) and GUARD_FN[eng.W1C](ch, e2)
                        d = eng.W0H if w0 else (eng.W1H if w1 else eng.PC)
                        nxt = (1, d, e2, d)
                        self.dispatch = e2
                        break
        self.next = nxt

    def commit(self):
        self.XV, self.XPC, self.XE, self.iaddr = self.next
