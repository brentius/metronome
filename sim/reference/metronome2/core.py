"""Threads (SPEC v2 4), cores (5), sources, destinations, guards (6, 7)."""
import re

from .md import m

F = m.FIELD


def field(w, name):
    f = F[name]
    return (w >> f.lsb) & ((1 << f.width) - 1)


_decode_cache = {}


def decode_word(w):
    """(pause, jmode, imm, cond, jcond, moves[(guard, src, dst)]); out-of-table indices handled by the users."""
    d = _decode_cache.get(w)
    if d is None:
        moves = tuple((field(w, f"m{i}_guard"), field(w, f"m{i}_src"), field(w, f"m{i}_dst")) for i in range(m.N_MOVES))
        d = (field(w, "pause"), field(w, "jmode"), field(w, "imm"), field(w, "cond"), field(w, "jcond"), moves)
        _decode_cache[w] = d
    return d


def _k(pattern, name):
    mt = re.fullmatch(pattern, name)
    return tuple(int(x) for x in mt.groups()) if mt else None


# ----------------------------------------------------------------------------------------------------------------
# Sources: SRC_FN[i](ch, line, imm) -> value; SRC_EFFECT[i]: None | "hostin" | "pd"
# ----------------------------------------------------------------------------------------------------------------
def _build_src():
    fns, eff = [], []
    for p in m.SRC:
        n, e_ = p.name, None
        if n == "ZERO":
            f = lambda ch, l, imm: 0
        elif n == "IMM":
            f = lambda ch, l, imm: imm
        elif n == "L.IN":
            f = lambda ch, l, imm: ch.lines[l].IN
        elif n == "L.CAP":
            f = lambda ch, l, imm: ch.lines[l].CAP
        elif n == "FLAGS.LO":
            f = lambda ch, l, imm: ch.flags.F & 0xFF
        elif n == "FLAGS.HI":
            f = lambda ch, l, imm: ch.flags.F >> 8
        elif n == "PINS.LO":
            f = lambda ch, l, imm: ch.lv & 0xFF
        elif n == "PINS.HI":
            f = lambda ch, l, imm: (ch.lv >> 8) & 0x1F
        elif n == "ACC":
            f = lambda ch, l, imm: ch.acc.A
        elif (a := _k(r"R(\d)", n)):
            f = (lambda k: lambda ch, l, imm: ch.acc.R[k])(*a)
        elif (a := _k(r"SH(\d)\.D", n)):
            f = (lambda k: lambda ch, l, imm: ch.sh[k].D)(*a)
        elif (a := _k(r"SH(\d)\.O", n)):
            f = (lambda k: lambda ch, l, imm: ch.sh[k].out)(*a)
        elif (a := _k(r"CNT(\d)\.LO", n)):
            f = (lambda k: lambda ch, l, imm: ch.cnt[k].V & 0xFF)(*a)
        elif (a := _k(r"CNT(\d)\.HI", n)):
            f = (lambda k: lambda ch, l, imm: ch.cnt[k].V >> 8)(*a)
        elif (a := _k(r"LF(\d)\.B(\d)", n)):
            f = (lambda k, b: lambda ch, l, imm: (ch.lf[k].S >> 8 * b) & 0xFF)(*a)
        elif (a := _k(r"LF(\d)\.O", n)):
            f = (lambda k: lambda ch, l, imm: ch.lf[k].S & 1)(*a)
        elif n == "P0.D":
            f = lambda ch, l, imm: ch.mem.ptr.D
            e_ = "pd"
        elif (a := _k(r"S(\d)\.BIT", n)):
            f = (lambda k: lambda ch, l, imm: ch.mem.streams[k].BIT)(*a)
        elif (a := _k(r"S(\d)\.BYTE", n)):
            f = (lambda k: lambda ch, l, imm: ch.mem.streams[k].BYTE)(*a)
        elif n == "HOST.IN":
            f = lambda ch, l, imm: ch.host.INB
            e_ = "hostin"
        else:
            raise AssertionError(n)
        fns.append(f)
        eff.append(e_)
    return fns, eff


SRC_FN, SRC_EFFECT = _build_src()


# ----------------------------------------------------------------------------------------------------------------
# Destinations: DST_INFO[i] = (kind, instance, op). Write-group key computed in Chip.
# ----------------------------------------------------------------------------------------------------------------
def _build_dst():
    info = []
    for p in m.DST:
        n = p.name
        if n == "NULL":
            info.append(("NULL", 0, ""))
        elif n in ("L.SYM", "L.DBIT", "L.XOR"):
            info.append(("LSYM", 0, n[2:]))
        elif n == "T.STOP":
            info.append(("TSTOP", 0, ""))
        elif n in ("FLAGS.SET", "FLAGS.CLR"):
            info.append(("FLAGS", 0, n[6:]))
        elif n.startswith("ACC."):
            info.append(("ACC", 0, n[4:]))
        elif (a := _k(r"R(\d)", n)):
            info.append(("R", a[0], ""))
        elif re.fullmatch(r"SH\d\.(LD|SH)", n):
            info.append(("SHLS", _k(r"SH(\d)\.\w+", n)[0], n.split(".")[1]))
        elif _k(r"SH(\d)\.CFG", n):
            info.append(("SHCFG", _k(r"SH(\d)\.CFG", n)[0], "CFG"))
        elif _k(r"CNT(\d)\.\w+", n):
            info.append(("CNT", _k(r"CNT(\d)\.\w+", n)[0], n.split(".")[1]))
        elif (a := _k(r"LF(\d)\.B(\d)", n)):
            info.append(("LF", a[0], a[1]))
        elif (a := _k(r"LF(\d)\.ST", n)):
            info.append(("LF", a[0], "ST"))
        elif n.startswith("P0."):
            info.append(("P", 0, n[3:]))
        elif _k(r"S(\d)\.\w+", n):
            info.append(("S", _k(r"S(\d)\.\w+", n)[0], n.split(".")[1]))
        elif (a := _k(r"L(\d)\.CTL", n)):
            info.append(("LCTL", a[0], "CTL"))
        elif n == "HOST.OUT":
            info.append(("HOSTOUT", 0, ""))
        else:
            raise AssertionError(n)
    return info


DST_INFO = _build_dst()
_GROUP_OF = {d: g for g, ds in m.WRITE_GROUPS.items() for d in ds}
DST_GROUP = [_GROUP_OF.get(p.name) for p in m.DST]


# ----------------------------------------------------------------------------------------------------------------
# Guards: global vector (per cycle) with line-relative entries per line.
# ----------------------------------------------------------------------------------------------------------------
G_ID = m.GUARD_ID
JMAP = [G_ID[n] for n in m.JUMP_GUARDS]
_LINE_REL = ("L.IN0", "L.IN1", "L.SYNC", "L.PINA", "L.PINB")


def guard_vector(ch):
    """Line-independent guards as a list of 64 ints (line-relative entries 0, out-of-table entries 0)."""
    g = [0] * 64
    g[G_ID["TRUE"]] = 1
    for k in range(m.N_FLAGS):
        g[G_ID[f"F{k}"]] = (ch.flags.F >> k) & 1
    for k, s in enumerate(ch.sh):
        g[G_ID[f"SH{k}.DONE"]] = s.done
        g[G_ID[f"SH{k}.OUT"]] = s.out
    for k, c in enumerate(ch.cnt):
        g[G_ID[f"CNT{k}.Z"]] = int(c.V == 0)
    g[G_ID["ACC.Z"]], g[G_ID["ACC.C"]], g[G_ID["ACC.N"]] = ch.acc.Z, ch.acc.C, ch.acc.N
    for k, lf in enumerate(ch.lf):
        g[G_ID[f"LF{k}.OUT"]] = lf.S & 1
    g[G_ID["HOST.INV"]] = ch.host.INV
    g[G_ID["HOST.OUTE"]] = int(not ch.host.OUTV)
    g[G_ID["P0.RDY"]] = ch.mem.ptr.RDY
    for k, s in enumerate(ch.mem.streams):
        g[G_ID[f"S{k}.END"]] = s.END
        g[G_ID[f"S{k}.MARK"]] = s.G_MARK
        g[G_ID[f"S{k}.BYTE"]] = s.G_BYTE
        g[G_ID[f"S{k}.BIT"]] = s.BIT
    for k in range(m.N_IN_PINS):
        g[G_ID[f"PIN{k}"]] = (ch.lv >> k) & 1
    for k, ln in enumerate(ch.lines):
        g[G_ID[f"L{k}.RUN"]] = ln.RUN
    return g


def line_guards(ch, base, l):
    g = list(base)
    ln = ch.lines[l]
    pin = lambda s: (ch.lv >> s) & 1 if s < m.N_IN_PINS else 0
    g[G_ID["L.IN0"]] = ln.IN & 1
    g[G_ID["L.IN1"]] = ln.IN >> 1
    g[G_ID["L.SYNC"]] = ln.SP
    g[G_ID["L.PINA"]] = pin(ln.PINA)
    g[G_ID["L.PINB"]] = pin(ln.PINB)
    return g


# ----------------------------------------------------------------------------------------------------------------
class Thread:
    STRIDE = m.HOST_STRIDE["THREAD"]

    def __init__(self, t):
        self.t = t
        self.cfg = bytearray(self.STRIDE)
        self.reset()

    def decode(self):
        b = self.cfg
        self.CORE, self.LINE, self.TRIG = b[0] & 1, (b[0] >> 1) & 3, b[0] >> 3
        self.W0C, self.W1C, self.W0H, self.W1H = b[1] & 63, b[2] & 63, b[3], b[4]

    def reset(self):
        self.cfg[:] = bytes(self.STRIDE)
        self.decode()
        self.PC = self.EN = self.READY = self.RUNNING = self.ARMED = self.LATE = self.OVR = 0

    def event(self, ch):
        if self.TRIG >= len(m.TRIGGERS):
            return 0
        name = m.TRIGGERS[self.TRIG]
        if name == "NONE":
            return 0
        if name == "ALWAYS":
            return int(not self.READY and not self.RUNNING)
        if name == "HOST.INV":
            return int(ch.host.INV and not ch.host.INVP)
        if name.startswith("FLAG"):
            k = int(name[4:name.index(".")])
            return int(((ch.flags.F >> k) & 1) and not ((ch.flags.FP >> k) & 1))
        if name.startswith("PINA."):
            pin = ch.lines[self.LINE].PINA
            if pin >= m.N_IN_PINS:
                return 0
            r, f = (ch.rs >> pin) & 1, (ch.fl >> pin) & 1
            return {"RISE": r, "FALL": f, "EDGE": r | f}[name[5:]]
        g, ev = int(name[1]), name[3:]
        ln = ch.lines[g]
        return ln.beat if ev == "BEAT" else ln.tap[int(ev[3])]


# ----------------------------------------------------------------------------------------------------------------
class Core:
    def __init__(self, c):
        self.c = c
        self.prog = [0] * m.PROG_WORDS
        self.reset()

    def reset(self):
        self.XV = self.RV = 0
        self.IR = 0
        self.FPC = 0
        self.XT = self.XL = self.RR = 0
        self.dout = 0                # word at the program memory output
        self.exec_log = []           # (cycle, thread, pc) of executed instructions (for tests)

    def plan(self, ch, base_guards, line_gv):
        """Phase 1. Decide moves, sequencing and dispatch from cycle-t state."""
        self.moves = []              # (move index, dst index, value, thread, line)
        self.effects = []
        self.pause = None            # (thread, npc)
        self.dispatch = None         # (thread, address)
        self.fetch = None
        jmp = pse = False
        if self.XV:
            pause, jmode, imm, cond, jcond, moves = decode_word(self.IR)
            g = line_gv(self.XL)
            C = g[cond] if cond < len(m.GUARD_CONDS) else 0
            JC = g[JMAP[jcond]]
            for i, (gd, s, d) in enumerate(moves):
                en = gd == 0 or (gd == 1 and C) or (gd == 2 and not C)
                if not en:
                    continue
                val = SRC_FN[s](ch, self.XL, imm) if s < len(m.SRC) else 0
                if s < len(m.SRC) and SRC_EFFECT[s]:
                    self.effects.append(SRC_EFFECT[s])
                self.moves.append((i, d if d < len(m.DST) else 0, val & 0xFF, self.XT, self.XL))
            taken = jmode == 1 or (jmode == 2 and JC) or (jmode == 3 and not JC)
            npc = imm if taken else self.FPC
            jmp = not pause and taken
            pse = bool(pause)
            ch.exec_trace(self.c, self.XT, (self.FPC - 1) & 0xFF)
            if pse:
                self.pause = (self.XT, npc)
            if jmp:
                self.fetch = imm
        self.load = self.RV and not jmp and not pse
        if self.load:
            self.fetch = (self.FPC + 1) & 0xFF
        free = pse or (not self.XV and not self.RV)
        if free and ch.ctrl.RUN:
            n = m.N_THREADS
            for j in range(n):
                e = (self.RR + j) % n
                th = ch.threads[e]
                if th.CORE == self.c and th.READY:
                    g = line_gv(th.LINE)
                    w0 = th.W0C != 0 and th.W0C < len(m.GUARD_CONDS) and g[th.W0C]
                    w1 = th.W1C != 0 and th.W1C < len(m.GUARD_CONDS) and g[th.W1C]
                    d = th.W0H if w0 else (th.W1H if w1 else th.PC)
                    self.dispatch = (e, d)
                    self.fetch = d
                    break

    def commit(self, ch, host_prog_write):
        if self.dispatch is not None:
            e, _ = self.dispatch
            self.XT, self.XL, self.RR = e, ch.threads[e].LINE, (e + 1) % m.N_THREADS
        nir = self.dout
        if host_prog_write is not None:      # SPEC v2 9a.8: the fetch in this cycle is undefined
            w, k, b = host_prog_write
            self.prog[w] = (self.prog[w] & ~(0xFF << 8 * k)) | (b << 8 * k)
        if self.fetch is not None:
            self.FPC = self.fetch
            self.dout = self.prog[self.fetch]
        self.RV = int(self.fetch is not None)
        self.XV = int(bool(self.load))
        if self.load:
            self.IR = nir
