"""Engines (SPEC 4) and output cells (SPEC 8)."""
import re
import machine as m

# TRIG code -> (kind, arg): decoded once from machine.TRIGGERS
TRIG_DECODE = []
for _name in m.TRIGGERS:
    if _name == "NONE":
        TRIG_DECODE.append(("none", 0))
    elif (mt := re.fullmatch(r"BG(\d)\.(BEAT|TAP(\d))", _name)):
        g = int(mt.group(1))
        TRIG_DECODE.append(("beat", g) if mt.group(2) == "BEAT" else ("tap", (g, int(mt.group(3)))))
    elif (mt := re.fullmatch(r"FLAG(\d+)\.RISE", _name)):
        TRIG_DECODE.append(("flag", int(mt.group(1))))
    elif _name == "PINA.RISE":
        TRIG_DECODE.append(("pinrise", 0))
    elif _name == "PINA.FALL":
        TRIG_DECODE.append(("pinfall", 0))
    elif _name == "PINA.EDGE":
        TRIG_DECODE.append(("pinedge", 0))
    elif _name == "HOST.INV":
        TRIG_DECODE.append(("inv", 0))
    elif _name == "ALWAYS":
        TRIG_DECODE.append(("always", 0))
    else:
        raise AssertionError(_name)


class Engine:
    def __init__(self, e):
        self.e = e
        self.reset()

    def reset(self):
        self.EN = self.CORE = self.BG = self.TRIG = 0
        self.PINA = self.PINB = 0
        self.LUT0 = self.LUT1 = 0
        self.W0C = self.W0H = self.W1C = self.W1H = 0
        self.PC = 0
        self.READY = self.RUNNING = self.ARMED = 0
        self.STAGED = self.COMMITTED = 0
        self.CAP = 0
        self.LATE = self.OVR = 0
        # per-cycle scratch
        self.trig = 0
        self.dispatched = False
        self.paused_npc = None

    @property
    def IN(self):
        return (((self.LUT1 >> self.CAP) & 1) << 1) | ((self.LUT0 >> self.CAP) & 1)

    def event(self, ch, rs, fl, lv, doorbell):
        """Does a trigger fire this cycle?"""
        if not self.EN:
            return 0
        if doorbell:
            return 1
        kind, a = TRIG_DECODE[self.TRIG] if self.TRIG < len(TRIG_DECODE) else ("none", 0)   # SPEC-AMBIGUITY: unused codes = NONE
        if kind == "none":
            return 0
        if kind == "beat":
            return ch.bg[a].beat
        if kind == "tap":
            return ch.bg[a[0]].taps[a[1]]
        if kind == "flag":
            return (ch.flags.F >> a) & 1 and not (ch.flags.FP >> a) & 1
        if kind == "pinrise":
            return (rs >> self.PINA) & 1
        if kind == "pinfall":
            return (fl >> self.PINA) & 1
        if kind == "pinedge":
            return ((rs | fl) >> self.PINA) & 1
        if kind == "inv":
            return int(ch.host.INV and not ch.host.INVP)
        return int(not self.READY and not self.RUNNING)       # always

    def fire_now(self):
        """Instant trigger used by backdoor writes (not cycle-accurate)."""
        if self.READY or self.RUNNING:
            self.OVR = 1
        else:
            self.READY = self.ARMED = 1

    def commit(self, ch, lv, sym):
        """sym: bus value of the winning E.SYM move this cycle (or None)."""
        bg = ch.bg[self.BG]
        trig = self.trig
        accepted = trig and not (self.READY or self.RUNNING)
        if trig and not accepted:
            self.OVR = 1
        ready, running, armed = self.READY, self.RUNNING, self.ARMED
        if accepted:
            ready = armed = 1
        if bg.beat:
            self.COMMITTED = (sym & 3) if sym is not None else self.STAGED
            armed = 1 if accepted else 0
        if sym is not None:
            if not self.ARMED:
                self.LATE = 1
            self.STAGED = sym & 3
        if self.dispatched:
            ready, running = 0, 1
        if self.paused_npc is not None:
            running = 0
            self.PC = self.paused_npc
        self.READY, self.RUNNING, self.ARMED = ready, running, armed
        pa = (lv >> self.PINA) & 1 if self.PINA < 13 else 0
        pb = (lv >> self.PINB) & 1 if self.PINB < 13 else 0
        cap = self.CAP
        t0, t1, t2 = bg.taps
        if t0:
            cap = (cap & ~1) | pa
        if t1:
            cap = (cap & ~0b1010) | (pa << 1) | (pb << 3)
        if t2:
            cap = (cap & ~0b100) | (pa << 2)
        self.CAP = cap


class OutCell:
    def __init__(self, o):
        self.o = o
        self.reset()

    def reset(self):
        self.ENG = 0
        self.LUT = 0
        self.OE = 0
        self.OUT = 0
        self.OEN = 0

    def compute(self, ch):
        if self.ENG < m.N_ENGINES:
            eng = ch.eng[self.ENG]
            idx = (ch.bg[eng.BG].seg << 2) | eng.COMMITTED
        else:
            idx = 0
        return (self.LUT >> idx) & 1, (self.OE >> idx) & 1
