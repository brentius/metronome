"""Host register map (SPEC 9): byte-wide read / write of every host-visible register.

`read(ch, addr)` returns the byte for a register-mapped address from current state (no side effects; side effects of
reads are applied by `read_effect`). `write(ch, addr, byte)` mutates state directly; the chip calls it at the end of a
cycle, after every other update, which gives host writes their priority over moves.
"""
import machine as m

BG0, ENG0, OUT0, UNIT0, CTRL0 = (m.HOST_MAP[k] for k in ("BG_BASE", "ENG_BASE", "OUT_BASE", "UNIT_BASE", "CTRL_BASE"))
PROG0, DATA0 = m.HOST_MAP["PROG_BASE"], m.HOST_MAP["DATA_BASE"]


def _lanes(table):
    """offset -> (name, lane) for every byte of every register in a machine.py table."""
    out = {}
    for off, (name, n) in table.items():
        for lane in range(n):
            out[off + lane] = (name, lane)
    return out


BG_LANES, ENG_LANES, OUT_LANES, CTRL_LANES = (_lanes(t) for t in (m.BG_REGS, m.ENG_REGS, m.OUT_REGS, m.CTRL_REGS))
UNIT_LANES = {}
for _off, (_name, _n) in m.UNIT_REGS.items():
    for _l in range(_n):
        UNIT_LANES[_off + _l] = (_name, _l)

BG_WIDE = {"INC": 0xFFFF, "MOD": 0xFFFF, "T0": 0xFFFF, "T1": 0xFFFF, "T2": 0xFFFF, "PRE": 0xFFFF,
           "WLO": 0xFFFF, "WHI": 0xFFFF, "PHASE": 0xFFFF}
ENG_WIDE = {"PC": 0xFF, "TRIG": 0x1F, "LUT0": 0xFFFF, "LUT1": 0xFFFF, "W0C": 0x3F, "W0H": 0xFF, "W1C": 0x3F, "W1H": 0xFF}


def _merge(old, lane, b, mask):
    s = 8 * lane
    return ((old & ~(0xFF << s)) | (b << s)) & mask


def decode(a):
    """Classify an address -> (kind, unit index, offset) or None if unmapped. kinds: prog, data, bg, eng, out, unit, ctrl."""
    if a < DATA0:
        return ("prog", (a >> 11) & 1, a & 0x7FF) if a < 0x1000 else None
    if a < DATA0 + m.DATA_BYTES:
        return ("data", 0, a - DATA0)
    if BG0 <= a < BG0 + 0x20 * m.N_BEATGENS:
        return ("bg", (a - BG0) >> 5, (a - BG0) & 0x1F)
    if ENG0 <= a < ENG0 + 0x20 * m.N_ENGINES:
        return ("eng", (a - ENG0) >> 5, (a - ENG0) & 0x1F)
    if OUT0 <= a < OUT0 + 8 * m.N_OUT_PINS:
        return ("out", (a - OUT0) >> 3, (a - OUT0) & 7)
    if UNIT0 <= a < UNIT0 + 8 * m.N_LFSRS:
        return ("unit", (a - UNIT0) >> 3, (a - UNIT0) & 7)
    if CTRL0 <= a < CTRL0 + 0x20:
        return ("ctrl", 0, a - CTRL0)
    return None


_READ_KIND = {"bg": ("BG", None), "eng": ("ENG", None), "out": ("OUT", None), "unit": ("UNIT", None)}


def _readable(kind, name):
    """D14: configuration registers outside machine.HOST_READABLE are write-only and read 0."""
    blk = _READ_KIND.get(kind)
    return blk is None or name in m.HOST_READABLE[blk[0]]


def read(ch, a):
    d = decode(a)
    if d is None or d[0] in ("prog", "data"):
        return 0
    kind, u, off = d
    lanes = {"bg": BG_LANES, "eng": ENG_LANES, "out": OUT_LANES, "unit": UNIT_LANES}.get(kind)
    if lanes is not None and off in lanes and not _readable(kind, lanes[off][0]):
        return 0
    if kind == "bg":
        g = ch.bg[u]
        if off not in BG_LANES:
            return 0
        name, lane = BG_LANES[off]
        if name in BG_WIDE:
            return ((g.PH if name == "PHASE" else getattr(g, name)) >> (8 * lane)) & 0xFF
        if name == "CTL":
            return g.RUN | (g.ARM << 1) | (g.REN << 2) | (g.WEN << 3)
        return g.EDGE_PIN | (g.EDGE_POL << 4)
    if kind == "eng":
        e = ch.eng[u]
        if off not in ENG_LANES:
            return 0
        name, lane = ENG_LANES[off]
        if name in ENG_WIDE:
            return (getattr(e, name) >> (8 * lane)) & 0xFF
        if name == "CFG":
            return e.EN | (e.CORE << 1) | (e.BG << 2)
        if name == "PINS":
            return e.PINA | (e.PINB << 4)
        if name == "SYM":
            return e.STAGED | (e.COMMITTED << 2)
        return e.READY | (e.RUNNING << 1) | (e.ARMED << 2) | (e.LATE << 4) | (e.OVR << 5)     # STAT
    if kind == "out":
        c = ch.out[u]
        if off not in OUT_LANES:
            return 0
        name, lane = OUT_LANES[off]
        if name == "ENG":
            return c.ENG
        return ((c.LUT if name == "LUT" else c.OE) >> (8 * lane)) & 0xFF
    if kind == "unit":
        if off not in UNIT_LANES:
            return 0
        return (ch.lf[u].POLY >> (8 * UNIT_LANES[off][1])) & 0xFF
    # ctrl
    if off not in CTRL_LANES:
        return 0
    name = CTRL_LANES[off][0]
    c, h = ch.ctrl, ch.host
    if name == "RUN":
        return c.RUN
    if name == "STICKY":
        return c.CONFLICT | (c.MEMHAZ << 1)
    if name == "IRQEN":
        return c.IRQEN
    if name == "DOORBELL":
        return 0
    if name == "HOSTIN":
        return h.INB
    if name == "HOSTOUT":
        return h.OUTB
    if name == "HOSTSTAT":
        return h.INV | (h.OUTV << 1)
    return 0xA0 | m.VERSION     # ID


def read_effect(ch, a):
    """Host reads have no side effects (SPEC 9; OUTV is acknowledged by writing HOSTSTAT bit 1)."""
    return False


def doorbell_addr(a):
    d = decode(a)
    return bool(d and d[0] == "ctrl" and d[2] in CTRL_LANES and CTRL_LANES[d[2]][0] == "DOORBELL")


def write(ch, a, b, instant=False):
    """Host write of one byte. DOORBELL is a trigger evaluated in phase 1 by the chip unless `instant`."""
    d = decode(a)
    if d is None:
        return
    kind, u, off = d
    if kind == "prog":
        word, byte = (off >> 3) & 0xFF, off & 7      # SPEC 9: each byte goes straight into its lane (byte mask)
        w = ch.cores[u].mem[word]
        ch.cores[u].mem[word] = (w & ~(0xFF << (8 * byte))) | (b << (8 * byte))
        return
    if kind == "data":
        ch.mem_host_write(off, b)
        return
    if kind == "bg":
        g = ch.bg[u]
        if off not in BG_LANES:
            return
        name, lane = BG_LANES[off]
        if name in BG_WIDE:
            attr = "PH" if name == "PHASE" else name
            setattr(g, attr, _merge(getattr(g, attr), lane, b, 0xFFFF))
        elif name == "CTL":
            g.RUN, g.ARM, g.REN, g.WEN = b & 1, (b >> 1) & 1, (b >> 2) & 1, (b >> 3) & 1
        else:
            g.EDGE_PIN, g.EDGE_POL = b & 0xF, (b >> 4) & 3
        return
    if kind == "eng":
        e = ch.eng[u]
        if off not in ENG_LANES:
            return
        name, lane = ENG_LANES[off]
        if name in ENG_WIDE:
            setattr(e, name, _merge(getattr(e, name), lane, b, ENG_WIDE[name]))
        elif name == "CFG":
            e.EN, e.CORE, e.BG = b & 1, (b >> 1) & 1, (b >> 2) & 3
        elif name == "PINS":
            e.PINA, e.PINB = b & 0xF, b >> 4
        elif name == "STAT":
            if b & 0x10:
                e.LATE = 0
            if b & 0x20:
                e.OVR = 0
        return
    if kind == "out":
        c = ch.out[u]
        if off not in OUT_LANES:
            return
        name, lane = OUT_LANES[off]
        if name == "ENG":
            c.ENG = b & 7
        elif name == "LUT":
            c.LUT = _merge(c.LUT, lane, b, 0xFFFF)
        elif u < m.N_OE_PINS:
            c.OE = _merge(c.OE, lane, b, 0xFFFF)
        return
    if kind == "unit":
        if off in UNIT_LANES:
            lf = ch.lf[u]
            lf.POLY = _merge(lf.POLY, UNIT_LANES[off][1], b, 0xFFFFFFFF)
        return
    if off not in CTRL_LANES:
        return
    name = CTRL_LANES[off][0]
    c, h = ch.ctrl, ch.host
    if name == "RUN":
        c.RUN = b & 1
    elif name == "STICKY":
        if b & 1:
            c.CONFLICT = 0
        if b & 2:
            c.MEMHAZ = 0
    elif name == "IRQEN":
        c.IRQEN = b & 3
    elif name == "DOORBELL":
        if instant:
            for e in range(m.N_ENGINES):
                if (b >> e) & 1 and ch.eng[e].EN:
                    ch.eng[e].fire_now()
    elif name == "HOSTIN":
        h.INB = b
        h.INV = 1
    elif name == "HOSTSTAT":
        if b & 2 and (instant or not getattr(ch, "_hostout_moved", False)):
            h.OUTV = 0
