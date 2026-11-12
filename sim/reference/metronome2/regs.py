"""Host address decode, register reads and writes (SPEC v2 9; map from machine.HOST_MAP / HOST_BLOCKS)."""
from .md import m

HM = m.HOST_MAP
_BLOCKS = []      # (lo, hi, block, stride, regs)
for _b, (_base, _st, _n, _regs) in m.HOST_BLOCKS.items():
    _stride = m.HOST_STRIDE[_st] if _st else 0x10
    _BLOCKS.append((HM[_base], HM[_base] + _stride * _n, _b, _stride, _regs))


def _reg_at(regs, off):
    for o, r in regs.items():
        if o <= off < o + r[1]:
            return o, r
    return None


def decode(addr):
    """('prog', core, word, byte) | ('data', None, offset) | (block, instance, offset, reg_off, reg) | None."""
    addr &= 0xFFFF
    pb, ps = HM["PROG_BASE"], m.HOST_STRIDE["PROG_CORE"]
    if pb <= addr < pb + ps * m.N_CORES:
        a = addr - pb
        return ("prog", a // ps, (a % ps) >> 3, a & 7)
    if HM["DATA_BASE"] <= addr < HM["DATA_BASE"] + m.DATA_BYTES:
        return ("data", None, addr - HM["DATA_BASE"])
    for lo, hi, b, stride, regs in _BLOCKS:
        if lo <= addr < hi:
            i, off = divmod(addr - lo, stride)
            r = _reg_at(regs, off)
            if r is None:
                return None
            if b == "OUT" and r[1][0] == "OE" and i >= m.N_OE_PINS:
                return None
            return (b, i, off, r[0], r[1])
    return None


CONFIG_BLOCKS = {"LINE", "THREAD", "LFSR", "STREAM", "OUT"}


def is_config(addr):
    d = decode(addr)
    return d is not None and d[0] in CONFIG_BLOCKS


def config_target(ch, block, i):
    return {"LINE": lambda: ch.lines[i], "THREAD": lambda: ch.threads[i], "LFSR": lambda: ch.lf_cfg[i],
            "STREAM": lambda: ch.mem.streams[i], "OUT": lambda: ch.out[i]}[block]()


def apply_config(ch, addr, v):
    """Latch the configuration byte (called when it becomes visible: W+2, or instantly via the backdoor)."""
    b, i, off, _, _ = decode(addr)
    tgt = config_target(ch, b, i)
    tgt.cfg[off] = v & 0xFF
    tgt.decode()


def _byte(v, off_in_reg):
    return (v >> (8 * off_in_reg)) & 0xFF


def errsum(ch):
    return (int(any(t.LATE for t in ch.threads)) | int(any(t.OVR for t in ch.threads)) << 1
            | int(any(ln.TAPMISS for ln in ch.lines)) << 2 | int(any(s.STARVED for s in ch.mem.streams)) << 3
            | ch.ctrl.CONFLICT << 4 | ch.ctrl.MEMHAZ << 5)


def read(ch, addr):
    """Value of a register in the current cycle (data RAM reads go through the arbiter; not handled here)."""
    d = decode(addr)
    if d is None or d[0] in ("prog", "data") or d[0] in CONFIG_BLOCKS:
        return 0
    b, i, off, roff, (name, nb, acc, _) = d
    k = off - roff
    if b == "CTRL":
        c, h = ch.ctrl, ch.host
        v = {"RUN": c.RUN, "STICKY": (c.MEMHAZ << 1) | c.CONFLICT, "IRQEN": c.IRQEN, "DOORBELL": 0,
             "HOSTIN": h.INB, "HOSTOUT": h.OUTB, "HOSTSTAT": (h.OUTV << 1) | h.INV, "ID": 0xA0 | m.VERSION,
             "ERRSUM": errsum(ch)}[name]
    elif b == "LRT":
        ln = ch.lines[i]
        v = {"PHASE": ln.PH, "CTL": ln.RUN | ln.ARM << 1 | ln.REN << 2 | ln.SP << 3 | ln.FIRED << 4,
             "SYM": ln.STAGED | ln.COMMITTED << 4, "INS": ln.CAP | ln.IN << 5, "STAT": ln.TAPMISS}[name]
    elif b == "TRT":
        t = ch.threads[i]
        v = {"PC": t.PC, "STAT": t.READY | t.RUNNING << 1 | t.ARMED << 2 | t.EN << 3 | t.LATE << 4
             | t.OVR << 5}[name]
    elif b == "SRT":
        s = ch.mem.streams[i]
        v = {"POSL": s.POS & 0xFF, "POSH": (s.POS >> 8) | s.BIDX << 4 | s.STARVED << 7, "CTL": 0}[name]
    else:
        v = 0
    return _byte(v, k)


def write_runtime(ch, addr, v):
    """Host write to a flop register at the end of cycle W (after every other update: host priority)."""
    d = decode(addr)
    if d is None:
        return
    b, i, off, roff, (name, nb, acc, _) = d
    k = off - roff
    ev = ch.events
    if b == "CTRL":
        c, h = ch.ctrl, ch.host
        if name == "RUN":
            c.RUN = v & 1
        elif name == "STICKY":
            if v & 1 and "CONFLICT" not in ev:
                c.CONFLICT = 0
            if v & 2 and "MEMHAZ" not in ev:
                c.MEMHAZ = 0
        elif name == "IRQEN":
            c.IRQEN = v & 3
        elif name == "DOORBELL":
            ch.db_next = v & ((1 << m.N_THREADS) - 1)
        elif name == "HOSTIN":
            h.INB, h.INV = v, 1
        elif name == "HOSTSTAT":
            if v & 2 and "HOSTOUT" not in ev:
                h.OUTV = 0
    elif b == "LRT":
        ln = ch.lines[i]
        if name == "PHASE":
            ln.PH = (ln.PH & ~(0xFF << 8 * k)) | (v << 8 * k)
            ln.fix_fired()
        elif name == "CTL":
            ln.RUN, ln.ARM, ln.REN = v & 1, (v >> 1) & 1, (v >> 2) & 1
            ln.fix_fired()
        elif name == "STAT":
            if v & 1 and ("TAPMISS", i) not in ev:
                ln.TAPMISS = 0
    elif b == "TRT":
        t = ch.threads[i]
        if name == "PC":
            t.PC = v
        elif name == "STAT":
            t.EN = (v >> 3) & 1
            if v & 0x10 and ("LATE", i) not in ev:
                t.LATE = 0
            if v & 0x20 and ("OVR", i) not in ev:
                t.OVR = 0
    # SRT CTL is applied inside the stream commit (Chip.step)
