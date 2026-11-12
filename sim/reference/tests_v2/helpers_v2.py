"""Test helpers for the v2 model: configuration through the instant backdoor, stepping, observation."""
from metronome2 import Chip, asm, m  # noqa: F401

IDLE = 0x02   # ui_in: CS_N high


def le(v, n):
    return int(v).to_bytes(n, "little")


def blk(chip, block, i=0, **kw):
    base, st, n, regs = m.HOST_BLOCKS[block]
    a0 = m.HOST_MAP[base] + (m.HOST_STRIDE[st] * i if st else 0)
    for off, (name, nb, acc, _) in regs.items():
        if name in kw:
            chip.backdoor_write(a0 + off, le(kw[name], nb))


def edge(pin, pol, wen=0, follow=0):
    return pin | (pol << 4) | (wen << 6) | (follow << 7)


def tcfg(core=0, line=0, trig="NONE"):
    return core | (line << 1) | (m.TRIG_ID[trig] << 3)


def thread(chip, t, core=0, line=0, trig="NONE", pc=0, en=1, **kw):
    blk(chip, "THREAD", t, CFG=tcfg(core, line, trig), **kw)
    blk(chip, "TRT", t, PC=pc, STAT=en << 3)


def run_line(chip, l, ctl=1):
    blk(chip, "LRT", l, CTL=ctl)


def steps(chip, n, ui=IDLE, uio=0):
    return [chip.step(ui, uio) for _ in range(n)]


def lut(fn, bits=5):
    """Truth table as an int: bit idx = fn(idx)."""
    return sum((fn(i) & 1) << i for i in range(1 << bits))
