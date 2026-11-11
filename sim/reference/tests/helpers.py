"""Test helpers: configuration through the instant backdoor, program loading, stepping."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "code" / "md"))
import machine as m           # noqa: E402
import encode as enc          # noqa: E402
from metronome import Chip    # noqa: E402

IDLE = 0x02   # ui_in with CS_N high, everything else low


def le(v, n):
    return int(v).to_bytes(n, "little")


def bg_cfg(chip, g, **kw):
    base = m.HOST_MAP["BG_BASE"] + 0x20 * g
    for off, (name, n) in m.BG_REGS.items():
        if name in kw:
            chip.backdoor_write(base + off, le(kw[name], n))


def eng_cfg(chip, e, **kw):
    base = m.HOST_MAP["ENG_BASE"] + 0x20 * e
    for off, (name, n) in m.ENG_REGS.items():
        if name in kw:
            chip.backdoor_write(base + off, le(kw[name], n))


def out_cfg(chip, o, **kw):
    base = m.HOST_MAP["OUT_BASE"] + 8 * o
    for off, (name, n) in m.OUT_REGS.items():
        if name in kw:
            chip.backdoor_write(base + off, le(kw[name], n))


def ctrl(chip, name, v):
    for off, (n, nb) in m.CTRL_REGS.items():
        if n == name:
            chip.backdoor_write(m.HOST_MAP["CTRL_BASE"] + off, le(v, nb))


def eng_cfgbyte(en=1, core=0, bg=0):
    return en | (core << 1) | (bg << 2)


def load(chip, insns, core=0, at=0):
    for i, ins in enumerate(insns):
        w = ins if isinstance(ins, int) else enc.encode(ins)
        chip.backdoor_write(m.HOST_MAP["PROG_BASE"] + core * 0x800 + (at + i) * 8, le(w, 8))


def I(*moves, **kw):
    """Instruction builder: moves are (src, dst[, guard]) tuples."""
    return enc.Insn(tuple(enc.Move(*mv) for mv in moves), **kw)


def step(chip, n=1, ui=IDLE, uio=0):
    r = None
    for _ in range(n):
        r = chip.step(ui, uio)
    return r


def oneshot(chip, insns, e=0, core=0, pc=0, maxc=200):
    """Load a burst, enable engine e on `core`, RUN=1, fire the doorbell instantly; step until the engine is idle.
    Returns the number of steps taken. Cycle 0 = dispatch, cycle 1 = first instruction."""
    load(chip, insns, core)
    eng_cfg(chip, e, PC=pc, CFG=eng_cfgbyte(1, core, 0))
    ctrl(chip, "RUN", 1)
    chip.backdoor_write(m.HOST_MAP["CTRL_BASE"] + 3, bytes([1 << e]))
    n = 0
    while n < maxc:
        step(chip)
        n += 1
        en = chip.eng[e]
        if not en.READY and not en.RUNNING:
            return n
    raise AssertionError("burst did not finish")
