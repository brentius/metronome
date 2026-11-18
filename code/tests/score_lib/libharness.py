"""Helpers for the library-score tests: load a library score, run a compiled sender role on the v2 cycle-level model
and read pins back.  Everything that decides pass or fail lives in indep.py (written from the standards), not here."""
from pathlib import Path

from harness import HM, IDLE, ROOT, hostin, new_chip, stream_reg, stream_rewind  # noqa: F401  (code/tests/scorec/harness.py)

LIB = ROOT / "code/score/lib"
CLK = 60_000_000


def lib_text(name):
    return (LIB / f"{name}.score").read_text(encoding="utf-8")


def pin_level(o, uo, uio, oe=None):
    """Level of output pin O<o> from one model step (O0..O7 are uio, O8.. are uo bits 2..)."""
    return (uio >> o) & 1 if o < 8 else (uo >> (o - 8 + 2)) & 1


def run_sender(compiled, data, pins, cycles, idle_in=0, ram=None):
    """Feed `data` (bytes) one per free mailbox slot, run `cycles` chip cycles, return {pin: [level per cycle]}.
    `ram` (bytes) is placed in data RAM as transmit stream 0 for `bytes[N]` fields."""
    chip = new_chip(compiled)
    if ram is not None:
        chip.backdoor_write(HM["DATA_BASE"], bytes(ram))
        stream_reg(chip, 0, "LEN", len(ram), 2)
        stream_rewind(chip, 0)
        for _ in range(40):
            chip.step(IDLE, idle_in)
    pending, tr = list(data), {p: [] for p in pins}
    for _ in range(cycles):
        if pending and chip.host.INV == 0:
            hostin(chip, pending.pop(0))
        uo, uio, oe = chip.step(IDLE, idle_in)
        for p in pins:
            tr[p].append(pin_level(p, uo, uio))
    return chip, tr


def model_clean(chip):
    assert all(t.LATE == 0 and t.OVR == 0 for t in chip.threads), [(t.LATE, t.OVR) for t in chip.threads]
    assert chip.ctrl.CONFLICT == 0
