"""Scenarios owned by the xinit bench.

They reuse the v2 scenario builder and instruction encoder (imported, never edited) but isolate the power-up
question from host-readback effects:

  load_run     host writes all program words and the data a running program reads; the result appears on pins, so a
               fully loaded program must behave identically whatever the prior SRAM contents were.
  load_read    host writes a whole-word-aligned region (including the one-word lookahead of the read command) and
               reads five bytes inside it; MISO must be identical whatever the prior SRAM contents were.
  read_probe   writes five bytes, reads five: the read command issues one extra lookahead read into the next
               (unwritten) word.  Used to characterise the undefined idle MISO after such a read.
  reset_only   reset and idle: the state and output after reset, with no host traffic at all.
  ping         a few register reads after reset (no data RAM), to prove the host link still works after a pulse.
"""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path[:0] = [str(ROOT / "sim/reference"), str(ROOT / "code/tests/lockstep_v2")]

import scenarios  # noqa: E402
from scenarios import HM, I, Scn, edge, lut  # noqa: E402
from metronome2 import m  # noqa: E402


def load_run(short=False):
    """eth_loopback's loaded TX stream, without the host readback at the end (same stimulus, pins are the output).

    `short=True` loads only the single instruction each thread executes.  The core then fetches the word after it
    (fetch-ahead / the paused thread's PC+1), which is unloaded; that is the documented host-contract case.  The
    default pads each program with a self-jump so every word the core can fetch is loaded.
    """
    s = Scn("xinit_load_run" if not short else "xinit_load_run_short")
    s.reset()
    data = [0x55, 0xD5, 0x12, 0xF0, 0x0F, 0xC3]
    # The stream length ends inside word 1.  The RTL reads one byte past LEN at the END decision, so the rest of the
    # word is part of the host contract: write the whole word, not just LEN bytes.  `short=True` leaves the tail
    # undefined, which is the case this scenario is meant to expose.
    s.data(0, data + ([0x00, 0x00] if not short else []))
    s.blk("STREAM", 0, MODE=0, START=0, LEN=len(data))
    s.blk("SRT", 0, CTL=1)
    s.blk("LINE", 0, INC=1, MOD=6, T0=0, T1=3, T2=0xFFFF)
    s.blk("OUT", 0, BIND=0b100, SEL=0, LUT=lut(lambda i: i & 1), OE=0xFFFFFFFF)
    p0 = [I(("S0.BIT", "L.DBIT"), ("ZERO", "S0.ADV"), pause=1, jmode="always", imm=0)]
    s.program(0, p0 if short else p0 + [I(pause=1, jmode="always", imm=1)])
    s.thread(0, core=0, line=0, trig="L0.BEAT")
    nrx = len(data) + 1
    s.blk("STREAM", 1, MODE=1, START=0x400, LEN=nrx)
    s.blk("SRT", 1, CTL=1)
    s.blk("LINE", 1, INC=1, MOD=6, T0=5, T1=0xFFFF, T2=0xFFFF, PINS=0, SNAP=0, LUT0=lut(lambda i: i & 1))
    p1 = [I(("L.IN", "S1.RX"), pause=1, jmode="always", imm=0)]
    s.program(1, p1 if short else p1 + [I(pause=1, jmode="always", imm=1)])
    s.thread(1, core=1, line=1, trig="L1.TAP0")
    s.blk("CTRL", RUN=1)
    s.uio = lambda t, o: o[1] & 1
    s.blk("LRT", 0, CTL=1)
    s.blk("LRT", 1, CTL=1)
    s.idle(6 * 8 * nrx + 60)
    return s


def load_read():
    """Whole words written, then a five-byte read inside them (the lookahead word is written too)."""
    s = Scn("xinit_load_read")
    s.reset()
    s.data(0x100, list(range(0x30, 0x38)))       # bytes 0x100..0x107 = words 0x40, 0x41
    s.read(HM["DATA_BASE"] + 0x100, 5)
    s.idle(12)
    return s


def read_probe():
    """Five bytes written, five read: the extra lookahead read touches word 74, which is not written."""
    s = Scn("xinit_read_probe")
    s.reset()
    s.data(0x123, [0x11, 0x22, 0x33, 0x44, 0x55])
    s.read(HM["DATA_BASE"] + 0x123, 5)
    s.idle(24)
    return s


def reset_only():
    s = Scn("xinit_reset_only")
    s.reset(low=5, after=64)
    return s


def ping():
    """After a reset: ID and the runtime control block, no data RAM reads."""
    s = Scn("xinit_ping")
    s.read(HM["CTRL_BASE"] + 7, 1)
    s.read(HM["CTRL_BASE"], 9)
    s.readback_all()
    s.idle(8)
    return s


def mid_reset(pulse=None):
    s = load_run()
    s.name = "xinit_mid_reset"
    s.mid = len(s.steps)
    s.pulse = pulse
    if pulse is None:
        s.reset(low=5, after=6)
    else:
        # Phase is measured from the falling edge, next rising edge at 8 ns.
        if pulse[1] > 8000:
            s.idle(1)
        s.reset(low=1 if pulse[0] <= 8000 else 2, after=6)
    # Prove the host interface and runtime registers recover. No SRAM is
    # compared after depositing arbitrary mid-cycle control state.
    s.read(HM["CTRL_BASE"], 9)
    return s


DIRECTED = {"xinit_load_run": load_run,
            "xinit_load_run_short": lambda: load_run(short=True),
            "xinit_load_read": load_read, "xinit_read_probe": read_probe,
            "xinit_reset_only": reset_only, "xinit_mid_reset": mid_reset}


def build(name):
    if name.startswith("xinit_pulse_"):
        width, phase = map(int, name.removeprefix("xinit_pulse_").split("_"))
        return mid_reset((width, phase))
    return DIRECTED[name]()
