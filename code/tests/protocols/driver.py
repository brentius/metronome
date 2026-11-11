"""Pin-level host driver: assembles a .mas program, loads it over SPI pins into the reference model and lets a test
interleave SPI transactions with protocol-pin stimulus. Reuses the lockstep Scenario SPI encoder (SPEC 9)."""
from __future__ import annotations

from pathlib import Path

import machine as m
from metronome import Chip
from metronome_tools.asm import assemble_file
from metronome_tools.image import host_writes
from scenarios import Scenario, miso_bytes, ctrl_reg

EX = Path(__file__).resolve().parents[2] / "host/examples"
CLK = 60e6


class PinScenario(Scenario):
    """Scenario whose SPI transactions keep the protocol-input pins in `hi` (ui[7:3]) and `uio` (P0..P7)."""
    hi = 0x08            # P8 = ui_in[3] idle high (UART idle)
    uio = 0

    def _spi(self, tx, ui_hi=None, uio=None):
        return super()._spi(tx, self.hi if ui_hi is None else ui_hi, self.uio if uio is None else uio)


class Driver:
    def __init__(self, hi=0x08, uio=0):
        self.chip = Chip()
        self.s = PinScenario()
        self.s.hi, self.s.uio = hi, uio
        self.done = 0
        self.trace = []          # (t, ui, uio, None, (uo, uio_out, oe))
        self.s.reset()
        self.flush()

    def flush(self):
        for t in range(self.done, len(self.s.cycles)):
            ui, uio, rst = self.s.cycles[t]
            self.trace.append((t, ui, uio, None, tuple(self.chip.step(ui, uio, rst))))
        self.done = len(self.s.cycles)

    def load(self, name: str):
        prog = assemble_file(EX / name)
        for addr, data, _note in host_writes(prog):
            self.write(addr, data)
        return prog

    def write(self, addr, data):
        self.s.write(addr, bytes(data))
        self.flush()

    def read(self, addr, n=1):
        first = len(self.s.reads)
        self.s.read(addr, n)
        self.flush()
        got = miso_bytes(self.trace, self.s, use_model=True)
        return [got[addr + k] for k in range(n)] if n else []

    def hoststat(self):
        return self.read(ctrl_reg("HOSTSTAT"))[0]

    def idle(self, n, p8=None, uio=None):
        """n cycles with CS_N high. p8 is an optional list of per-cycle P8 levels."""
        if p8 is None:
            self.s.idle(n, self.s.hi, self.s.uio if uio is None else uio)
        else:
            for lv in p8:
                self.s.idle(1, (self.s.hi & ~0x08) | (lv << 3), self.s.uio)
        self.flush()

    def out_bit(self, o):
        """Per-cycle level of output Ok (O0..O7 via uio_out, O8..O13 via uo_out[2..7]) over the whole trace."""
        if o >= 8:
            return [tr[4][0] >> (o - 6) & 1 for tr in self.trace]
        return [tr[4][1] >> o & 1 for tr in self.trace]
