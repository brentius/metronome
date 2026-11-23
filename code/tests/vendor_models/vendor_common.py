"""Shared cocotb helpers for the vendor-model co-simulations.

The benches drive the chip's SPI host link only (SPEC_V2 9); every device-facing pin is wired to the
third-party device model in the Verilog top, so the DUT is the real RTL plus the real model.

One clock cycle per `_cycle` call: `ui_in` is set on the falling edge (as the lockstep bench does) and
outputs are sampled only when `sample=True`, because a full-chip Icarus run costs about a millisecond
per simulated cycle of cocotb round trips.
"""
from __future__ import annotations

import sys
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge, Timer

ROOT = Path(__file__).resolve().parents[3]
for _p in ("sim/reference", "code/host2", "code/scorec", "code/score"):
    if str(ROOT / _p) not in sys.path:
        sys.path.insert(0, str(ROOT / _p))

from metronome2 import m, spi                      # noqa: E402
from metronome2_tools.image import host_writes     # noqa: E402

HM = m.HOST_MAP
IDLE = spi.IDLE
CLK_NS = 16.666          # 60 MHz (cocotb needs an even number of time units)

__all__ = ["ROOT", "HM", "IDLE", "Bench", "stream_addr", "srt_addr", "m", "spi"]


def stream_addr(k, reg):
    from metronome2_tools.image import stream_addr as f
    return f(k, reg)


def srt_addr(k, reg):
    from metronome2_tools.image import srt_addr as f
    return f(k, reg)


def _val(sig):
    # Fail on X/Z instead of decoding it as 0: an unresolved pin during a sampled host read is a
    # defect to report, not data (review S5, 2026-11-19).
    v = sig.value
    if not v.is_resolvable:
        raise AssertionError(f"unresolved value {v} on {sig._name} during a sampled read")
    return int(v)


class Bench:
    def __init__(self, dut):
        self.dut = dut
        self.outs = []          # sampled (uo, uio_out, uio_oe), in sampling order
        self.cycle = 0

    async def start(self, reset_cycles=3, settle=8):
        cocotb.start_soon(Clock(self.dut.clk, CLK_NS, unit="ns").start())
        await self._cycle(IDLE, ena=1, rst_n=0)
        for _ in range(reset_cycles - 1):
            await self._cycle(IDLE)
        await self._cycle(IDLE, rst_n=1)
        for _ in range(settle):
            await self._cycle(IDLE)

    async def _cycle(self, ui, sample=False, **extra):
        await FallingEdge(self.dut.clk)
        for name, value in extra.items():
            getattr(self.dut, name).value = value
        self.dut.ui_in.value = ui
        await RisingEdge(self.dut.clk)
        if sample:
            await ReadOnly()
            self.outs.append((_val(self.dut.uo_out), _val(self.dut.uio_out), _val(self.dut.uio_oe)))
        self.cycle += 1

    async def idle(self, n=1):
        for _ in range(n):
            await self._cycle(IDLE)

    async def wait(self, n=1):
        """Free-run the clock for n cycles with the pins held at idle.

        The chip and the device model keep working on their own; only the Python round trip per cycle is
        skipped, which is what makes bus waits (write cycles, low-rate frames) affordable.  The pins keep
        their last driven values, so callers use this only where no pin change is needed.
        """
        await Timer(n * 16666, unit="ps")           # 60 MHz period = 16.666 ns, exact in picoseconds
        await FallingEdge(self.dut.clk)
        self.cycle += n

    async def pulse(self, name, value=1, settle=2):
        """Drive a test-bench-only control (for example the PS/2 device model's `go` input)."""
        await self._cycle(IDLE, **{name: value})
        await self._cycle(IDLE, **{name: 0})
        await self.idle(settle)

    async def write(self, addr, data, half=2):
        for f in spi.write_frames(addr, bytes(data), half):
            await self._cycle(f)

    async def read(self, addr, n, half=8):
        frames = spi.read_frames(addr, n, half)
        outs = []
        for f in frames:
            await self._cycle(f, sample=True)
            outs.append(self.outs[-1])
        return spi.decode_read(frames, outs, n)

    async def read_u8(self, addr, half=8):
        return (await self.read(addr, 1, half))[0]

    async def load(self, program, idle=40):
        """Write a compiled image over the host link, then let the program settle."""
        for addr, data, _ in host_writes(program):
            await self.write(addr, bytes(data))
        await self.idle(idle)
