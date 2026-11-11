# SPDX-FileCopyrightText: © 2024 Tiny Tapeout
# SPDX-License-Identifier: Apache-2.0
"""Template-level smoke test for tt_um_brentius_metronome, run by the TT `test` (RTL) and `gl_test` (gate level)
GitHub Actions. It only uses the chip's pins, so it runs unchanged on the post-route netlist.

The example program code/host/examples/blink.mas is assembled with the project's own toolchain, loaded over the host
SPI port, and must then toggle O8 (uo_out[2]) once per beat. The beat rate is raised from 1 kHz to 1 MHz (60 clocks)
to keep the simulation short. The full verification (reference-model lockstep, protocol checkers, formal) lives in
code/tests; see wiki/VERIFICATION.md.
"""

import sys
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "code" / "host"))
from metronome_tools.asm import Assembler  # noqa: E402
from metronome_tools.image import build_image, image_to_spi  # noqa: E402

SCK, CS_N, MOSI = 0, 1, 2   # ui_in bits (host SPI target, mode 0)
HALF = 8                    # SCK half period in clk cycles (SCK = clk / 16)
BEAT = 60                   # clocks per beat at 1 MHz beats and a 60 MHz clock
O8 = 2                      # uo_out bit of output pin O8


def blink_frames():
    src = (ROOT / "code/host/examples/blink.mas").read_text(encoding="utf-8")
    src = src.replace("rate 1000 ", "rate 1000000 ")
    return image_to_spi(build_image(Assembler(src, "blink.mas").assemble()))


async def spi_frame(dut, frame):
    """Drive one chip-select frame of `frame` bytes, MSB first, changing MOSI while SCK is low."""
    ui = 1 << CS_N
    async def drive(sck, cs_n, mosi):
        nonlocal ui
        ui = (sck << SCK) | (cs_n << CS_N) | (mosi << MOSI)
        dut.ui_in.value = ui
        await ClockCycles(dut.clk, HALF)
    await FallingEdge(dut.clk)
    await drive(0, 0, 0)
    for b in frame:
        for i in range(7, -1, -1):
            bit = (b >> i) & 1
            await drive(0, 0, bit)
            await drive(1, 0, bit)
    await drive(0, 0, 0)
    await drive(0, 1, 0)


@cocotb.test()
async def test_project(dut):
    dut._log.info("Start")

    # About 60 MHz, the clock the demo board's RP2350 supplies (info.yaml clock_hz).
    # 16.666 ns because cocotb needs an even number of 1 ps steps.
    clock = Clock(dut.clk, 16.666, unit="ns")
    cocotb.start_soon(clock.start())

    dut._log.info("Reset")
    dut.ena.value = 1
    dut.ui_in.value = 1 << CS_N
    dut.uio_in.value = 0
    dut.rst_n.value = 0
    await ClockCycles(dut.clk, 10)
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 10)

    frames = blink_frames()
    dut._log.info(f"Loading blink.mas: {len(frames)} SPI frames, {sum(len(f) for f in frames)} bytes")
    for f in frames:
        await spi_frame(dut, f)

    # Record O8 at every falling edge for a few beats and check it toggles exactly once per beat.
    await ClockCycles(dut.clk, 2 * BEAT)
    levels = []
    for _ in range(8 * BEAT):
        await FallingEdge(dut.clk)
        levels.append((int(dut.uo_out.value) >> O8) & 1)
    edges = [i for i in range(1, len(levels)) if levels[i] != levels[i - 1]]
    dut._log.info(f"O8 edges at {edges}")
    assert len(edges) >= 6, f"O8 should toggle every {BEAT} clocks, saw {len(edges)} edges in {len(levels)} clocks"
    gaps = {b - a for a, b in zip(edges, edges[1:])}
    assert gaps == {BEAT}, f"O8 edges should be exactly {BEAT} clocks apart, saw gaps {sorted(gaps)}"
