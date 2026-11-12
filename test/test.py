# SPDX-FileCopyrightText: © 2024 Tiny Tapeout
# SPDX-License-Identifier: Apache-2.0
"""Template-level smoke test for tt_um_brentius_metronome (Metronome v2, wiki/SPEC_V2.md), run by the TT `test`
(RTL) and `gl_test` (gate level) GitHub Actions. It only uses the chip's pins, so it runs unchanged on the
post-route netlist.

Over the host SPI port it reads the ID register, then loads a one-instruction blink program: line 0 generates a
beat every 60 clocks (1 MHz at 60 MHz), thread 0 on core 0 runs on every boundary and toggles bit 0 of the line's
output symbol (L.XOR), and output pin O8 (uo_out[2]) shows that bit, so O8 toggles once per beat. Instruction and
register encodings come from code/md2/machine.py through the v2 reference model's encoder. The full verification
(reference-model lockstep, per-block tests) lives in code/tests/lockstep_v2 and code/tests/rtl_v2.
"""

import sys
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "sim" / "reference"))
from metronome2 import asm, m  # noqa: E402

SCK, CS_N, MOSI = 0, 1, 2   # ui_in bits (host SPI target, mode 0)
MISO = 0                    # uo_out bit
HALF = 8                    # SCK half period in clk cycles (SCK = clk / 16, SPEC_V2 9)
BEAT = 60                   # clocks per beat
O8 = 2                      # uo_out bit of output pin O8
HM = m.HOST_MAP


def addr(block, i, name):
    base, st, n, regs = m.HOST_BLOCKS[block]
    a0 = HM[base] + (m.HOST_STRIDE[st] * i if st else 0)
    return a0 + next(off for off, r in regs.items() if r[0] == name)


async def spi_frame(dut, frame, nread=0):
    """Drive one chip-select frame, MSB first, changing MOSI while SCK is low; returns the bytes read on MISO
    during the last `nread` bytes (sampled just before each SCK rising edge)."""
    bits = []

    async def drive(sck, cs_n, mosi):
        dut.ui_in.value = (sck << SCK) | (cs_n << CS_N) | (mosi << MOSI)
        await ClockCycles(dut.clk, HALF)

    await FallingEdge(dut.clk)
    await drive(0, 0, 0)
    for b in frame:
        for i in range(7, -1, -1):
            bit = (b >> i) & 1
            await drive(0, 0, bit)
            bits.append((int(dut.uo_out.value) >> MISO) & 1)
            await drive(1, 0, bit)
    await drive(0, 0, 0)
    await drive(0, 1, 0)
    data = bits[len(bits) - 8 * nread:] if nread else []
    return [int("".join(map(str, data[8 * j:8 * j + 8])), 2) for j in range(nread)]


async def write(dut, a, data):
    await spi_frame(dut, [0x02, a >> 8, a & 0xFF, *data])


async def read(dut, a, n):
    return await spi_frame(dut, [0x03, a >> 8, a & 0xFF] + [0] * n, nread=n)


def le(v, n):
    return list(int(v).to_bytes(n, "little"))


@cocotb.test()
async def test_project(dut):
    dut._log.info("Start")
    # About 60 MHz (info.yaml clock_hz); 16.666 ns because cocotb needs an even number of 1 ps steps.
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

    ident = await read(dut, addr("CTRL", 0, "ID"), 1)
    dut._log.info(f"ID = {ident}")
    assert ident == [0xA0 | m.VERSION], f"ID register: {ident}"

    word = asm.insn(("IMM", "L.XOR"), pause=1, jmode="always", imm=1)
    await write(dut, HM["PROG_BASE"], le(word, 8) * 2)                        # words 0 and 1 of core 0
    await write(dut, addr("LINE", 0, "INC"), le(1, 2) + le(BEAT, 2) + le(0xFFFF, 2) * 3)   # INC, MOD, T0..T2 off
    await write(dut, addr("OUT", 8, "BIND"), [0b100])                         # O8 bound to line 0
    await write(dut, addr("OUT", 8, "LUT"), le(sum(1 << i for i in range(32) if i & 1), 4))   # O8 = symbol bit 0
    await write(dut, addr("THREAD", 0, "CFG"), [m.TRIG_ID["L0.BEAT"] << 3])   # core 0, line 0, on boundaries
    await write(dut, addr("TRT", 0, "PC"), [0, 0x08])                         # PC 0, EN 1
    await write(dut, addr("CTRL", 0, "RUN"), [1])
    await write(dut, addr("LRT", 0, "CTL"), [1])                              # line 0 RUN

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
    errsum = await read(dut, addr("CTRL", 0, "ERRSUM"), 1)
    assert errsum == [0], f"ERRSUM {errsum}: no LATE, OVR, TAPMISS, STARVED, CONFLICT or MEMHAZ expected"
