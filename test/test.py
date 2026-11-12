# SPDX-FileCopyrightText: © 2024 Tiny Tapeout
# SPDX-License-Identifier: Apache-2.0
"""Smoke test for the v2 latch-bank sizing top (branch sizing/latch-bank-20261112), run by the TT `test` (RTL) and
`gl_test` (gate level) actions. Pins only, so it runs unchanged on the post-route netlist.
Pin protocol: src/project.v header. Source of truth: sim/numerics/v2_sizing/tt_latch_top/ on metronome-v2.0."""
import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, Timer


async def cmd(dut, data, mode):
    dut.ui_in.value = data
    dut.uio_in.value = mode << 1
    await ClockCycles(dut.clk, 1)
    dut.uio_in.value = (mode << 1) | 1
    await ClockCycles(dut.clk, 4)
    dut.uio_in.value = mode << 1
    await ClockCycles(dut.clk, 4)


def fold(vals):
    f = [0] * 6
    for k, v in enumerate(vals):
        for b in range(8):
            f[(8 * k + b) % 6] ^= (v >> b) & 1
    return sum(bit << j for j, bit in enumerate(f))


@cocotb.test()
async def test_project(dut):
    # About 60 MHz (info.yaml clock_hz); cocotb needs an even number of 1 ps steps.
    cocotb.start_soon(Clock(dut.clk, 16.666, unit="ns").start())
    dut.ena.value = 1
    dut.ui_in.value = 0
    dut.uio_in.value = 0
    dut.rst_n.value = 0
    await ClockCycles(dut.clk, 10)
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 4)
    await Timer(1, unit="ns")
    assert int(dut.uo_out.value) == 0
    assert (int(dut.uio_out.value) >> 2) == 0
    assert int(dut.uio_oe.value) == 0xFC

    ref = [0] * 256
    await cmd(dut, 0, 0)                          # address 0
    rnd = random.Random(1)
    for k in range(256):                          # sequential auto-increment writes
        ref[k] = rnd.randrange(1, 256)
        await cmd(dut, ref[k], 1)
    await Timer(1, unit="ns")
    assert (int(dut.uio_out.value) >> 2) == fold(ref), "XOR fold mismatch"
    for a in (0, 1, 77, 254, 255):                # readback of single bytes
        await cmd(dut, a, 0)
        await Timer(1, unit="ns")
        assert int(dut.uo_out.value) == ref[a], f"readback {a}"

    await cmd(dut, 77, 0)                         # overwrite one byte; neighbours unchanged
    await cmd(dut, 0x5A, 1)
    ref[77] = 0x5A
    for a in (76, 77, 78):
        await cmd(dut, a, 0)
        await Timer(1, unit="ns")
        assert int(dut.uo_out.value) == ref[a], f"after overwrite, byte {a}"

    dut.rst_n.value = 0                           # reset clears the bank
    await ClockCycles(dut.clk, 2)
    await Timer(1, unit="ns")
    assert int(dut.uo_out.value) == 0
    assert (int(dut.uio_out.value) >> 2) == 0
