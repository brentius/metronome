"""v3 top-level checks that a lockstep run cannot afford: the edge-capture counter DC saturating at 2^19 - 1
(SPEC v2 12.4). DC is deposited near the limit instead of simulating 524k cycles."""
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, RisingEdge

MAX = (1 << 19) - 1


@cocotb.test()
async def dc_saturates(dut):
    cocotb.start_soon(Clock(dut.clk, 16, unit="ns").start())
    dut.ena.value = 1
    dut.ui_in.value = 0x02
    dut.uio_in.value = 0
    dut.rst_n.value = 0
    for _ in range(3):
        await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    for _ in range(4):
        await RisingEdge(dut.clk)
    await FallingEdge(dut.clk)
    dut.cen.value = 1
    dut.emask.value = 1
    dut.dc.value = MAX - 3
    seen = []
    for _ in range(10):
        await FallingEdge(dut.clk)
        seen.append(int(dut.dc.value))
    assert seen[:3] == [MAX - 2, MAX - 1, MAX] and all(v == MAX for v in seen[2:]), seen
    dut.uio_in.value = 1                                   # an edge on P0 (masked in): DC restarts at 1
    for _ in range(3):
        await FallingEdge(dut.clk)
    assert int(dut.dc.value) == 1, int(dut.dc.value)
    await FallingEdge(dut.clk)
    assert int(dut.dc.value) == 2
