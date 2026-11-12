"""cocotb bench for cfg_latch_bank / cfg_flop_bank (same interface, BYTES=8). Run through test_cfg_latch_bank.py.

Timing convention (documented in sim/numerics/v2_sizing/LATCH_SIZING.md): `we` and the write fields are sampled on
rising edge E1; q changes shortly after the NEXT rising edge E2 (latency 2 cycles from the sampling edge), so a
register sampling q at E3 sees the new value.
Write spacing (cfg_latch_bank r3 rule): `we` is never high on two consecutive edges; `write()` leaves one idle edge."""
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

BYTES = 8


async def start(dut, hold_reset=3):
    cocotb.start_soon(Clock(dut.clk, 16, unit="ns").start())
    dut.we.value = 0
    dut.waddr.value = 0
    dut.wdata.value = 0
    dut.rst_n.value = 0
    for _ in range(hold_reset):
        await RisingEdge(dut.clk)
    await Timer(1, unit="ns")


async def release(dut):
    """Release reset just after a rising edge; returns after the next 3 edges (synchroniser flushed)."""
    dut.rst_n.value = 1
    for _ in range(3):
        await RisingEdge(dut.clk)
    await Timer(1, unit="ns")


async def write(dut, addr, data):
    """Present one write for exactly one rising edge (E1), then one idle edge (write spacing rule).
    The write fields are scrambled while `we` is low, to show data is taken only on the write edge."""
    dut.we.value = 1
    dut.waddr.value = addr
    dut.wdata.value = data
    await RisingEdge(dut.clk)
    dut.we.value = 0
    dut.wdata.value = (~data) & 0xFF
    await RisingEdge(dut.clk)
    await Timer(1, unit="ns")


def no_spacing_error(dut):
    if hasattr(dut, "wr_spacing_err"):
        assert int(dut.wr_spacing_err.value) == 0, "write spacing rule violated"


def byte(dut, k):
    return (int(dut.q.value) >> (8 * k)) & 0xFF


async def settle(dut, n=3):
    for _ in range(n):
        await RisingEdge(dut.clk)
    await Timer(1, unit="ns")


@cocotb.test()
async def test_reset_clears(dut):
    await start(dut)
    assert int(dut.q.value) == 0
    await release(dut)
    for k in range(BYTES):
        await write(dut, k, 0xA0 + k)
    await settle(dut)
    assert byte(dut, 3) == 0xA3
    dut.rst_n.value = 0                      # async assert: clears without waiting for a clock edge
    await Timer(1, unit="ns")
    assert int(dut.q.value) == 0, hex(int(dut.q.value))


@cocotb.test()
async def test_single_write_only_its_byte(dut):
    await start(dut)
    await release(dut)
    await write(dut, 5, 0x5A)
    await settle(dut)
    assert int(dut.q.value) == 0x5A << 40, hex(int(dut.q.value))
    no_spacing_error(dut)


@cocotb.test()
async def test_spaced_writes(dut):
    """Writes every other cycle (the fastest the spacing rule allows): each byte gets its own value."""
    await start(dut)
    await release(dut)
    vals = [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88]
    for k, v in enumerate(vals):
        await write(dut, k, v)
    await settle(dut)
    assert [byte(dut, k) for k in range(BYTES)] == vals
    for v in (0xC1, 0xC2, 0xC3):              # rewriting one byte every other cycle: last value wins
        await write(dut, 2, v)
    await settle(dut)
    assert byte(dut, 2) == 0xC3 and byte(dut, 1) == 0x22 and byte(dut, 3) == 0x44
    no_spacing_error(dut)


@cocotb.test()
async def test_consecutive_write_flagged(dut):
    """The latch bank's simulation check flags `we` on consecutive edges (the flop bank has no such rule)."""
    await start(dut)
    await release(dut)
    if dut._name != "cfg_latch_bank":
        return
    assert hasattr(dut, "wr_spacing_err"), "COCOTB_SIM check missing from the latch bank build"
    assert int(dut.wr_spacing_err.value) == 0
    dut.we.value = 1
    for k in (0, 1):
        dut.waddr.value = k
        dut.wdata.value = 0x5 + k
        await RisingEdge(dut.clk)
    dut.we.value = 0
    await settle(dut, 1)
    assert int(dut.wr_spacing_err.value) == 1


@cocotb.test()
async def test_write_in_reset_release_cycle_ignored(dut):
    await start(dut)
    dut.rst_n.value = 1                       # reset releases; this is the first edge that sees rst_n high
    dut.we.value = 1
    dut.waddr.value = 4
    dut.wdata.value = 0xEE
    await RisingEdge(dut.clk)                 # write presented in the release cycle (E_R)
    await RisingEdge(dut.clk)                 # and held through the second synchroniser stage
    dut.we.value = 0
    await settle(dut, 4)
    assert int(dut.q.value) == 0, hex(int(dut.q.value))
    await write(dut, 4, 0x77)                 # a normal write afterwards works
    await settle(dut)
    assert byte(dut, 4) == 0x77


@cocotb.test()
async def test_out_of_range_ignored(dut):
    await start(dut)
    await release(dut)
    for a in range(BYTES, 2 ** len(dut.waddr)):
        await write(dut, a, 0xFF)
    await settle(dut)
    assert int(dut.q.value) == 0, hex(int(dut.q.value))


@cocotb.test()
async def test_latency(dut):
    await start(dut)
    await release(dut)
    dut.we.value = 1
    dut.waddr.value = 6
    dut.wdata.value = 0x9C
    await RisingEdge(dut.clk)                 # E1: write sampled
    dut.we.value = 0
    await Timer(1, unit="ns")
    assert byte(dut, 6) == 0, "q must not change after E1"
    await RisingEdge(dut.clk)                 # E2
    await Timer(1, unit="ns")
    assert byte(dut, 6) == 0x9C, "q must show the data after E2 (2 cycles from sampling edge)"
