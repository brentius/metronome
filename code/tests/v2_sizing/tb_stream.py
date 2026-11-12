"""cocotb bench for md2_stream. All activity happens at falling clock edges, so every output sampled there is the
settled state after the previous rising edge, and inputs set there act at the end of the cycle (move semantics)."""
from __future__ import annotations

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge


class Bench:
    """Drives the stream and models a 512 x 32 synchronous RAM behind an arbiter that can withhold grants.

    grant_policy(cycle, req_addr, req_we) -> bool decides each cycle whether a pending request is granted."""

    def __init__(self, dut):
        self.dut = dut
        self.ram = [0] * 512
        self.cycle = 0
        self.grant_policy = lambda cyc, addr, we: True
        self.grants = 0
        self._rd = 0

    # byte-level RAM helpers (little endian bytes in words)
    def poke(self, baddr, val):
        w, l = baddr >> 2, baddr & 3
        self.ram[w] = (self.ram[w] & ~(0xFF << (8 * l))) | (val << (8 * l))

    def peek(self, baddr):
        return (self.ram[baddr >> 2] >> (8 * (baddr & 3))) & 0xFF

    async def start(self):
        d = self.dut
        cocotb.start_soon(Clock(d.clk, 10, unit="ns").start())
        await self.reset()

    async def reset(self, mode=0, msb=0, start=0, length=0, mark=0):
        d = self.dut
        d.rst_n.value = 0
        for s in ("adv", "rx_bit_we", "rx_bit", "ctl_we", "ctl", "clr_starved", "gnt", "rdata"):
            getattr(d, s).value = 0
        self.config(mode, msb, start, length, mark)
        self.grant_policy = lambda cyc, addr, we: True
        for _ in range(3):
            await FallingEdge(d.clk)
        d.rst_n.value = 1
        self._rd = 0
        await FallingEdge(d.clk)

    def config(self, mode, msb, start, length, mark=0):
        d = self.dut
        d.cfg_mode.value, d.cfg_msb.value, d.cfg_start.value = mode, msb, start
        d.cfg_len.value, d.cfg_mark.value = length, mark

    async def cycle_(self, adv=0, rxb=None, ctl=None, clr=0):
        """Run one cycle; return a dict of the outputs as seen during that cycle (before its inputs take effect)."""
        d = self.dut
        seen = dict(bit=int(d.bit_out.value), byte=int(d.byte_out.value), end=int(d.g_end.value),
                    mark=int(d.g_mark.value), gbyte=int(d.g_byte.value), starved=int(d.starved.value),
                    pos=int(d.pos.value), bitidx=int(d.bitidx.value))
        d.rdata.value = self._rd                      # data of the read granted in the previous cycle
        d.adv.value = adv
        d.rx_bit_we.value = 0 if rxb is None else 1
        d.rx_bit.value = 0 if rxb is None else rxb
        d.ctl_we.value = 0 if ctl is None else 1
        d.ctl.value = 0 if ctl is None else ctl
        d.clr_starved.value = clr
        g = 0
        if int(d.req.value) and self.grant_policy(self.cycle, int(d.req_addr.value), int(d.req_we.value)):
            g = 1
            self.grants += 1
            a = int(d.req_addr.value)
            if int(d.req_we.value):
                m, wd = int(d.req_wmask.value), int(d.req_wdata.value)
                for l in range(4):
                    if (m >> l) & 1:
                        self.ram[a] = (self.ram[a] & ~(0xFF << (8 * l))) | (wd & (0xFF << (8 * l)))
            else:
                self._rd = self.ram[a]
        d.gnt.value = g
        self.cycle += 1
        await FallingEdge(d.clk)
        return seen

    async def idle(self, n):
        for _ in range(n):
            await self.cycle_()

    async def rewind(self, wait=12):
        await self.cycle_(ctl=1)
        await self.idle(wait)


def exp_bits(data, msb):
    out = []
    for b in data:
        out += [(b >> (7 - i)) & 1 if msb else (b >> i) & 1 for i in range(8)]
    return out


def fill(bn, base, n, seed=0x5A):
    data = [(seed + 37 * i) & 0xFF for i in range(n)]
    for i, v in enumerate(data):
        bn.poke(base + i, v)
    return data


async def tx_run(bn, data, msb, pace, start, mark_byte):
    """Stream len(data) bytes; check every bit and guard, then check that advancing at END does nothing."""
    n = len(data)
    bn.config(0, msb, start, n, mark_byte)
    await bn.rewind()
    bits = exp_bits(data, msb)
    for k, eb in enumerate(bits):
        s = await bn.cycle_(adv=1)
        assert s["bit"] == eb, f"bit {k} (byte {k // 8}) got {s['bit']} want {eb}"
        assert s["gbyte"] == (k % 8 == 0), f"BYTE guard at bit {k}"
        assert s["mark"] == (k % 8 == 0 and k // 8 == mark_byte), f"MARK guard at bit {k}"
        assert s["end"] == 0, f"END early at bit {k}"
        assert s["pos"] == k // 8 and s["bitidx"] == k % 8
        assert s["byte"] == data[k // 8], f"byte_out at bit {k}"
        for _ in range(pace - 1):
            await bn.cycle_()
    s = await bn.cycle_(adv=1)
    assert s["end"] == 1 and s["pos"] == n and s["bitidx"] == 0 and s["bit"] == 0
    s = await bn.cycle_(adv=1)
    assert s["pos"] == n and s["bitidx"] == 0, "advance at END must do nothing"
    assert s["starved"] == 0, "starved with prompt grants"


@cocotb.test()
async def test_tx_unaligned(dut):
    bn = Bench(dut)
    await bn.start()
    for msb in (0, 1):
        for pace in (1, 6):
            await bn.reset()
            bn.ram = [0xFFFFFFFF] * 512
            data = fill(bn, 5, 5)            # unaligned: bytes 5..9, crossing a word boundary twice
            await tx_run(bn, data, msb, pace, 5, 2)


@cocotb.test()
async def test_tx_longer_all_alignments(dut):
    bn = Bench(dut)
    await bn.start()
    for start in (0, 1, 2, 3, 2047 - 15):
        await bn.reset()
        data = fill(bn, start, 16, seed=start + 1)
        await tx_run(bn, data, 1, 6, start, 15)


@cocotb.test()
async def test_rx_flush(dut):
    bn = Bench(dut)
    await bn.start()
    for msb in (0, 1):
        await bn.reset()
        bn.ram = [0xAAAAAAAA] * 512
        bn.config(1, msb, 6, 16, 0)
        await bn.rewind(2)
        data = [0xC5, 0x3E]
        tail = [1, 0, 1]
        for b in exp_bits(data, msb) + tail:
            await bn.cycle_(rxb=b)
        s = await bn.cycle_()
        assert s["pos"] == 2 and s["bitidx"] == 3
        await bn.cycle_(ctl=2)               # flush
        await bn.idle(8)
        s = await bn.cycle_()
        assert s["pos"] == 3 and s["bitidx"] == 0
        tailbyte = (0b101 << 5) if msb else 0b101
        want = {6: data[0], 7: data[1], 8: tailbyte}
        for a in range(0, 16):
            assert bn.peek(a) == want.get(a, 0xAA), f"byte {a}: {bn.peek(a):02x} (msb={msb})"
        assert s["starved"] == 0


@cocotb.test()
async def test_rx_stops_at_end_and_flush_empty(dut):
    bn = Bench(dut)
    await bn.start()
    await bn.reset()
    bn.ram = [0] * 512
    bn.config(1, 0, 0, 1, 0)
    await bn.rewind(2)
    await bn.cycle_(ctl=2)                   # flush with nothing pending: nothing happens
    s = await bn.cycle_()
    assert s["pos"] == 0
    for k in range(24):
        await bn.cycle_(rxb=1)
    await bn.idle(8)
    s = await bn.cycle_()
    assert s["pos"] == 1 and s["end"] == 1
    assert bn.peek(0) == 0xFF and bn.peek(1) == 0 and bn.peek(2) == 0


@cocotb.test()
async def test_rx_overflow_starved(dut):
    bn = Bench(dut)
    await bn.start()
    await bn.reset()
    bn.grant_policy = lambda c, a, w: False
    bn.config(1, 0, 0, 8, 0)
    await bn.rewind(2)
    for k in range(15):                      # byte 0 completes and waits for grant; byte 1 still assembling
        s = await bn.cycle_(rxb=1)
        assert s["starved"] == 0
    await bn.cycle_(rxb=1)                   # byte 1 completes into a full buffer
    s = await bn.cycle_()
    assert s["starved"] == 1


@cocotb.test()
async def test_tx_starved_when_grants_withheld(dut):
    bn = Bench(dut)
    await bn.start()
    # prompt grants at Ethernet-rate pacing across 3 words: never starved
    await bn.reset()
    data = fill(bn, 0, 12)
    await tx_run(bn, data, 0, 6, 0, 3)       # tx_run asserts starved == 0 at the end
    # first fetch granted, later ones withheld: starved on entering byte 4
    await bn.reset()
    fill(bn, 0, 12)
    bn.grants = 0
    bn.grant_policy = lambda c, a, w: bn.grants < 1
    bn.config(0, 0, 0, 12, 0)
    await bn.rewind()
    for k in range(32):
        s = await bn.cycle_(adv=1)
        assert s["starved"] == 0, f"starved too early at bit {k}"
    s = await bn.cycle_(adv=1)
    s = await bn.cycle_()
    assert s["starved"] == 1, "starved must be set on entering byte 4"
    bn.grant_policy = lambda c, a, w: True
    await bn.idle(10)
    await bn.cycle_(clr=1)
    s = await bn.cycle_()
    assert s["starved"] == 0, "clr_starved clears the flag"


@cocotb.test()
async def test_tx_rewind_mid_frame(dut):
    bn = Bench(dut)
    await bn.start()
    await bn.reset()
    data = fill(bn, 3, 6)
    bn.config(0, 0, 3, 6, 0)
    await bn.rewind()
    for _ in range(11):
        await bn.cycle_(adv=1)
    await bn.rewind()
    bits = exp_bits(data, 0)
    for k, eb in enumerate(bits):
        s = await bn.cycle_(adv=1)
        assert s["bit"] == eb and s["pos"] == k // 8, f"replay bit {k}"
        await bn.idle(5)
    s = await bn.cycle_()
    assert s["end"] == 1 and s["starved"] == 0
