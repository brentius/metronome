"""Co-simulation: Metronome (scorec SPI mode-0 controller) against the Winbond W25Q128JVxIM flash model.

Run by `python -m pytest code/tests/vendor_models -q` (see test_vendor_models.py for the build).
The device answers on MISO; every result is read back over the SPI host link (receive stream in data
RAM, stream POS/BIDX, CTRL and line registers).  The flash model is unmodified; the bench changes only
two of its parameters (NUM_PAGES, tPP) in tb_spi_flash.v.
"""
import sys
from pathlib import Path

import cocotb

sys.path.insert(0, str(Path(__file__).resolve().parent))
from vendor_common import Bench, HM, srt_addr, stream_addr   # noqa: E402

SCORE = "code/score/lib/spi_mode0.score"
BIND = "sck=O0 cs_n=O1 mosi=O2 miso=P3"
RATE_HZ = 4_000_000                    # 15 chip cycles per SCK period (250 ns; 4-cycle sample margin)
PERIOD = 15
JEDEC = bytes((0xEF, 0x70, 0x18))      # W25Q128JV: Winbond, SPI NOR, 128 Mbit

TX_BASE = 0x000                        # stream 0 start: an offset in data RAM (HM["DATA_BASE"] + TX_BASE)
RX_BASE = 0x400                        # stream 1 start: also an offset in data RAM


def compile_controller():
    import scorec
    root = Path(__file__).resolve().parents[3]
    return scorec.compile_score((root / SCORE).read_text(encoding="utf-8"), "controller", BIND,
                                rate_hz=RATE_HZ)


class Flash:
    """Host side of one CS_N-framed transfer at a time."""

    def __init__(self, bench: Bench, plan: list[bytes]):
        self.b = bench
        # One contiguous TX buffer, one offset per planned transfer (the stream start is a runtime register).
        self.offsets = []
        blob = bytearray()
        for tx in plan:
            self.offsets.append(len(blob))
            blob += tx
        self.blob = bytes(blob)
        self.plan = plan

    async def setup(self):
        await self.b.write(HM["DATA_BASE"] + TX_BASE, self.blob)
        await self.b.write(stream_addr(0, "LEN"), [0, 0])
        await self.b.write(stream_addr(1, "LEN"), [200, 0])
        await self.b.write(srt_addr(0, "CTL"), [1])
        await self.b.write(srt_addr(1, "CTL"), [1])
        await self.b.idle(20)

    async def transfer(self, k: int) -> bytes:
        tx = self.plan[k]
        start = TX_BASE + self.offsets[k]
        await self.b.write(stream_addr(0, "START"), [start & 0xFF, start >> 8, len(tx) & 0xFF, len(tx) >> 8])
        await self.b.write(srt_addr(0, "CTL"), [1])
        await self.b.write(srt_addr(1, "CTL"), [1])
        await self.b.idle(20)
        await self.b.write(HM["CTRL_BASE"] + 4, [1])             # go byte for the controller thread
        await self.b.wait((len(tx) * 8 + 8) * PERIOD + 120)
        pos = await self.b.read(srt_addr(1, "POSL"), 3)
        got = pos[0] | ((pos[1] & 0x0F) << 8)
        assert got == len(tx), f"transfer {k}: receive stream POS {got}, expected {len(tx)}"
        assert not (pos[1] & 0x80), f"transfer {k}: stream 1 STARVED"
        return bytes(await self.b.read(HM["DATA_BASE"] + RX_BASE, len(tx)))


@cocotb.test()
async def spi_flash(dut):
    b = Bench(dut)
    await b.start()
    compiled = compile_controller()

    plan = [
        bytes((0x9F, 0xFF, 0xFF, 0xFF)),                            # 0 JEDEC ID
        bytes((0x05, 0xFF)),                                       # 1 read status
        bytes((0x02, 0x00, 0x00, 0x10, 0x11, 0x22, 0x33, 0x44)),    # 2 program, no WREN
        bytes((0x05, 0xFF)),                                       # 3 read status
        bytes((0x03, 0x00, 0x00, 0x10, 0xFF, 0xFF, 0xFF, 0xFF)),    # 4 read
        bytes((0x06,)),                                            # 5 WREN
        bytes((0x05, 0xFF)),                                       # 6 read status
        bytes((0x02, 0x00, 0x00, 0x10, 0xDE, 0xAD, 0xBE, 0xEF)),    # 7 page program
        bytes((0x05, 0xFF)),                                       # 8 read status (WIP)
        bytes((0x05, 0xFF)),                                       # 9 read status (done)
        bytes((0x03, 0x00, 0x00, 0x10, 0xFF, 0xFF, 0xFF, 0xFF)),    # 10 read back
        bytes((0x03, 0x00, 0x00, 0x14, 0xFF, 0xFF, 0xFF, 0xFF)),    # 11 read past the data
        bytes((0x03, 0x00, 0x00, 0x0C, 0xFF, 0xFF, 0xFF, 0xFF)),    # 12 read before the data
        bytes((0x05, 0xFF)),                                       # 13 read status
    ]
    flash = Flash(b, plan)
    await b.load(compiled.program)
    await flash.setup()

    assert await b.read_u8(HM["CTRL_BASE"] + 7) == 0xA2, "chip ID"

    # JEDEC ID (9Fh): the flash shifts out EF 70 18 while the controller clocks 0xFF.
    rx = await flash.transfer(0)
    assert rx[1:4] == JEDEC, f"JEDEC ID read {rx[1:4].hex()}, expected {JEDEC.hex()}"
    dut._log.info(f"JEDEC ID: {rx[1:4].hex()}")

    # Status register before any write: WEL = 0, WIP = 0.
    rx = await flash.transfer(1)
    assert rx[1] & 0x03 == 0, f"status {rx[1]:#04x} after reset"

    # A page program without WREN must be ignored (the model's write-enable gate).
    await flash.transfer(2)
    rx = await flash.transfer(3)
    assert rx[1] & 0x03 == 0, f"status {rx[1]:#04x} after a program without WREN"
    rx = await flash.transfer(4)
    assert rx[4:8] == b"\xff\xff\xff\xff", f"program without WREN changed flash: {rx[4:8].hex()}"

    # WREN, then page program: WEL shows in the status register and WIP sets while tPP runs.
    payload = bytes((0xDE, 0xAD, 0xBE, 0xEF))
    rx = await flash.transfer(5)
    # The flash leaves DO released outside a read, so the pad (no pull-up in this bench) reads 0.
    assert rx[0] == 0x00, f"MISO during WREN: {rx[0]:#04x}"
    rx = await flash.transfer(6)
    assert rx[1] & 0x02, f"WEL not set after WREN (status {rx[1]:#04x})"
    await flash.transfer(7)
    rx = await flash.transfer(8)
    assert rx[1] & 0x01, f"WIP not set while the page program is in flight (status {rx[1]:#04x})"
    await b.wait(3200)                                           # tPP = 100 us in this bench (model parameter)
    rx = await flash.transfer(9)
    assert rx[1] & 0x03 == 0, f"status {rx[1]:#04x} after the program cycle completed"

    # READ (03h) returns the programmed bytes; the bytes around them stay erased.
    rx = await flash.transfer(10)
    assert rx[4:8] == payload, f"read back {rx[4:8].hex()}, expected {payload.hex()}"
    rx = await flash.transfer(11)
    assert rx[4:8] == b"\xff\xff\xff\xff", f"erased region read {rx[4:8].hex()}"
    rx = await flash.transfer(12)
    assert rx[4:8] == b"\xff\xff\xff\xff", f"bytes before the program read {rx[4:8].hex()}"

    # WEL cleared itself after the program.
    rx = await flash.transfer(13)
    assert rx[1] & 0x03 == 0, f"status {rx[1]:#04x} at the end"

    # The machine raised no sticky error and the controller is back in its idle state.
    pos = await b.read(srt_addr(1, "POSL"), 3)
    assert not (pos[1] & 0x80), f"stream 1 STARVED: {pos[1]:#04x}"
    ctrl = await b.read(HM["CTRL_BASE"], 2)
    assert ctrl[0] & 1, "RUN_global"
    assert not (ctrl[1] & 0x05), f"sticky CONFLICT/MEMHAZ: {ctrl[1]:#04x}"
    dut._log.info(f"{b.cycle} cycles, {sum(len(tx) for tx in plan)} bytes on the wire")
