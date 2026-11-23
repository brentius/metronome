"""Co-simulation: Metronome (scorec I2C controller) against the 24LC256 EEPROM model.

Run by `python -m pytest code/tests/vendor_models -q` (see test_vendor_models.py for the build).

The chip is the I2C controller: P0 = SCL, P1 = SDA, both open drain.  The device acknowledges its address, takes
a page write, refuses acknowledges for its write cycle (ack polling), and returns the stored bytes on a read.
Everything the host checks crosses the real pins; the model is unmodified (the bench only preloads its array and
shortens its write-cycle time, see tb_i2c_eeprom.v).
"""
import sys
from pathlib import Path

import cocotb

sys.path.insert(0, str(Path(__file__).resolve().parent))
from vendor_common import Bench, HM, srt_addr, stream_addr   # noqa: E402

from scorec.bus import controller_rx, controller_tx          # noqa: E402

SCORE = "code/score/lib/i2c.score"
BIND = "scl=P0/O0 sda=P1/O1"
RATE_HZ = 300_000                      # within the part's 400 kHz rating and above the model's tLO=1.3 us check
BEAT = 200                             # chip cycles per I2C beat at 60 MHz and 300 kHz
T_WC = 200_000                         # write cycle time as set in tb_i2c_eeprom.v, ns

TX_BASE = 0x000                        # stream 0 (controller transmit bits) lives at data RAM offset 0
RX_BASE = 0x400                        # stream 1 (controller receive bits), as the compiled image configures it
DEV = 0x50                             # 24LC256 device address with A2..A0 = 000
ADDR = 0x0040                          # word address exercised
PAGE = bytes((0xDE, 0xAD, 0xBE, 0xEF))
ERASED = 0xFF


def compile_controller():
    import scorec
    root = Path(__file__).resolve().parents[3]
    return scorec.compile_score((root / SCORE).read_text(encoding="utf-8"), "controller", BIND,
                                rate_hz=RATE_HZ)


def beats(requests) -> int:
    """Upper bound on controller beats for one transaction (code/tests/scorec/test_i2c.py)."""
    return 4 + len(requests) + sum(10 + 9 * (len(a) if kind == "w" else a) for _ad, kind, a in requests)


def expect(got, want, what: str):
    """The one comparison the positive and the negative control both go through."""
    assert got == want, f"{what}: got {got!r}, expected {want!r}"


class Peer:
    def __init__(self, bench: Bench):
        self.b = bench

    async def setup(self):
        await self.b.write(stream_addr(0, "LEN"), [0, 0])
        await self.b.write(stream_addr(1, "LEN"), [200, 0])
        await self.b.write(srt_addr(0, "CTL"), [1])
        await self.b.write(srt_addr(1, "CTL"), [1])
        await self.b.idle(20)

    async def txn(self, requests, extra=0):
        """Run one controller transaction; return (host status byte, decoded receive data)."""
        tx = controller_tx(requests)
        await self.b.write(HM["DATA_BASE"] + TX_BASE, tx)
        await self.b.write(stream_addr(0, "LEN"), [len(tx) & 0xFF, len(tx) >> 8])
        await self.b.write(srt_addr(0, "CTL"), [1])
        await self.b.write(srt_addr(1, "CTL"), [1])
        await self.b.idle(20)
        await self.b.write(HM["CTRL_BASE"] + 4, [1])                  # go byte (HOST.IN)
        await self.b.wait(beats(requests) * BEAT + 400 + extra)
        stat = await self.b.read(HM["CTRL_BASE"] + 6, 1)              # HOSTSTAT: bit 1 OUTV
        assert stat[0] & 0x02, f"transaction did not finish: HOSTSTAT={stat[0]:#04x}"
        out = await self.b.read_u8(HM["CTRL_BASE"] + 5)               # HOST.OUT: 0 done, 1 address NACK
        await self.b.write(HM["CTRL_BASE"] + 6, [0x02])               # clear OUTV
        pos = await self.b.read(srt_addr(1, "POSL"), 3)
        nbytes, bits = pos[0] | ((pos[1] & 0x0F) << 8), pos[1] >> 4
        assert not (pos[1] & 0x80), "receive stream STARVED"
        data = bytes(await self.b.read(HM["DATA_BASE"] + RX_BASE, max(1, nbytes)))
        return out, controller_rx(requests, data, nbytes * 8 + bits)


@cocotb.test()
async def i2c_eeprom(dut):
    b = Bench(dut)
    await b.start()
    peer = Peer(b)
    await b.load(compile_controller().program)
    await peer.setup()

    assert await b.read_u8(HM["CTRL_BASE"] + 7) == 0xA2, "chip ID"
    assert int(dut.bus_fault.value) == 0, "the chip drove a '1' onto the open-drain bus"

    # ---- write: device address, two word-address bytes, four data bytes ------------------------------
    out, rx = await peer.txn([(DEV, "w", bytes((ADDR >> 8, ADDR & 0xFF, *PAGE)))])
    assert out == 0, f"write not acknowledged: HOST.OUT={out}"
    assert rx == [(0, [0] * 6)], f"write acknowledges: {rx}"

    # ---- acknowledge polling: the device refuses its address while the write cycle runs ---------------
    # A driver probes the address with R/W = 0 until the device acknowledges.  The model answers 1 (NACK)
    # for the whole write cycle, so the first probe must fail and a later one succeed.
    out_busy, _ = await peer.txn([(DEV, "w", b"")])
    assert out_busy == 1, "the device acknowledged while its write cycle was still running"
    await b.wait(int(round(T_WC / 1e9 * 60e6)) + 600)                  # one write cycle
    out_idle, _ = await peer.txn([(DEV, "w", b"")])
    assert out_idle == 0, "the device still refuses its address after the write cycle"
    # Model quirk (code/tests/vendor_models/FINDINGS.md, F1): the write-address-only probe leaves a stale
    # write-buffer count, so the model starts a second (harmless, same-data) write cycle at the probe's
    # STOP.  A real 24LC256 is idle here; we wait one write cycle and say so.
    await b.wait(int(round(T_WC / 1e9 * 60e6)) + 600)

    # ---- read back: dummy write of the word address, repeated start, six bytes -----------------------
    start_word = ADDR - 2                                              # two erased bytes, then the page
    out, rx = await peer.txn([(DEV, "w", bytes((start_word >> 8, start_word & 0xFF))), (DEV, "r", 6)])
    assert out == 0, f"read transaction failed: HOST.OUT={out}"
    got = bytes(rx[1][1])
    expect(got, bytes((ERASED, ERASED)) + PAGE, "read-back of the programmed page")
    dut._log.info(f"EEPROM read-back at {start_word:#06x}: {got.hex()}")

    # ---- negative controls --------------------------------------------------------------------------
    # (a) a different word address must not hold the page
    out, rx = await peer.txn([(DEV, "w", bytes((0x01, 0x00))), (DEV, "r", 4)])
    assert out == 0
    other = bytes(rx[1][1])
    expect(other, bytes((ERASED,)) * 4, "read-back of an unprogrammed word address")
    poisoned = PAGE[:4]
    try:
        expect(other, poisoned, "deliberately wrong expectation")
    except AssertionError:
        pass
    else:                                              # pragma: no cover - the control must fail
        raise AssertionError("the checker accepted wrong data: the positive control is vacuous")

    # (b) a wrong device address must be refused, not silently mapped to the EEPROM
    out, _ = await peer.txn([(0x51, "w", b"")])
    assert out == 1, "a 0x51 address was acknowledged by a 0x50 device"

    assert int(dut.bus_fault.value) == 0, "the chip drove a '1' onto the open-drain bus"
    ctrl = await b.read(HM["CTRL_BASE"], 2)
    assert ctrl[0] & 1, "RUN_global"
    assert not (ctrl[1] & 0x05), f"sticky CONFLICT/MEMHAZ: {ctrl[1]:#04x}"
    dut._log.info(f"{b.cycle} cycles, {b.cycle / 60e6 * 1e3:.1f} ms of bus time")
