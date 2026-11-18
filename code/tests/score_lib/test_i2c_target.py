"""I2C target compiled from the library copy of spec 16.2 and run on the cycle model against a controller waveform written
in indep_more.py (UM10204 timing, not the score codec); the resolved bus is decoded by an independent bus decoder.
All 256 byte values are written to the target in one transaction at 400 kHz."""
import os
import random

import indep_more as ind
import pytest
from libharness import *
from harness import spec_block
from score import check, parse

SRC = lib_text("i2c")
BEAT = 150                                      # chip cycles per bit at 400 kHz


def test_library_text_is_the_spec_example():
    assert spec_block(1) in SRC
    assert [str(d) for d in check(parse(SRC)) if d.code.startswith("E-")] == []


def run_target(my, addr, data, beat=BEAT):
    import scorec
    from scorec.bus import target_rx
    c = scorec.compile_score(SRC, "target", "scl=P0 sda=P1/O1", follow_period=4 * 600, params={"my_addr": my}, rate_hz=60e6 / beat)
    chip = new_chip(c)
    chip.backdoor_write(HM["DATA_BASE"], b"\x00")
    stream_reg(chip, 0, "LEN", 1, 2)
    stream_rewind(chip, 0)
    stream_rewind(chip, 1)
    for _ in range(80):
        chip.step(IDLE, 0b11)
    scl_c, sda_c = ind.i2c_controller_wave(addr, data, beat)
    scl, sda = [], []
    uo, uio, oe = chip.step(IDLE, 0b11)
    for t in range(len(scl_c) + 4 * beat):
        cs = scl_c[t] if t < len(scl_c) else 1
        cd = sda_c[t] if t < len(sda_c) else 1
        chip_sda = 0 if (oe >> 1) & 1 and not (uio >> 1) & 1 else 1     # open drain: an enabled output pulls low
        bus_sda = cd & chip_sda
        scl.append(cs)
        sda.append(bus_sda)
        uo, uio, oe = chip.step(IDLE, cs | (bus_sda << 1))
    s1 = chip.mem.streams[1]
    rec = target_rx(bytes(chip.mem.data[0x400:0x400 + s1.POS]), my)
    return chip, scl, sda, rec


def expected_events(addr, data, acked):
    ev = [("S",), ("B", addr << 1, acked)]
    if acked:
        ev += [("B", d, True) for d in data]
    return ev + [("P",)] if acked else ev


SLOW = bool(os.environ.get("SCORE_LIB_SLOW"))


def test_byte_values_written_and_acknowledged():
    """All 256 values with SCORE_LIB_SLOW=1 (about 65 s); otherwise a shuffled 48-value subset that still spans the range."""
    my = 0x2B
    data = bytes(range(256)) if SLOW else bytes(random.Random(2).sample(range(256), 48))
    chip, scl, sda, rec = run_target(my, my, data)
    bus = ind.i2c_bus_decode(scl, sda)
    assert bus == [("S",), ("B", my << 1, True)] + [("B", d, True) for d in data] + [("P",)]
    assert rec == [[(my, 0, list(data))]]
    model_clean(chip)
    assert all(ln.TAPMISS == 0 for ln in chip.lines)


@pytest.mark.parametrize("rate_div", [1, 4])
def test_address_match_ack_and_nack_at_100_and_400_khz(rate_div):
    my = 0x51
    beat = 600 // rate_div
    chip, scl, sda, rec = run_target(my, my, b"\xa5\x5a", beat)
    assert ind.i2c_bus_decode(scl, sda) == expected_events(my, b"\xa5\x5a", True)
    assert rec == [[(my, 0, [0xA5, 0x5A])]]
    chip, scl, sda, rec = run_target(my, my ^ 0x08, b"\x11", beat)
    ev = ind.i2c_bus_decode(scl, sda)
    assert ev[:2] == [("S",), ("B", (my ^ 0x08) << 1, False)]               # a different address: the target does not pull SDA low
    assert all(e[0] != "B" or not e[2] for e in ev) and rec == [[((my ^ 0x08), 0, None)]]
    model_clean(chip)
