"""SPI mode 0 "target" (peripheral role) compiled from the library copy of spec 16.3 and run on the cycle model against a
mode-0 controller waveform written in indep_more.py (not the score codec).  All 256 byte values in both directions."""
import os
import random

import indep_more as ind
import pytest
from libharness import *
from harness import spec_block
from score import check, parse

SRC = lib_text("spi_mode0")
BIND = "sck=P0 mosi=P1 cs_n=P2 miso=O8"


def test_library_text_is_the_spec_example():
    assert spec_block(2) in SRC
    assert [str(d) for d in check(parse(SRC)) if d.code.startswith("E-")] == []


def run_peripheral(mosi, miso_bytes, period=60):
    import scorec
    c = scorec.compile_score(SRC, "peripheral", BIND)
    chip = new_chip(c)
    chip.backdoor_write(HM["DATA_BASE"], bytes(miso_bytes))
    stream_reg(chip, 0, "LEN", len(miso_bytes) + 2, 2)
    stream_rewind(chip, 0)
    sck, cs, mo = ind.spi0_controller_wave(list(mosi), period, lead=60, tail=200)
    for _ in range(60):
        chip.step(IDLE, 0b100)
    miso = []
    for t in range(len(sck)):
        uo, _, _ = chip.step(IDLE, sck[t] | (mo[t] << 1) | (cs[t] << 2))
        miso.append((uo >> 2) & 1)
    return chip, (sck, cs, mo), miso


def miso_at_rises(sck, miso):
    """What a mode-0 controller reads: MISO one cycle before every rising SCK edge."""
    return [miso[t - 1] for t in range(1, len(sck)) if sck[t] and not sck[t - 1]]


def bits_msb(bs):
    return [(b >> (7 - i)) & 1 for b in bs for i in range(8)]


@pytest.mark.parametrize("seed", range(3))
def test_random_transfers_both_directions(seed):
    rng = random.Random(seed)
    n = rng.randrange(2, 9)
    mo, mi = bytes(rng.randrange(256) for _ in range(n)), bytes(rng.randrange(256) for _ in range(n))
    chip, (sck, cs, _), miso = run_peripheral(mo, mi)
    assert miso_at_rises(sck, miso) == bits_msb(mi)
    s = chip.mem.streams[1]
    assert bytes(chip.mem.data[0x400:0x400 + s.POS]) == mo
    model_clean(chip)
    assert chip.lines[0].TAPMISS == 0


def test_byte_values_in_both_directions_in_one_transfer():
    """All 256 values in one transfer with SCORE_LIB_SLOW=1 (about 40 s); otherwise a shuffled 64-value subset."""
    vals = list(range(256)) if os.environ.get("SCORE_LIB_SLOW") else random.Random(4).sample(range(256), 64)
    mo = bytes(vals)
    mi = bytes((255 - v) for v in vals)
    chip, (sck, cs, _), miso = run_peripheral(mo, mi)
    assert miso_at_rises(sck, miso) == bits_msb(mi)
    s = chip.mem.streams[1]
    assert s.POS == len(mo) and bytes(chip.mem.data[0x400:0x400 + len(mo)]) == mo
    model_clean(chip)


def test_miso_returns_to_idle_when_cs_rises():
    chip, (sck, cs, _), miso = run_peripheral(bytes([0xA5, 0x5A]), bytes([0xFF, 0xFF]))
    assert miso[-100:] == [0] * 100
