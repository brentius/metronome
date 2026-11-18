"""The two personalities: a beat-rate logic analyser and a waveform / pattern generator, on the cycle model, with their
host scripts (code/score/examples/*_host.py).  Checked against stimulus and decoders written here."""
import random
import sys

import pytest
from libharness import *

sys.path.insert(0, str(ROOT / "code/score/examples"))
import logic_analyser_host as la  # noqa: E402
import pattern_gen_host as pg  # noqa: E402
from score import check, parse  # noqa: E402


def read_vcd(path):
    """Minimal independent VCD reader for one 1-bit signal: -> [(time_ns, level)]."""
    out, t = [], 0
    for ln in path.read_text().splitlines():
        if ln.startswith("#"):
            t = int(ln[1:])
        elif len(ln) == 2 and ln[0] in "01":
            out.append((t, int(ln[0])))
    return out


def vcd_levels(changes, period_ns, n):
    """Sample a VCD's changes at the middle of each of n beats."""
    lv, k, cur = [], 0, changes[0][1]
    for i in range(n):
        mid = (i + 0.5) * period_ns
        while k < len(changes) and changes[k][0] <= mid:
            cur = changes[k][1]
            k += 1
        lv.append(cur)
    return lv


@pytest.mark.parametrize("name", ["pattern_gen", "logic_analyser"])
def test_parse_and_check(name):
    assert [str(d) for d in check(parse(lib_text(name))) if d.code.startswith("E-")] == []


# ---- pattern generator -------------------------------------------------------------------------------------
@pytest.mark.parametrize("rate", [1e6, 2.5e6, 5e6])
def test_pattern_gen_plays_random_bits_at_the_chosen_rate(rate):
    rng = random.Random(int(rate))
    bits = [1] + [rng.randrange(2) for _ in range(511)]            # starts with 1 so the first edge marks beat 0
    comp = pg.compile_pattern_gen(rate)
    chip, tr = pg.play(comp, bits, rate)
    beat = 60e6 / rate
    first = next(i for i in range(1, len(tr)) if tr[i] and not tr[i - 1])
    got = [tr[int(first + (k + 0.5) * beat)] for k in range(512)]
    assert got == bits
    for i in range(1, first + int(512 * beat)):                      # every edge is on the beat grid, +-1 chip cycle
        if tr[i] != tr[i - 1]:
            off = (i - first) % beat
            assert min(off, beat - off) <= 1.0, (i, off)
    assert tr[-int(2 * beat):] == [0] * int(2 * beat)                # the line returns to idle low
    model_clean(chip)


def test_pattern_gen_pack_is_lsb_first_and_pads():
    assert pg.pack([1, 0, 1]) == bytes([0b101]) + bytes(63)
    assert pg.pack([0] * 8 + [1])[1] == 1
    with pytest.raises(ValueError):
        pg.pack([1] * 513)


def test_pattern_gen_every_byte_value():
    """Bytes 0..255 as four 512-bit frames; each byte comes out LSB first.  Byte 0 of each frame has no leading edge, so
    frames are aligned on the first rising edge and the known position of the first set bit."""
    rate, beat = 5e6, 12
    comp = pg.compile_pattern_gen(rate)
    out = []
    for q in range(4):
        vals = list(range(64 * q, 64 * q + 64))
        bits = [(v >> i) & 1 for v in vals for i in range(8)]
        chip, tr = pg.play(comp, bits, rate)
        edge = next(i for i in range(1, len(tr)) if tr[i] and not tr[i - 1])
        start = edge - bits.index(1) * beat
        got = [tr[start + k * beat + beat // 2] for k in range(512)]
        out += [sum(got[8 * j + i] << i for i in range(8)) for j in range(64)]
    assert out == list(range(256))


def test_pattern_gen_vcd_round_trip(tmp_path):
    bits = [1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1] + [0] * 5
    comp = pg.compile_pattern_gen(1e6)
    chip, tr = pg.play(comp, bits, 1e6)
    pg.write_vcd(tr, tmp_path / "p.vcd")
    ch = read_vcd(tmp_path / "p.vcd")
    first = next(t for t, v in ch if v == 1)
    got = vcd_levels(ch, 1000.0, 600)
    k0 = round(first / 1000)
    assert got[k0:k0 + len(bits)] == bits


# ---- logic analyser ----------------------------------------------------------------------------------------
@pytest.mark.parametrize("rate", [1e6, 2e6, 500e3])
def test_logic_analyser_captures_the_pin_every_beat(rate):
    rng = random.Random(int(rate))
    stim = [1] + [rng.randrange(2) for _ in range(la.SAMPLES)]
    comp = la.compile_analyser(rate)
    got, chip = la.capture(comp, stim, rate)
    assert got == stim[1:]
    assert all(t.LATE == 0 and t.OVR == 0 for t in chip.threads) and chip.lines[0].TAPMISS == 0


def test_logic_analyser_vcd_round_trip(tmp_path):
    rate = 1e6
    stim = [1] + [1 if (k // 3) % 2 == 0 else 0 for k in range(la.SAMPLES)]       # a 6-beat clock
    comp = la.compile_analyser(rate)
    got, _ = la.capture(comp, stim, rate)
    la.write_vcd(got, rate, tmp_path / "c.vcd")
    ch = read_vcd(tmp_path / "c.vcd")
    assert vcd_levels(ch, 1000.0, len(stim)) == stim


def test_logic_analyser_captures_a_uart_byte_and_an_independent_decode_reads_it():
    """The analyser samples at 4x the baud rate; the captured bits are decoded by hand as an 8N1 UART."""
    rate, q, byte = 4 * 115200, 4, 0x5A
    wire = [1] * 6 + [0] + [(byte >> i) & 1 for i in range(8)] + [1] * 4          # idle, start, data LSB first, stop
    stim = [v for bit in wire for v in [bit] * q]                                   # starts with a 1: the trigger
    comp = la.compile_analyser(rate)
    got, _ = la.capture(comp, stim, rate)
    s = [1] + got                                                                   # the trigger beat is a known 1
    i = next(k for k in range(1, len(s)) if s[k - 1] == 1 and s[k] == 0)           # falling edge of the start bit
    centre = lambda b: s[i + q * b + q // 2]                                        # noqa: E731  (bit b, start = 0)
    assert centre(0) == 0 and centre(9) == 1
    assert sum(centre(1 + b) << b for b in range(8)) == byte
