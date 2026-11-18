"""WS2812: codec level over all 256 byte values, parse/check pass, compiled sender on the cycle model."""
import random

import indep
import pytest
from libharness import *
from score import Codec, check, parse

SRC = lib_text("ws2812")
LED = lambda f: [(n, f[i + j]) for i in range(0, len(f), 3) for j, n in enumerate("grb")]  # noqa: E731


def frames_256():
    """All 256 byte values over eleven 24-byte frames (the last one padded with 0x00)."""
    allb = bytes(range(256)) + bytes(24 * 11 - 256)
    return [allb[i:i + 24] for i in range(0, len(allb), 24)]


def test_parses_and_checks():
    assert [str(d) for d in check(parse(SRC)) if d.code.startswith("E-")] == []


def test_every_byte_value_codec_vs_independent_decoder():
    sc = parse(SRC)
    c = Codec(sc)
    for f in frames_256():
        enc = c.encode_all(LED(f))
        got, bad = indep.ws2812_decode(enc.bus["din"])
        assert bad == [] and got == [f], (f, bad)
        r = c.decode("led", enc.bus)
        assert r.ok and [e[1] for e in r.events] == list(f)


def test_codec_pulse_widths_are_within_150ns_of_nominal():
    enc = Codec(parse(SRC)).encode_all(LED(bytes([0x00, 0xFF] * 12)))
    s = enc.bus["din"]
    widths = {0: set(), 1: set()}
    for lvl, st, n in indep.runs(s):
        if lvl:
            widths[0 if abs(n * indep.NS - 400) < abs(n * indep.NS - 800) else 1].add(n * indep.NS)
    assert all(abs(w - 400) <= 150 for w in widths[0]) and all(abs(w - 800) <= 150 for w in widths[1])
    assert widths[0] and widths[1]


@pytest.fixture(scope="module")
def compiled():
    import scorec
    return scorec.compile_score(SRC, "sender", "din=O8")


@pytest.mark.parametrize("seed", range(3))
def test_compiled_sender_pulse_widths_on_cycle_model(compiled, seed):
    rng = random.Random(seed)
    f1, f2 = bytes(rng.randrange(256) for _ in range(24)), bytes(rng.randrange(256) for _ in range(24))
    chip, tr = run_sender(compiled, f1 + f2, [8], 2 * (24 * 8 * 75 + 3600 + 600) + 800)
    got, bad = indep.ws2812_decode(tr[8])
    assert bad == [] and got == [f1, f2]
    model_clean(chip)


def test_compiled_sender_all_256_values_on_cycle_model(compiled):
    fr = frames_256()[:11]
    data = b"".join(fr)
    chip, tr = run_sender(compiled, data, [8], 11 * (24 * 8 * 75 + 3600) + 4000)
    got, bad = indep.ws2812_decode(tr[8])
    assert bad == [] and got == fr
    assert b"".join(got)[:256] == bytes(range(256))
    model_clean(chip)
