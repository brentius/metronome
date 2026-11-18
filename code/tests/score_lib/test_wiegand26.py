"""Wiegand 26: nominal timing at the codec, every facility code 0..255 and every card-number byte at a faster clock, the
compiled sender at 4 kHz (250 us interval, 25 us pulses: inside the standard's windows) on the cycle model."""
import os

import indep_more as ind
import pytest
from libharness import *
from score import Codec, check, parse

SRC = lib_text("wiegand26")
FAST = SRC.replace("clock 500 Hz", "clock 1 MHz").replace("split 2.5%", "split 10%")     # 60-cycle beats: tests only
STD4K = SRC.replace("clock 500 Hz", "clock 4 kHz").replace("split 2.5%", "split 10%")      # 250 us interval, 25 us pulse


def events(fc, card):
    return [("pe", ind.wiegand26_pe(fc, card)), ("fc", fc), ("card_a", card >> 12), ("card_b", (card >> 4) & 255), ("card_c", card & 15)]


def test_parses_and_checks():
    assert [str(d) for d in check(parse(SRC)) if d.code.startswith("E-")] == []


def test_nominal_timing_in_the_codec():
    enc = Codec(parse(SRC)).encode_all(events(0x5A, 0xBEEF))
    bits, bad = ind.wiegand_decode(enc.bus["d0"], enc.bus["d1"])
    assert bad == [] and len(bits) == 26
    fc, card, e_ok, o_ok = ind.wiegand26_fields(bits)
    assert (fc, card, e_ok, o_ok) == (0x5A, 0xBEEF, True, True)
    pulses = [n * ind.NS / 1000 for lvl, st, n in ind.runs(enc.bus["d0"]) if lvl == 0]
    assert all(abs(p - 50) < 0.1 for p in pulses)


def test_every_facility_code_and_card_byte_codec_vs_decoder():
    c = Codec(parse(FAST))
    ev, want = [], []
    for v in range(256):
        card = (v << 8) | (255 - v)                    # every value appears as the card's high byte and low byte
        ev += events(v, card)
        want.append((v, card))
    enc = c.encode_all(ev)
    bits, bad = ind.wiegand_decode(enc.bus["d0"], enc.bus["d1"], pulse_us=(0, 1e9), interval_us=(0, 1e9))
    assert len(bits) == 26 * 256
    got = [ind.wiegand26_fields(bits[26 * i:26 * i + 26]) for i in range(256)]
    assert [(g[0], g[1]) for g in got] == want
    assert all(g[2] and g[3] for g in got)             # both parities right, from the score's own odd-parity field


def compiled_frame(text, rate, cyc):
    import scorec
    fc, card = 0xA5, 0x3C96
    c = scorec.compile_score(text, "reader", "d0=O8 d1=O9", rate_hz=rate)
    # one host byte per field (widths 1, 8, 4, 8 and 4 bits); the frame starts three beats after the go byte
    chip, tr = run_sender(c, [ev[1] for ev in events(fc, card)], [8, 9], 31 * cyc)
    model_clean(chip)
    return fc, card, tr


def test_compiled_sender_on_cycle_model_fast_clock():
    """20 kHz (3000-cycle beats, 10 % pulses = 5 us): the bits, both parities and the pulse fraction; the standard's
    absolute windows are checked at the nominal rate by the slow test and the codec test above."""
    fc, card, tr = compiled_frame(SRC.replace("clock 500 Hz", "clock 20 kHz").replace("split 2.5%", "split 10%"), 20000, 3000)
    bits, bad = ind.wiegand_decode(tr[8], tr[9], pulse_us=(0, 1e9), interval_us=(0, 1e9))
    assert len(bits) == 26 and ind.wiegand26_fields(bits) == (fc, card, True, True)
    assert {n for w in (8, 9) for lvl, st, n in ind.runs(tr[w]) if lvl == 0} == {300}      # 10 % of 3000 cycles


@pytest.mark.skipif(not os.environ.get("SCORE_LIB_SLOW"), reason="75 s: set SCORE_LIB_SLOW=1")
def test_compiled_sender_at_standard_windows_on_cycle_model():
    fc, card, tr = compiled_frame(STD4K, 4000, 15000)
    bits, bad = ind.wiegand_decode(tr[8], tr[9])
    assert bad == [] and len(bits) == 26
    assert ind.wiegand26_fields(bits) == (fc, card, True, True)
