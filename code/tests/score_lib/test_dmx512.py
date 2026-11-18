"""DMX512-A: codec level over all 256 slot values, and the compiled sender on the cycle model, both read by dmx_decode
(written from ANSI E1.11, independent of the score codec)."""
import indep_more as ind
import pytest
from libharness import *
from score import Codec, check, parse

SRC = lib_text("dmx512")
PKT = 25 * 240 + 3 * 240 + 5 * 11 * 240                      # cycles in one 4-slot packet (brk + mab + 5 slots)


def test_parses_and_checks():
    assert [str(d) for d in check(parse(SRC)) if d.code.startswith("E-")] == []


def test_every_slot_value_codec_vs_independent_decoder():
    c = Codec(parse(SRC))
    vals = [(4 * i + k) & 255 for i in range(64) for k in range(4)]          # all 256 values, 64 packets of 4 slots
    events = []
    for i in range(64):
        events += [("brk",)] + [("ch", vals[4 * i + k]) for k in range(4)]
    enc = c.encode_all(events)
    pk = ind.dmx_decode(enc.bus["dmx"])
    assert len(pk) == 64 and all(p["errors"] == [] for p in pk)
    assert [p["slots"] for p in pk] == [[0] + vals[4 * i:4 * i + 4] for i in range(64)]
    assert sorted(v for p in pk for v in p["slots"][1:]) == list(range(256))
    assert min(p["brk_us"] for p in pk) >= 92 and min(p["mab_us"] for p in pk) >= 12


def test_codec_decodes_its_own_packet():
    c = Codec(parse(SRC))
    enc = c.encode_all([("brk",), ("ch", 1), ("ch", 2), ("ch", 255), ("ch", 0)])
    r = c.decode("fixture", enc.bus)
    assert r.ok and [e for e in r.events if e[0] == "ch"] == [("ch", 1), ("ch", 2), ("ch", 255), ("ch", 0)]


@pytest.mark.parametrize("data", [bytes([0x00, 0xFF, 0x55, 0xAA, 0x01, 0x80, 0x7F, 0xFE]), bytes(range(8))])
def test_compiled_sender_on_cycle_model(data):
    import scorec
    c = scorec.compile_score(SRC, "sender", "dmx=O8")
    chip, tr = run_sender(c, data, [8], 2 * PKT + 3000)
    pk = ind.dmx_decode(tr[8])
    assert len(pk) >= 2 and all(p["errors"] == [] for p in pk[:2])
    assert [p["slots"] for p in pk[:2]] == [[0] + list(data[:4]), [0] + list(data[4:])]
    assert all(92 <= p["brk_us"] <= 110 and 12 <= p["mab_us"] <= 16 for p in pk[:2])
    model_clean(chip)


def test_compiler_symbol_repeat_count_x3():
    """Regression for the scorec repeat bug (fixed 2026-11-16: `X x N` shared Step objects that merge_syms mutated)."""
    import scorec
    text = SRC.replace("mab mab mab", "mab x 3")
    assert "mab x3" in scorec.compile_score(text, "sender", "dmx=O8").mas
