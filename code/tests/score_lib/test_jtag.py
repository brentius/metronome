"""JTAG data-register scan (partial score): the TAP state path and the shifted bits at the codec level, against an
independent IEEE 1149.1 TAP-controller model; scorec refusals recorded."""
import indep_more as ind
import pytest
from libharness import *
from score import Codec, check, parse

SRC = lib_text("jtag")
PATH = ["TLR", "RTI", "SelDR", "CapDR", "ShDR"]


def scan_events(tdi, tdo):
    return [("treset",), ("tdi", tdi), ("tdo", tdo)]


def test_parses_and_checks():
    assert [str(d) for d in check(parse(SRC)) if d.code.startswith("E-")] == []


def test_every_byte_value_through_the_tap_model():
    c = Codec(parse(SRC))
    ev, want = [], []
    for v in range(256):
        tdi, tdo = v, v ^ 0xA5
        ev += scan_events(tdi, tdo)
        want.append((tdi, tdo))
    enc = c.encode_all(ev)
    b = enc.bus
    scans = ind.jtag_decode(b["tck"], b["tms"], b["tdi"], b["tdo"])
    assert len(scans) == 256
    for s, (tdi, tdo) in zip(scans, want):
        assert len(s["tdi"]) == 9 and s["tdi"][8] == 0                       # 8 field bits + the exit clock's pad bit
        assert sum(bit << i for i, bit in enumerate(s["tdi"][:8])) == tdi
        assert sum(bit << i for i, bit in enumerate(s["tdo"][:8])) == tdo
        # Capture-DR, Shift-DR entered then eight shifts with TMS=0 (the ninth shift is the TMS=1 clock), Exit1-DR, Update-DR, Run-Test/Idle
        assert s["path"] == ["CapDR"] + ["ShDR"] * 9 + ["Ex1DR", "UpdDR", "RTI"]
    assert {v for v, _ in want} == set(range(256)) and {w for _, w in want} == set(range(256))


def test_tap_is_reset_by_five_tms_ones_from_any_state():
    """The independent TAP model: five TMS=1 clocks reach Test-Logic-Reset from each of the sixteen states."""
    for s0 in ind.TAP:
        s = s0
        for _ in range(5):
            s = ind.TAP[s][1]
        assert s == "TLR"


def test_codec_decodes_its_scan():
    c = Codec(parse(SRC))
    enc = c.encode_all(scan_events(0x5A, 0xC3))
    r = c.decode("device", enc.bus)
    assert r.ok, r.notes
    assert [e for e in r.events if e[0] in ("tdi", "tdo")] == [("tdi", 0x5A), ("tdo", 0xC3)]


def test_compiler_refusals_are_recorded():
    import scorec
    with pytest.raises(scorec.CompileError) as e:
        scorec.compile_score(SRC, "probe", "tck=O8 tms=O9 tdi=O10 tdo=P0")
    assert e.value.code == "E-UNSUPPORTED" and "dup" in str(e.value)
    with pytest.raises(scorec.CompileError) as e:
        scorec.compile_score(SRC, "device", "tck=P1 tms=P2 tdi=P3 tdo=O8", follow_period=240)
    assert e.value.code == "E-UNSUPPORTED" and "follower template" in str(e.value)
