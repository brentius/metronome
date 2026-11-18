"""ARM SWD: request parity, ACK (OK / WAIT / FAULT), both turnarounds and the data parity, at the codec level against an
independent ADIv5 packet decoder; every byte value in the data word; scorec refuses the shared bus."""
import random

import indep_more as ind
import pytest
from libharness import *
from score import Codec, check, parse

SRC = lib_text("swd")
OK, WAIT, FAULT = 1, 2, 4


def events(apndp, rnw, a, ack, data=0):
    ev = [("apndp", apndp), ("rnw", rnw), ("a", a), ("ack", ack)]
    return ev + ([("d", data)] if ack == OK else [])


def test_parses_and_checks():
    assert [str(d) for d in check(parse(SRC)) if d.code.startswith("E-")] == []


def test_all_request_headers_and_acks():
    c = Codec(parse(SRC))
    want, ev = [], []
    for apndp in (0, 1):
        for rnw in (0, 1):
            for a in range(4):
                for ack in (OK, WAIT, FAULT):
                    d = (0xA5A5_0000 | (apndp << 9) | (rnw << 8) | (a << 4) | ack) & 0xFFFFFFFF
                    ev += events(apndp, rnw, a, ack, d)
                    want.append((apndp, rnw, a, {OK: "OK", WAIT: "WAIT", FAULT: "FAULT"}[ack], d if ack == OK else None))
    enc = c.encode_all(ev)
    got = ind.swd_decode(enc.bus["swclk"], enc.bus["swdio"])
    assert len(got) == len(want) == 48
    assert all(t["errors"] == [] for t in got)
    assert [(t["apndp"], t["rnw"], t["a"], t["ack"], t.get("data")) for t in got] == want


def test_every_byte_value_in_every_data_position():
    c = Codec(parse(SRC))
    rng = random.Random(3)
    ev, want = [], []
    for v in range(256):
        for rnw in (0, 1):
            d = (v | ((v ^ 0xFF) << 8) | (v << 16) | (((v * 5) & 255) << 24)) if rnw else (rng.getrandbits(24) << 8 | v)
            ev += events(1, rnw, v & 3, OK, d)
            want.append((rnw, d))
    enc = c.encode_all(ev)
    got = ind.swd_decode(enc.bus["swclk"], enc.bus["swdio"])
    assert len(got) == 512 and all(t["errors"] == [] for t in got)
    assert [(t["rnw"], t["data"]) for t in got] == want
    for pos in range(4):
        assert {(t["data"] >> (8 * pos)) & 255 for t in got if t["rnw"] == 1} == set(range(256))


def test_both_turnaround_clocks_are_clocked_and_never_driven_to_zero():
    """A turnaround is a full SWCLK cycle in which neither side drives SWDIO low (the shared wire floats high); the
    host and the target never both drive a value in the same beat."""
    c = Codec(parse(SRC))
    for rnw, ta2 in ((1, 8 + 1 + 3 + 33), (0, 8 + 1 + 3)):
        enc = c.encode_all(events(0, rnw, 2, OK, 0x12345678))
        host, target = enc.drives["host"]["swdio"], enc.drives["target"]["swdio"]
        rises = [i for i in range(1, enc.bus.n) if enc.bus["swclk"][i] and not enc.bus["swclk"][i - 1]]
        assert len(rises) == 46
        assert [i for i in rises if host[i] is not None and target[i] is not None] == []
        for k in (8, ta2):
            assert host[rises[k]] != 0 and target[rises[k]] != 0 and enc.bus["swdio"][rises[k]] == 1


def test_codec_decodes_read_and_write():
    c = Codec(parse(SRC))
    for rnw in (0, 1):
        enc = c.encode_all(events(0, rnw, 1, OK, 0xDEADBEEF))
        r = c.decode("target", enc.bus)
        assert r.ok, r.notes
        assert ("d", 0xDEADBEEF) in r.events and ("ack", 1) in r.events


def test_wrong_data_parity_is_seen_by_the_independent_decoder():
    enc = Codec(parse(SRC)).encode_all(events(0, 1, 0, OK, 0x1))
    rises = [i for i in range(1, enc.bus.n) if enc.bus["swclk"][i] and not enc.bus["swclk"][i - 1]]
    sd = list(enc.bus["swdio"])
    r = rises[8 + 1 + 3 + 32]                              # the data parity beat of a read
    for j in range(r - 30, r + 30):
        sd[j] ^= 1
    (t,) = ind.swd_decode(enc.bus["swclk"], sd)
    assert t["errors"] == ["data parity"] and t["data"] == 1


def test_compiler_refuses_parity_on_the_bus_template():
    import scorec
    with pytest.raises(scorec.CompileError) as e:
        scorec.compile_score(SRC, "host", "swclk=O8 swdio=P0/O0")
    assert e.value.code == "E-UNSUPPORTED" and "parity" in str(e.value)
