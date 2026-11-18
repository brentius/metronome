"""1-Wire (Maxim AN126 standard speed): reset, presence, Skip ROM, Read Scratchpad with the Maxim CRC-8, at the codec.
The score uses a shared open-drain wire, which scorec compiles only through its I2C-shaped bus template: refused."""
import random

import indep_more as ind
import pytest
from libharness import *
from score import Codec, check, parse

SRC = lib_text("onewire")


def txn_events(spad):
    return [("rst",), ("spad", bytes(spad))]


def test_parses_and_checks():
    assert [str(d) for d in check(parse(SRC)) if d.code.startswith("E-")] == []


def test_crc8_check_value():
    assert ind.crc8_maxim(b"123456789") == 0xA1             # CRC-8/MAXIM-DOW catalogue check value


def test_nominal_timing_reset_presence_and_slots():
    spad = [0x50, 0x05, 0x4B, 0x46, 0x7F, 0xFF, 0x0C, 0x10]            # a DS18B20 power-on scratchpad
    enc = Codec(parse(SRC)).encode_all(txn_events(spad))
    (t,) = ind.onewire_decode(enc.bus["dq"])
    assert t["errors"] == []
    assert 480 <= t["reset_us"] <= 640
    ps, pl = t["presence"]
    assert 15 <= ps <= 60.05 and 60 <= pl <= 240      # the presence pulse starts at the far edge of the window: 60 us
    assert t["bytes"] == [0xCC, 0xBE] + spad + [ind.crc8_maxim(bytes(spad))]
    lows = sorted({round(n * ind.NS / 1000) for lvl, st, n in ind.runs(enc.bus["dq"]) if lvl == 0})
    assert 6 in lows and 60 in lows                                    # write-1 / read initiation 6 us, write-0 60 us


def test_every_scratchpad_byte_value_at_eight_times_speed():
    """All 256 values in the eight scratchpad bytes (32 transactions), the codec running at 8x so the trace stays small;
    the decoder scales its windows back.  Timing windows themselves are checked above at nominal speed."""
    c = Codec(parse(SRC), rate=12_500 * 8)
    rng = random.Random(5)
    vals = list(range(256))
    rng.shuffle(vals)
    ev = []
    for i in range(32):
        ev += txn_events(vals[8 * i:8 * i + 8])
    enc = c.encode_all(ev)
    ts = ind.onewire_decode(enc.bus["dq"], scale=8)
    assert len(ts) == 32 and all(t["errors"] == [] for t in ts)
    assert [t["bytes"][2:10] for t in ts] == [vals[8 * i:8 * i + 8] for i in range(32)]
    assert all(t["bytes"][10] == ind.crc8_maxim(bytes(t["bytes"][2:10])) for t in ts)
    assert sorted(b for t in ts for b in t["bytes"][2:10]) == list(range(256))


def test_codec_decodes_its_own_transaction():
    c = Codec(parse(SRC))
    enc = c.encode_all(txn_events(range(8)))
    r = c.decode("master", enc.bus)
    assert r.ok, r.notes
    assert [e for e in r.events if e[0] in ("skip", "cmd", "spad", "chk")][:3] == [("skip", 0xCC), ("cmd", 0xBE), ("spad", bytes(range(8)))]


def test_a_bad_crc_is_visible_to_the_independent_decoder():
    spad = bytes(range(8))
    good = ind.crc8_maxim(spad)
    enc = Codec(parse(SRC)).encode_all([("rst",), ("spad", spad), ("chk", good ^ 0x40)])
    (t,) = ind.onewire_decode(enc.bus["dq"])
    assert t["bytes"][-1] != ind.crc8_maxim(bytes(t["bytes"][2:10]))


def test_compiler_refuses_the_shared_bus_shape():
    import scorec
    with pytest.raises(scorec.CompileError) as e:
        scorec.compile_score(SRC, "master", "dq=P0/O0")
    assert e.value.code == "E-UNSUPPORTED" and "most significant bit first" in str(e.value)
