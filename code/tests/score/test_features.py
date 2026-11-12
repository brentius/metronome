"""Coding, field and grammar features on small synthetic scores, with independent bit-level models."""
import random

import pytest
from score import Codec, check, parse
from score.codec import EncodeError

LEAD = 8
BEAT = 60       # 1 MHz beat at 60 MHz


def mk(grammar, bits="msb first", extra="", symbols=""):
    return f"""protocol t
roles a, b
wire w out push-pull idle low by a
clock 1 MHz
  a: generated
  b: generated
symbols
  bit(d) w "d"
  sof    w "1"
  eof    w "0"
{symbols}
bits {bits}
{extra}
grammar
  frame = {grammar}
"""


def line_bits(bus, nbeats):
    return [bus["w"][LEAD + BEAT * k + BEAT // 2] for k in range(nbeats)]


def bits_of(data, order="msb"):
    out = []
    for byte in data:
        out += [(byte >> (7 - i)) & 1 for i in range(8)] if order == "msb" else [(byte >> i) & 1 for i in range(8)]
    return out


def rt(src, events, role="b", **kw):
    sc = parse(src)
    assert [str(d) for d in check(sc) if d.code.startswith("E-")] == []
    c = Codec(sc, **kw)
    enc = c.encode_all(events)
    r = c.decode(role, enc.bus)
    return c, enc, r


def ref_stuff(bits, n, kind, value):
    """Independent lazy stuffing model: after n counted equal bits insert `value` (None = complement)."""
    out, runv, runn = [], None, 0
    for b in bits:
        if runn >= n and runv is not None:
            out.append((1 - runv) if value is None else value)
            runv, runn = None, 0
        out.append(b)
        counts = kind == "equal" or (kind == "ones" and b == 1) or (kind == "zeros" and b == 0)
        if not counts:
            runv, runn = None, 0
        elif b == runv:
            runn += 1
        else:
            runv, runn = b, 1
    return out


@pytest.mark.parametrize("spec,n,kind,val", [("stuff 0 after 5 ones", 5, "ones", 0),
                                              ("stuff after 3 equal", 3, "equal", None),
                                              ("stuff 1 after 4 zeros", 4, "zeros", 1)])
@pytest.mark.parametrize("seed", range(6))
def test_stuffing_matches_independent_model(spec, n, kind, val, seed):
    rng = random.Random(seed)
    data = bytes(rng.choice([0x00, 0xFF, 0xF8, 0x1F, rng.randrange(256)]) for _ in range(rng.randrange(1, 7)))
    src = mk("sof n:u8 = %d p:bytes[n] eof" % len(data), f"msb first, {spec}")
    c, enc, r = rt(src, [("p", data)])
    assert r.ok, r.notes
    assert [e for e in r.events if e[0] == "p"] == [("p", data)]
    beats = [p for p in enc.plan if p.kind == "beat"]
    bits = line_bits(enc.bus, len(beats))
    # beats: sof, then n and the payload (stuffing runs across the two fields), then eof
    assert bits[0] == 1 and bits[-1] == 0
    assert bits[1:-1] == ref_stuff(bits_of([len(data)]) + bits_of(data), n, kind, val)


def test_differential_matches_independent_nrzi():
    rng = random.Random(3)
    for dv in (0, 1):
        data = bytes(rng.randrange(256) for _ in range(5))
        src = mk("sof p:bytes[5] eof", f"msb first, differential on {dv}")
        c, enc, r = rt(src, [("p", data)])
        assert r.ok and r.events[1] == ("p", data)
        beats = [p for p in enc.plan if p.kind == "beat"]
        lb = line_bits(enc.bus, len(beats))[1:-1]
        prev, exp = 1, []                      # reference after `sof` (which ends high)
        for d in bits_of(data):
            prev = prev ^ (1 if d == dv else 0)
            exp.append(prev)
        assert lb == exp


def test_invert_and_lsb_first():
    data = bytes([0xA5, 0x0F])
    src = mk("sof p:bytes[2] eof", "lsb first, invert")
    c, enc, r = rt(src, [("p", data)])
    assert r.ok
    beats = [p for p in enc.plan if p.kind == "beat"]
    lb = line_bits(enc.bus, len(beats))[1:-1]
    assert lb == [1 - b for b in bits_of(data, "lsb")]


def test_field_order_override_and_widths():
    src = mk("sof a:u16 lsb first b:u12 c:s8 eof", "msb first")
    c, enc, r = rt(src, [("a", 0x1234), ("b", 0xABC), ("c", -100)])
    assert r.ok and r.events == [("sof",), ("a", 0x1234), ("b", 0xABC), ("c", -100), ("eof",)]
    beats = [p for p in enc.plan if p.kind == "beat"]
    lb = line_bits(enc.bus, len(beats))[1:17]
    assert lb == [(0x1234 >> i) & 1 for i in range(16)]            # lsb first override
    with pytest.raises(EncodeError):
        c.encode_all([("a", 70000), ("b", 0), ("c", 0)])


def test_parity_and_crc_custom():
    src = mk("sof p:bytes[3] q: parity even over p..p  k:crc c16 over p..p  eof", "lsb first",
             extra="crc c16 width 16 poly 0x1021 init 0xFFFF refin refout xorout 0x0000")
    c, enc, r = rt(src, [("p", b"\x01\x02\x03")])
    assert r.ok, r.notes
    ev = dict((e[0], e[1] if len(e) > 1 else None) for e in r.events)
    assert ev["q"] == 0                                           # 0x01,0x02,0x03 have four ones: even
    from score.ast import CrcDecl
    from score.crc import crc_bytes
    assert ev["k"] == crc_bytes(CrcDecl("x", 16, 0x1021, 0xFFFF, True, True, 0), b"\x01\x02\x03")
    c2 = Codec(parse(src))
    bad = c2.encode_all([("p", b"\x01\x02\x03"), ("q", 1)])
    r2 = c2.decode("b", bad.bus)
    assert not r2.ok and any("parity" in n for n in r2.notes)


def test_switch_loops_and_counts():
    src = mk("sof kind:u2 switch kind { 0: a:u8  1: b:u16  else: c:u4 } cnt:u3 items:bytes[cnt] "
             "{ x:u8 } until x == 0  eof")
    for kind, ev in ((0, ("a", 9)), (1, ("b", 0x1FF)), (3, ("c", 5))):
        events = [("kind", kind), ev, ("cnt", 2), ("items", b"\xde\xad"), ("x", 3), ("x", 9), ("x", 0)]
        c, enc, r = rt(src, events)
        assert r.ok, r.notes
        assert [e for e in r.events if e[0] not in ("sof", "eof")] == events


def test_choice_by_symbol_lookahead_and_symbol_until():
    src = """protocol t
roles a, b
wire w out push-pull idle low by a
clock 1 MHz
  a: generated
  b: generated
  split 33% 66%
symbols
  bit(d) w "ddd"  sample w at 50%
  sof    w "111"
  alt1   w "110"
  alt2   w "011"
  eof    w "010"
bits msb first
grammar
  frame = sof (alt1 x:u8 | alt2 y:u8) body:bytes until eof eof
"""
    for first, ev in (("alt1", ("x", 7)), ("alt2", ("y", 8))):
        events = [("sof",), (first,), ev, ("body", b"\x01\x02\x80"), ("eof",)]
        c, enc, r = rt(src, events)
        assert r.ok, r.notes
        assert r.events == events


def test_expect_mismatch_and_turnaround_and_params():
    src = mk("sof magic:u8 expect 0xA5 t:u8 = k + 1 turnaround 2 beats z:bit eof",
             extra="param\n  k : u8 = 7")
    c, enc, r = rt(src, [("magic", 0xA5), ("z", 1)])
    assert r.ok and ("t", 8) in r.events
    c2 = Codec(parse(src), params={"k": 20})
    enc2 = c2.encode_all([("magic", 0x00), ("z", 0)])
    r2 = c2.decode("b", enc2.bus)
    assert not r2.ok and any("mismatch" in n for n in r2.notes) and ("t", 21) in r2.events


def test_wave_strings_hold_complement_and_release():
    src = """protocol t
roles a, b
wire w shared open-drain idle high
wire v out push-pull idle low by a
mirror vn = !v
clock 1 MHz
  a: generated
  b: generated
  split 25% 50% 75%
symbols
  s(d)  w "d.z1"  v "!d.d."
  t     w "0000"  v "xx1x"
grammar
  f = s(1) s(0) t
"""
    sc = parse(src)
    assert [str(x) for x in check(sc) if x.code.startswith("E-")] == []
    c = Codec(sc)
    enc = c.encode_all([])
    a = enc.drives["a"]
    seg = lambda wv, beat, j: wv[LEAD + int((beat + [0, .25, .5, .75][j]) * BEAT) + 1]   # noqa: E731
    # w is open drain: '1' and 'z' release; s(1): "1.z1" -> release, hold, release, release
    assert [seg(a["w"], 0, j) for j in range(4)] == [None, None, None, None]
    # s(0): "0.z1" -> drive 0, hold 0, release, release
    assert [seg(a["w"], 1, j) for j in range(4)] == [0, 0, None, None]
    # v "!d.d." with d=1: !d hold d hold -> 0 0 1 1; d=0: 1 1 0 0; t "xx1x" holds the previous level
    assert [seg(a["v"], 0, j) for j in range(4)] == [0, 0, 1, 1]
    assert [seg(a["v"], 1, j) for j in range(4)] == [1, 1, 0, 0]
    assert [seg(a["v"], 2, j) for j in range(4)] == [0, 0, 1, 1]
    assert all(x + y == 1 for x, y in zip(enc.bus["v"], enc.bus["vn"]))


def test_two_frames_with_gap_and_noise_free_idle():
    src = mk("{ sof n:u8 p:bytes[n] eof gap 3 beats }*")
    events = [("sof",), ("n", 2), ("p", b"\x11\x22"), ("eof",), ("sof",), ("n", 1), ("p", b"\xf0"), ("eof",)]
    c, enc, r = rt(src, events)
    assert r.ok and r.events == events


def test_parse_only_constructs_and_groups():
    src = """protocol t version 2
roles a, b
use std
wire w shared open-drain idle high
wire v out push-pull idle low by a
clock 1 MHz
  a: generated, stretch on w
  b: follow w fall, capture on w rise
symbols
  bit(d) w "d"
  go     v "1"
recognise
  quiet   no edge on w for 2 beats
  lo      w low for > 5 us
  rise_ev w rises
arbitrate w
grammar
  f = go every 16 ms: go
      retry 3 { x:u8 asm { beats 4
                           reads x
                           ; body
                         } model { def m(x): return x } } on quiet
      y:u8 by b asm { beats dynamic }
      sw:crc crc16_usb over x..x
abort
  on quiet in f -> idle
param
  p : u8 = 3 for a
"""
    sc = parse(src)
    assert sc.version == 2 and sc.arbitrates == ["w"]
    retry = [n for n in sc.prods[0].body.items if type(n).__name__ == "Retry"][0]
    assert retry.count == 3 and retry.event == "quiet"
    fld = retry.node
    assert fld.asm is not None and "beats 4" in fld.asm and fld.model.strip().startswith("def m")
    ds = [d for d in check(sc) if d.code.startswith("E-")]
    assert ds == [], [str(d) for d in ds]
    g = parse("""protocol g
roles a, b
group tx_side:
  wire tx out push-pull idle high by a
  clock 115200 Hz
    a: generated
    b: started by tx fall
group rx_side:
  wire rx out push-pull idle high by b
  clock 115200 Hz
    b: generated
    a: started by rx fall
symbols
  bit(d)  tx "d"  sample tx at 50%
  rbit(d) rx "d"  sample rx at 50%
grammar
  f = x:u8
""")
    assert len(g.groups) == 2
