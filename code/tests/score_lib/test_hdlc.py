"""HDLC: codec level (flags, zero insertion, FCS-16) over every byte value, read by an independent flag/unstuff/FCS
decoder; the compiled sender on the cycle model, which exposes two scorec gaps (stuffing ignored by the sender template)."""
import indep_more as ind
import pytest
from libharness import *
from score import Codec, check, parse

SRC = lib_text("hdlc")


def frame_events(addr, ctrl, info, fcs=None):
    ev = [("addr", addr), ("ctrl", ctrl), ("info", bytes(info))]
    return ev + ([("fcs", fcs)] if fcs is not None else [])


def test_parses_and_checks():
    assert [str(d) for d in check(parse(SRC)) if d.code.startswith("E-")] == []


def test_x25_check_value():
    assert ind.crc16_x25(b"123456789") == 0x906E            # CRC-16/X-25 catalogue check value


def test_every_byte_value_codec_vs_independent_decoder():
    """All 256 values in addr, ctrl and every info byte.  The independent encoder gives the ISO 13239 bit stream of each
    frame.  The codec matches it exactly, except for frames whose last five data bits are ones: there the standard
    inserts a zero before the closing flag and the codec (lazy stuffing, spec 6) does not (gap G6)."""
    c = Codec(parse(SRC))
    ev, payloads = [], []
    for v in range(256):
        p = bytes([v, v ^ 0xFF, v, v ^ 0x55, (v * 7) & 255, (v + 13) & 255])
        ev += frame_events(p[0], p[1], p[2:])
        payloads.append(p)
    enc = c.encode_all(ev)
    got = ind.hdlc_bits(enc.bus["clk"], enc.bus["d"])
    exact, lazy, short = [], [], []
    for p in payloads:
        std, lz = ind.hdlc_encode(p), ind.hdlc_encode(p, stuff_tail=False)
        exact += std
        lazy += lz
        short.append(std != lz)
    assert any(short) and not all(short)
    assert got == lazy                                  # what the codec does
    nonconforming = [p for p, s in zip(payloads, short) if s]
    frames, errors = ind.hdlc_decode(got)
    ok = [f for f, good in frames if good]
    assert {b for p in payloads for b in p} == set(range(256))
    # every conforming frame is read back intact by the independent decoder
    assert all(p in ok for p, s in zip(payloads, short) if not s)
    assert len(nonconforming) >= 1 and errors                # the decoder does notice the missing zero


def test_stuffing_really_happens_and_the_flag_is_not_stuffed():
    """All-ones payload: the wire must carry a zero after every five ones inside the frame and exactly six ones in a flag."""
    c = Codec(parse(SRC))
    enc = c.encode_all(frame_events(0xFF, 0xFF, b"\xff\xff\xff\xff"))
    bits = ind.hdlc_bits(enc.bus["clk"], enc.bus["d"])
    s = "".join(map(str, bits))
    assert s.startswith("01111110") and s.endswith("01111110")
    inner = s[8:-8]
    assert "111111" not in inner and len(inner) > 8 * 8
    frames, errors = ind.hdlc_decode(bits)
    assert errors == [] and frames[0][0] == b"\xff" * 6 and frames[0][1]


def test_codec_decodes_its_own_frame():
    c = Codec(parse(SRC))
    enc = c.encode_all(frame_events(0x03, 0x3F, b"\x7e\x7e\x7e\x7e"))     # payload full of flag look-alikes
    r = c.decode("receiver", enc.bus)
    assert r.ok, r.notes
    assert [e for e in r.events if e[0] in ("addr", "ctrl", "info")] == [("addr", 3), ("ctrl", 0x3F), ("info", b"\x7e" * 4)]
    frames, errors = ind.hdlc_decode(ind.hdlc_bits(enc.bus["clk"], enc.bus["d"]))
    assert errors == [] and frames[0][1] and frames[0][0] == b"\x03\x3f" + b"\x7e" * 4


@pytest.mark.xfail(strict=True, reason="score-language gap G6: stuffing is lazy (spec 6), so no 0 is inserted when the data "
                                       "ends in five 1s and the closing flag follows; ISO 13239 requires it")
def test_data_ending_in_five_ones_is_stuffed_before_the_closing_flag():
    # FCS 0xF800 (given, fault-injection style): its last-sent bits (MSB of the high byte, LSB first) are 11111
    enc = Codec(parse(SRC)).encode_all(frame_events(0x01, 0x02, b"\x00\x00\x00\x00", fcs=0xF800))
    frames, errors = ind.hdlc_decode(ind.hdlc_bits(enc.bus["clk"], enc.bus["d"]))
    assert errors == [] and len(frames) == 1 and frames[0][0] == bytes([1, 2, 0, 0, 0, 0])


def test_compiled_sender_refuses_stuffing():
    """scorec refuses `stuff` with E-UNSUPPORTED (2026-11-16) instead of silently sending unstuffed NRZ. Before the
    refusal, the compiled sender's flags, bit order and FCS matched the independent decoder for payloads with no run of
    five ones; stuffing itself has never been compiled."""
    import scorec
    with pytest.raises(scorec.CompileError) as e:
        scorec.compile_score(SRC, "sender", "clk=O8 d=O9")
    assert e.value.code == "E-UNSUPPORTED" and "stuff" in str(e.value)
