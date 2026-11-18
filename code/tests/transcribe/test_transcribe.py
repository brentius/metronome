"""Transcription: capture an unknown wire, infer a score, replay it with Metronome.
Evidence level: verified in simulation against the reference codec (model level), not hardware."""
import random
import zlib

import pytest

from harness import IDLE, hostin, new_chip, parse, spec_block, Codec, scorec  # noqa: E402
from score import check  # noqa: E402
from transcribe import InferenceError, search_crc, transcribe  # noqa: E402
from transcribe.infer import classify  # noqa: E402

FS = 60e6


def hidden_text(rate, bits=8, parity=None, stops=1, idle=1):
    start, stop = ("0", "1") if idle else ("1", "0")
    g = [f"  char   = bit({start})", f"           data:u{bits}"]
    if parity:
        g.append(f"           p: parity {parity} over data")
    g += [f"           bit({stop})"] * stops + ["           gap 0 beats"]
    return "\n".join([
        "protocol hidden", "roles    sender, receiver", "",
        f"wire tx out push-pull idle {'high' if idle else 'low'} by sender", "",
        f"clock {rate} Hz", "  sender:   generated", f"  receiver: started by tx {'fall' if idle else 'rise'}",
        "  tolerance 3%", "", "symbols", "  bit(d)   tx \"d\"          sample tx at 50%", "",
        "bits lsb first" + ("" if idle else ", invert"), "", "grammar", "  line   = char*", *g]) + "\n"


def capture(text, data, nominal, err=0.0, jitter=0, seed=0):
    """Reference-codec waveform of `data`, clock error `err`, +-jitter samples on every edge."""
    lv = list(Codec(parse(text), rate=nominal * (1 + err)).encode_all([("data", b) for b in data]).bus["tx"])
    if jitter:
        rng = random.Random(seed)
        edges = [i for i in range(1, len(lv)) if lv[i] != lv[i - 1]]
        new = [e + rng.randint(-jitter, jitter) for e in edges]
        out, cur, prev = [], lv[0], 0
        for e in new + [len(lv)]:
            out += [cur] * (e - prev)
            cur ^= 1
            prev = e
        lv = out[:len(lv)]
    return lv


def rand_bytes(n, bits, seed):
    r = random.Random(seed)
    return [r.randrange(1 << bits) for _ in range(n)]


CASES = [  # rate, bits, parity, stops, idle
    (9600, 8, None, 1, 1), (115200, 8, None, 1, 1), (1_000_000, 8, None, 1, 1),
    (115200, 7, None, 1, 1), (115200, 7, "even", 1, 1), (115200, 8, "odd", 1, 1),
    (115200, 8, None, 2, 1), (115200, 7, None, 2, 1), (115200, 5, None, 1, 1), (115200, 9, None, 1, 1),
    (115200, 8, None, 1, 0), (460800, 8, "even", 2, 0),
]


@pytest.mark.parametrize("case", CASES, ids=lambda c: "%d-%d%s%d-idle%d" % (c[0], c[1], (c[2] or "none")[0].upper(), c[3], c[4]))
@pytest.mark.parametrize("err,jit", [(0.0, 0), (0.015, 2), (-0.015, 2)])
def test_infers_hidden_uart(case, err, jit):
    rate, bits, parity, stops, idle = case
    text = hidden_text(rate, bits, parity, stops, idle)
    data = rand_bytes(24, bits, 7)
    t = transcribe(capture(text, data, rate, err, jit), FS)
    u = t.uart
    assert (u.data_bits, u.parity, u.stop_bits, u.idle_level) == (bits, parity or "none", stops, idle), u
    assert u.words == list(data)
    measured_err = u.baud_measured / (rate * (1 + err)) - 1
    assert abs(measured_err) < 0.005, measured_err      # estimated baud within 0.5% of the true (error-shifted) rate
    assert [d for d in check(parse(t.score)) if str(d.code).startswith("E-")] == []
    if err == 0:
        assert u.baud_standard and u.baud_used == rate
    else:
        assert not u.baud_standard                    # 1.5% off a standard baud: the measured value is used
        assert f"measured {u.baud_measured:.1f}" in t.score


def chip_output(compiled, data, nbits, rate):
    chip = new_chip(compiled)
    pending, trace = list(data), []
    P = FS / rate
    for _ in range(int(len(data) * nbits * P + 4 * P + 3000)):
        if pending and chip.host.INV == 0:
            hostin(chip, pending.pop(0))
        uo, uio, oe = chip.step(IDLE, 0)
        trace.append((uo >> 2) & 1)
    return chip, trace


ROUND_TRIP = [  # the hidden transmitter; the emitted score must reproduce it on the chip model
    (115200, 8, None, 1, 1, 0.015, 2), (1_000_000, 8, None, 1, 1, -0.015, 2), (1_000_000, 8, None, 2, 1, 0.0, 2),
]
# Parity and idle-low + `invert` senders: compiler gaps found by this suite on 2026-11-14 and fixed in scorec/tx.py
# the same day (parity on the LFSR as a width-1 CRC; invert applied to every coded bit). Now full round trips.
ROUND_TRIP += [(1_000_000, 7, "even", 2, 1, 0.0, 2), (460800, 8, None, 1, 0, 0.0, 2), (115200, 8, "odd", 1, 0, 0.01, 2)]
COMPILER_GAPS = []


def replay(score_text, hidden, msg, bits, parity, stops, rate):
    c = scorec.compile_score(score_text, "sender", "tx=O8")
    chip, trace = chip_output(c, msg, 1 + bits + (parity is not None) + stops, rate)
    assert all(th.LATE == 0 and th.OVR == 0 for th in chip.threads)
    return Codec(parse(hidden)).decode("receiver", {"tx": trace})


@pytest.mark.parametrize("rate,bits,parity,stops,idle,err,jit", ROUND_TRIP + COMPILER_GAPS)
def test_round_trip_replay_on_model(rate, bits, parity, stops, idle, err, jit):
    hidden = hidden_text(rate, bits, parity, stops, idle)
    t = transcribe(capture(hidden, rand_bytes(16, bits, 3), rate, err, jit), FS)
    msg = rand_bytes(4, bits, 99)
    r = replay(t.score, hidden, msg, bits, parity, stops, t.uart.baud_used)
    if (rate, bits, parity, stops, idle, err, jit) in ROUND_TRIP:
        assert r.ok, r.notes
        assert [e[1] for e in r.events if e[0] == "data"] == msg
    else:
        base = replay(hidden, hidden, msg, bits, parity, stops, rate)
        assert (r.ok, r.events) == (base.ok, base.events)


def test_spec_uart_example_is_recovered():
    tr = list(Codec(parse(spec_block(0)), rate=115200).encode_all([("data", b) for b in b"Metronome!"]).bus["tx"])
    t = transcribe(tr, FS)
    assert t.uart.baud_used == 115200 and t.uart.data_bits == 8 and t.uart.parity == "none"
    assert bytes(t.uart.words) == b"Metronome!"
    assert "lsb first" in t.uart.bit_order and "ASSUMPTION" in t.score


# ---- CRC -------------------------------------------------------------------------------------------------------
def frames_with(name, n=5, seed=1):
    from score.crc import STD, crc_bytes
    c = STD[name]
    r = random.Random(seed)
    out = []
    for _ in range(n):
        p = bytes(r.randrange(256) for _ in range(r.randrange(6, 40)))
        out.append(p + crc_bytes(c, p).to_bytes(c.width // 8, "big"))
    return out, c


@pytest.mark.parametrize("name", ["crc8_smbus", "crc16_ccitt", "crc16_usb"])
def test_crc_search_recovers_known(name):
    from score.ast import CrcDecl
    from score.crc import crc_bytes
    frames, c = frames_with(name)
    ms = search_crc(frames)
    key = (c.width, c.poly, c.init, c.refin, c.refout, c.xorout)
    assert any((m.width, m.poly, m.init, m.refin, m.refout, m.xorout) == key and m.byteorder == "big" for m in ms)
    for m in ms:                                         # every reported match really reproduces all frames
        W = m.width // 8
        d = CrcDecl("x", m.width, m.poly, m.init, m.refin, m.refout, m.xorout)
        assert all(crc_bytes(d, f[:-W]).to_bytes(W, m.byteorder) == f[-W:] for f in frames)


def test_crc32_ethernet_little_endian_fcs_and_decl_parses():
    r = random.Random(5)
    frames = []
    for _ in range(4):
        p = bytes(r.randrange(256) for _ in range(r.randrange(10, 60)))
        frames.append(p + zlib.crc32(p).to_bytes(4, "little"))
    ms = search_crc(frames, 4)
    eth = [m for m in ms if m.name == "CRC-32/ETHERNET"]
    assert eth and eth[0].byteorder == "little"
    d = eth[0].decl("crc32_eth")
    assert d == "crc crc32_eth width 32 poly 0x04C11DB7 init 0xFFFFFFFF refin refout xorout 0xFFFFFFFF"
    text = hidden_text(115200).replace("bits lsb first", d + "\n\nbits lsb first")   # the parser accepts the declaration
    assert parse(text).crcs["crc32_eth"].poly == 0x04C11DB7


def test_crc_search_requires_distinct_frames_and_rejects_non_crc():
    with pytest.raises(ValueError):
        search_crc([b"abc\x01", b"abc\x01"])
    r = random.Random(0)
    junk = [bytes(r.randrange(256) for _ in range(20)) for _ in range(4)]
    assert search_crc(junk) == []


# ---- Manchester ------------------------------------------------------------------------------------------------
def test_manchester_classified_on_ethernet_trace():
    body = bytes(random.Random(3).randrange(256) for _ in range(40))
    tr = list(Codec(parse(spec_block(3))).encode_all([("body", body)]).bus["td"])
    c = classify(tr, FS)
    assert c.kind == "manchester", c.evidence
    assert abs(c.bit_rate / 10e6 - 1) < 0.005, c.bit_rate
    t = transcribe(tr, FS)
    assert t.uart is None and t.score is None and t.classification.kind == "manchester"


def test_uart_is_not_manchester():
    tr = capture(hidden_text(115200), rand_bytes(24, 8, 1), 115200)
    assert classify(tr, FS).kind == "nrz"


# ---- negatives -------------------------------------------------------------------------------------------------
def test_no_edges_is_a_clear_error():
    with pytest.raises(InferenceError, match="no usable activity"):
        transcribe([1] * 5000, FS)


def test_garbage_is_a_clear_error():
    r = random.Random(1)
    with pytest.raises(InferenceError):
        transcribe([r.randrange(2) for _ in range(20000)], FS)
    lv, cur = [], 0
    for _ in range(300):                                  # random run lengths, no common bit time
        lv += [cur] * r.randrange(5, 400)
        cur ^= 1
    with pytest.raises(InferenceError):
        transcribe(lv, FS)


def test_short_trace_is_an_error():
    with pytest.raises(InferenceError):
        transcribe([0, 1, 0], FS)
