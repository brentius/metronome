"""Coding-layer features in the sender: `parity` fields (computed on the LFSR as a width-1 CRC) and `bits ..., invert`
(SPEC A 6), checked against the reference codec. Receivers refuse both with E-UNSUPPORTED instead of misbehaving.
Both gaps were found by the transcription round trip (code/tests/transcribe) on 2026-11-14."""
import random

import pytest
from harness import *
from scorec.plan import CompileError


def uart_text(bits=8, parity=None, idle=1, stops=1, order="lsb"):
    start, stop = ("0", "1") if idle else ("1", "0")
    g = [f"  char   = bit({start})", f"           data:u{bits}"]
    if parity:
        g.append(f"           p: parity {parity} over data")
    g += [f"           bit({stop})"] * stops + ["           gap 0 beats"]
    return "\n".join([
        "protocol u", "roles    sender, receiver", "",
        f"wire tx out push-pull idle {'high' if idle else 'low'} by sender", "",
        "clock 1 MHz", "  sender:   generated", f"  receiver: started by tx {'fall' if idle else 'rise'}",
        "  tolerance 3%", "", "symbols", '  bit(d)   tx "d"          sample tx at 50%', "",
        f"bits {order} first" + ("" if idle else ", invert"), "", "grammar", "  line   = char*", *g]) + "\n"


def send(text, data, bits):
    c = scorec.compile_score(text, "sender", "tx=O8")
    chip = new_chip(c)
    pending, tr = list(data), []
    for _ in range(int((len(data) * (bits + 4) + 4) * 60)):
        if pending and chip.host.INV == 0:
            hostin(chip, pending.pop(0))
        tr.append((chip.step(IDLE, 0)[0] >> 2) & 1)
    assert all(t.LATE == 0 and t.OVR == 0 for t in chip.threads)
    return tr


CASES = [(8, "even", 1, "lsb"), (8, "odd", 1, "lsb"), (7, "even", 1, "msb"), (8, None, 0, "lsb"),
         (8, "even", 0, "lsb"), (5, "odd", 0, "msb")]


@pytest.mark.parametrize("bits,parity,idle,order", CASES)
def test_sender_coding_matches_codec(bits, parity, idle, order):
    text = uart_text(bits, parity, idle, order=order)
    rng = random.Random(bits * 7 + idle)
    data = [rng.randrange(1 << bits) for _ in range(6)] + [0, (1 << bits) - 1]
    tr = send(text, data, bits)
    r = Codec(parse(text)).decode("receiver", {"tx": tr})
    assert r.ok, r.notes
    assert [e[1] for e in r.events if e[0] == "data"] == data
    if parity:                                          # the parity bit really is on the wire
        assert [e[1] for e in r.events if e[0] == "p"] == [
            (bin(d).count("1") + (parity == "odd")) & 1 for d in data]


def test_wrong_parity_is_caught_by_the_codec():
    text = uart_text(8, "even")
    tr = send(text.replace("parity even", "parity odd"), [0x35, 0x80], 8)
    assert not Codec(parse(text)).decode("receiver", {"tx": tr}).ok


@pytest.mark.parametrize("parity,idle", [("even", 1), (None, 0)])
def test_receiver_refuses_parity_and_invert(parity, idle):
    with pytest.raises(CompileError) as e:
        scorec.compile_score(uart_text(8, parity, idle), "receiver", "tx=P5")
    assert e.value.code == "E-UNSUPPORTED"


@pytest.mark.parametrize("bits,order", [(7, "msb"), (5, "msb"), (7, "lsb")])
def test_receiver_narrow_fields(bits, order):
    text = uart_text(bits, None, 1, order=order)
    data = [0x15 & ((1 << bits) - 1), 1, (1 << bits) - 1, 0]
    enc = Codec(parse(text)).encode_all([("data", d) for d in data])
    chip = new_chip(scorec.compile_score(text, "receiver", "tx=P5"))
    for _ in range(40):
        chip.step(IDLE, 1 << 5)
    for lvl in list(enc.bus["tx"]) + [1] * 400:
        chip.step(IDLE, (lvl & 1) << 5)
    # the receive stream packs fields bit-contiguously in the stream's bit order (narrow fields are not byte-aligned)
    s = chip.mem.streams[0]
    raw = chip.mem.data[0x400:0x400 + s.POS + 1]
    msb = order == "msb"
    bitl = [(raw[i // 8] >> ((7 - i % 8) if msb else (i % 8))) & 1 for i in range(s.POS * 8 + s.BIDX)]
    got = []
    for k in range(len(bitl) // bits):
        chunk = bitl[k * bits:(k + 1) * bits]
        got.append(sum(b << (bits - 1 - j) if msb else b << j for j, b in enumerate(chunk)))
    assert got == data
