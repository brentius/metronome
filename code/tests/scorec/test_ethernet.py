"""10BASE-T one direction (spec 16.4): compiled sender and receiver on the v2 cycle-level model vs the reference codec."""
import os
import random
import zlib

import pytest
from harness import *


@pytest.fixture(scope="module")
def eth_score():
    return parse(spec_block(3))


def run_eth_sender(body, extra=300):
    c = scorec.compile_score(spec_block(3), "sender", "td=O0 tdn=O1", skip_periodic=True)
    chip = new_chip(c)
    for _ in range(20):
        chip.step(IDLE, 0)
    send_frame_go(chip, body)
    n = (64 + 8 * len(body) + 32 + 2 + 110) * 6 + extra
    td, tdn = [], []
    for _ in range(n):
        uo, uio, oe = chip.step(IDLE, 0)
        td.append(uio & 1)
        tdn.append((uio >> 1) & 1)
    return c, chip, td, tdn


@pytest.mark.parametrize("n", [1, 7, 46, 60])
def test_sender_decodes_with_reference_codec(eth_score, n):
    body = bytes(random.Random(n).randrange(256) for _ in range(n))
    c, chip, td, tdn = run_eth_sender(body)
    r = Codec(eth_score).decode("receiver", {"td": td})
    assert r.ok, r.notes
    d = dict((e[0], e[1] if len(e) > 1 else None) for e in r.events)
    assert d["body"] == body and d["fcs"] == zlib.crc32(body)
    assert all(a + b == 1 for a, b in zip(td, tdn))
    assert all(t.LATE == 0 and t.OVR == 0 for t in chip.threads) and chip.ctrl.CONFLICT == 0
    assert not any(s.STARVED for s in chip.mem.streams) and chip.lines[0].TAPMISS == 0


def run_eth_receiver(wave, tail=2500):
    c = scorec.compile_score(spec_block(3), "receiver", "td=P2 tdn=P3", skip_periodic=True)
    chip = new_chip(c)
    for _ in range(60):
        chip.step(IDLE, 0)
    status = []
    for lvl in list(wave) + [0] * tail:
        chip.step(IDLE, (lvl & 1) << 2)
        if chip.host.OUTV:
            status.append(chip.host.OUTB)
            chip.host.OUTV = 0
    return c, chip, status


@pytest.mark.parametrize("n", [1, 7, 46, 60, 100])
def test_receiver_stores_body_and_fcs_from_codec_waveform(eth_score, n):
    body = bytes(random.Random(50 + n).randrange(256) for _ in range(n))
    enc = Codec(eth_score).encode_all([("body", body)])
    c, chip, status = run_eth_receiver(enc.bus["td"])
    pos = chip.mem.streams[0].POS
    got = bytes(chip.mem.data[0x400:0x400 + pos])
    assert status == [0], status
    assert got == body + zlib.crc32(body).to_bytes(4, "little")
    assert all(t.LATE == 0 and t.OVR == 0 for t in chip.threads) and chip.ctrl.CONFLICT == 0
    assert chip.lines[0].TAPMISS == 0


def test_receiver_flags_bad_fcs(eth_score):
    body = os.urandom(30)
    enc = Codec(eth_score).encode_all([("body", body), ("fcs", zlib.crc32(body) ^ 1)])
    c, chip, status = run_eth_receiver(enc.bus["td"])
    assert status == [4]                                  # bit 2: crc error


def test_receiver_two_frames_back_to_back(eth_score):
    b1, b2 = os.urandom(20), os.urandom(33)
    enc = Codec(eth_score).encode_all([("body", b1), ("body", b2)])
    c, chip, status = run_eth_receiver(enc.bus["td"])
    pos = chip.mem.streams[0].POS
    want = b1 + zlib.crc32(b1).to_bytes(4, "little") + b2 + zlib.crc32(b2).to_bytes(4, "little")
    assert status == [0, 0] and bytes(chip.mem.data[0x400:0x400 + pos]) == want


def test_receiver_flags_corrupted_preamble(eth_score):
    body = os.urandom(20)
    enc = Codec(eth_score).encode_all([("body", body)])
    td = list(enc.bus["td"])
    first = next(i for i, v in enumerate(td) if v)
    for i in range(first + 6 * 20 + 1, first + 6 * 20 + 5):      # flip one preamble cell's polarity
        td[i] ^= 1
    c, chip, status = run_eth_receiver(td)
    assert status and status[0] & 1                        # signature of the const bits differs


@pytest.mark.parametrize("ppm", [-5000, -2000, 2000, 5000, 15000])
def test_receiver_tolerates_sender_rate_error(eth_score, ppm):
    body = os.urandom(60)
    enc = Codec(eth_score, rate=10e6 * (1 + ppm / 1e6)).encode_all([("body", body)])
    c, chip, status = run_eth_receiver(enc.bus["td"])
    pos = chip.mem.streams[0].POS
    assert status == [0] and bytes(chip.mem.data[0x400:0x400 + pos]) == body + zlib.crc32(body).to_bytes(4, "little")
