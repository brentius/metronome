"""Check card-to-wire CRC identification and reply against an independent codec."""

import binascii

import pytest

from harness import load
from metronome2 import Chip
from metronome2_tools.asm import assemble_text
from metronome2_tools.check import check
from transcribe.fw_crc import CLOCKS_PER_BIT, REPLY, source


def crc_smbus(data):
    value = 0
    for byte in data:
        value ^= byte
        for _ in range(8):
            value = ((value << 1) ^ (0x107 if value & 0x80 else 0)) & 255
    return bytes([value])


def crc_arc(data):
    value = 0
    for byte in data:
        value ^= byte
        for _ in range(8):
            value = (value >> 1) ^ (0xA001 if value & 1 else 0)
    return value.to_bytes(2, "little")


def crc_ccitt(data):
    return binascii.crc_hqx(data, 0xFFFF).to_bytes(2, "big")


def run(frames, reply):
    image = assemble_text(source(frames, reply))
    assert not check(image).errors
    chip = Chip()
    for _ in range(4):
        chip.step(2, 0)
    load(chip, image)
    tx = []
    for _ in range(50_000):
        uo, _, _ = chip.step(2, 0)
        tx.append((uo >> 2) & 1)
        if chip.host.OUTV:
            break
    else:
        pytest.fail("CRC firmware did not complete")
    assert not chip.contract_violations
    assert not (chip.ctrl.CONFLICT or chip.ctrl.MEMHAZ or chip.ctrl.CWOVR)
    assert not any(thread.LATE or thread.OVR for thread in chip.threads)
    return chip, tx


def receive(tx):
    rx = bytearray()
    cycle = tx.index(1) + 1
    while cycle < len(tx) and 0 in tx[cycle:]:
        start = tx.index(0, cycle)
        sample = start + CLOCKS_PER_BIT // 2
        frame = tx[sample:sample + 10 * CLOCKS_PER_BIT:CLOCKS_PER_BIT]
        assert len(frame) == 10 and frame[0] == 0 and frame[-1] == 1
        rx.append(sum(bit << n for n, bit in enumerate(frame[1:9])))
        cycle = sample + 9 * CLOCKS_PER_BIT + 1
    return bytes(rx)


@pytest.mark.parametrize("profile,crc", [(1, crc_smbus), (2, crc_ccitt), (4, crc_arc)])
def test_profile_detect_and_transmit(profile, crc):
    traffic = [b"test", b"\x00\xc3\x1e\x99", b"\x02\x00\x10\xf1"]
    frames = [payload + crc(payload) for payload in traffic]
    reply = b"new!"
    chip, tx = run(frames, reply)
    expected = reply + crc(reply)
    assert chip.host.OUTB == profile
    assert bytes(chip.mem.data[REPLY:REPLY + len(expected)]) == expected
    assert receive(tx) == expected


def test_bad_crc_suppresses_tx():
    frames = [payload + crc_ccitt(payload) for payload in (b"test", b"test"[::-1], b"mock")]
    frames[1] = bytes([frames[1][0] ^ 1]) + frames[1][1:]
    chip, tx = run(frames, b"new!")
    assert chip.host.OUTB == 0
    assert receive(tx) == b""


def test_ambiguous_crc_suppresses_tx():
    frames = list(map(bytes.fromhex, ("222d00009a71", "d3c30000c8b8", "b13d0100b760")))
    assert all(crc_ccitt(frame[:-2]) == crc_arc(frame[:-2]) == frame[-2:] for frame in frames)
    chip, tx = run(frames, b"new!")
    assert chip.host.OUTB == 6
    assert receive(tx) == b""
