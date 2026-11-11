"""eth_tx.mas on the reference model: frame body written into data RAM over pin-level SPI, transmission started with a
HOSTIN write, O8 decoded with the independent eth_decode (10BASE-T Manchester, CRC-32 = zlib.crc32).
Numbers are "verified in simulation against the reference model"."""
import zlib

import machine as m
import pytest
from driver import Driver
from protocols import eth_decode
from scenarios import ctrl_reg

RAM = m.HOST_MAP["DATA_BASE"]


def frame_body(n_payload, seed=1):
    dst, src, typ = bytes.fromhex("0123456789ab"), bytes.fromhex("fedcba987654"), b"\x08\x00"
    pay = bytes((seed * 31 + i * 7) & 0xFF for i in range(n_payload))
    return dst + src + typ + pay


def send(d, body):
    d.write(RAM, len(body).to_bytes(2, "little") + body)
    t0 = len(d.trace)
    d.write(ctrl_reg("HOSTIN"), [1])
    d.idle((len(body) + 12 + 2) * 8 * 6 + 400)
    return t0


@pytest.mark.parametrize("n_payload", [46, 1, 100])
def test_eth_tx(n_payload):
    d = Driver(hi=0x00)
    d.load("eth_tx.mas")
    body = frame_body(n_payload)
    t0 = send(d, body)
    lv = d.out_bit(8)
    assert not any(lv[:t0]), "O8 not idle low before start"
    frames = eth_decode(lv, 6.0)
    assert len(frames) == 1, frames
    f = frames[0]
    assert f.data == body
    assert f.fcs_ok          # eth_decode compares the received FCS with zlib.crc32(body)
    # timing: all transitions are on the 3-clock grid relative to the first one
    edges = [t for t in range(1, len(lv)) if lv[t] != lv[t - 1]]
    runs = {b - a for a, b in zip(edges, edges[1:]) if b - a <= 6}
    assert runs <= {3, 6}, runs
    grid = [(t - edges[0]) % 3 for t in edges if t <= edges[-1] - 18]
    assert set(grid) == {0}, "edges off the half-bit grid"
    inframe = [b - a for a, b in zip(edges, edges[1:])][:-1]
    assert max(inframe) <= 6, 'gap inside the frame'
    # last edge -> idle: TP_IDL high hold
    last = edges[-1]
    assert lv[last - 1] == 1 and lv[last] == 0, "line must end low after TP_IDL"
    hold = last - edges[-2]
    nbits = (7 + 1 + len(body) + 4) * 8
    dur = (edges[-2] - edges[0])
    print(f"eth_tx payload {n_payload}: body {len(body)} B + FCS {zlib.crc32(body):08x} decoded ok; half-bit widths {sorted(runs)} "
          f"clocks (jitter 0 clocks: every edge on the 3-clock grid); {nbits} bits in ~{dur} clocks "
          f"({dur / nbits:.3f} clocks/bit); TP_IDL high {hold} clocks (verified in simulation against the reference model)")
    assert hold >= 12
    assert 5.95 < dur / nbits < 6.05


def test_eth_back_to_back_frames():
    d = Driver(hi=0x00)
    d.load("eth_tx.mas")
    bodies = [frame_body(60, 3), frame_body(46, 4)]
    for b in bodies:
        send(d, b)
    frames = eth_decode(d.out_bit(8), 6.0)
    assert [f.data for f in frames] == bodies and all(f.fcs_ok for f in frames)
