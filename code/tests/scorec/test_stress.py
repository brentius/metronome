"""Stress projection (scorec/stress.py): faults placed by transforming the score, compiled by the unchanged compiler.

Two independent oracles per stress: the reference codec of the ORIGINAL score must reject the stressed waveform, and
the codec of the STRESSED score must accept it (the fault is exactly the one asked for).  Where a compiled receiver
exists, the receiver compiled from the original score must flag the fault in its status byte.
"""
import zlib

import pytest
from harness import *
from scorec.plan import CompileError
from scorec.stress import apply, compile_stressed

from test_ethernet import run_eth_receiver
from test_uart import run_receiver, run_sender


def eth_sender_trace(c, body, extra=300):
    chip = new_chip(c)
    for _ in range(20):
        chip.step(IDLE, 0)
    send_frame_go(chip, body)
    td = []
    for _ in range((64 + 8 * len(body) + 32 + 2 + 110) * 6 + extra):
        uo, uio, oe = chip.step(IDLE, 0)
        td.append(uio & 1)
    return chip, td


def test_uart_stop_bit_framing_error():
    orig = parse(spec_block(0))
    st = [("terminal", 1, (0,))]                       # stop bit(1) sent as bit(0)
    c = compile_stressed(spec_block(0), "sender", "tx=O8", st)
    assert c.report.startswith("STRESSED: terminal(1, (0,))")
    data = bytes([0x5A, 0x00, 0xFF])
    chip, tr = run_sender(c, data)
    bad = Codec(orig).decode("receiver", {"tx": tr})
    assert not bad.ok or bad.events != [("data", b) for b in data]
    # The original receiver, compiled from the nominal score, flags the stop-bit violation (status bit 1).  With the
    # stop bit low the next start bit has no falling edge, so later characters lose sync, as on a real UART.
    rc = scorec.compile_score(spec_block(0), "receiver", "tx=P5")
    _, statuses = run_receiver(rc, tr)
    assert statuses and statuses[0] & 2 and len([s for s in statuses if s == 0]) < len(data), statuses
    _, tr1 = run_sender(c, bytes([0x81]))
    assert run_receiver(rc, tr1)[1] == [2]                # one character: exactly one framing error


def test_uart_tempo_within_tolerance_still_decodes():
    data = bytes([0xA5, 0x3C])
    rc = scorec.compile_score(spec_block(0), "receiver", "tx=P5")
    for ppm in (-20000, 20000):
        c = compile_stressed(spec_block(0), "sender", "tx=O8", [("tempo", ppm)])
        chip, tr = run_sender(c, data)
        rchip, statuses = run_receiver(rc, tr)
        assert bytes(rchip.mem.data[0x400:0x400 + rchip.mem.streams[0].POS]) == data and statuses == [0, 0], ppm


def test_uart_tempo_far_outside_tolerance_is_caught():
    data = bytes([0x00, 0x00, 0x00])
    c = compile_stressed(spec_block(0), "sender", "tx=O8", [("tempo", 120000)])     # +12%
    chip, tr = run_sender(c, data)
    rc = scorec.compile_score(spec_block(0), "receiver", "tx=P5")
    rchip, statuses = run_receiver(rc, tr)
    got = bytes(rchip.mem.data[0x400:0x400 + rchip.mem.streams[0].POS])
    assert got != data or any(statuses), (got, statuses)


@pytest.mark.parametrize("bit", [0, 17, 31])
def test_ethernet_crc_corruption(bit):
    orig = parse(spec_block(3))
    st = [("crc_init", bit)]
    body = bytes(range(1, 21))
    c = compile_stressed(spec_block(3), "sender", "td=O0 tdn=O1", st, skip_periodic=True)
    chip, td = eth_sender_trace(c, body)
    assert all(t.LATE == 0 and t.OVR == 0 for t in chip.threads) and chip.ctrl.CONFLICT == 0
    bad = Codec(orig).decode("receiver", {"td": td})
    good = Codec(apply(orig, st)).decode("receiver", {"td": td})
    assert good.ok, good.notes
    assert not bad.ok
    d = dict((e[0], e[1] if len(e) > 1 else None) for e in good.events)
    assert d["body"] == body and d["fcs"] != zlib.crc32(body)
    _, _, status = run_eth_receiver(td)
    assert status == [4], status                         # the nominal receiver reports a crc error


def test_ethernet_sfd_corruption():
    orig = parse(spec_block(3))
    st = [("const", 7, 0)]                               # SFD D5 -> D4
    body = bytes(range(10))
    c = compile_stressed(spec_block(3), "sender", "td=O0 tdn=O1", st, skip_periodic=True)
    chip, td = eth_sender_trace(c, body)
    good = Codec(apply(orig, st)).decode("receiver", {"td": td})
    assert good.ok, good.notes
    bad = Codec(orig).decode("receiver", {"td": td})
    bd = dict((e[0], e[1] if len(e) > 1 else None) for e in bad.events) if bad.ok else {}
    assert not bad.ok or bd.get("body") != body
    _, rchip, status = run_eth_receiver(td)
    assert status != [0]


def test_stress_rejects_modes_that_do_not_apply():
    with pytest.raises(CompileError) as e:
        apply(parse(spec_block(0)), [("crc_init", 0)])
    assert e.value.code == "E-STRESS"
    with pytest.raises(CompileError):
        apply(parse(spec_block(3)), [("const", 99, 0)])
    with pytest.raises(CompileError):
        apply(parse(spec_block(0)), [("warp", 1)])


def test_stress_does_not_mutate_the_original():
    from score.crc import STD
    s = parse(spec_block(3))
    init, rate = STD["crc32_ethernet"].init, s.clock_for().rate
    st = apply(s, [("crc_init", 3), ("tempo", 5000), ("const", 0, 1)])
    assert "crc32_ethernet" not in s.crcs and STD["crc32_ethernet"].init == init and s.clock_for().rate == rate
    assert st.crcs["crc32_ethernet"].init == init ^ 8 and st.clock_for().rate == rate * 1005 / 1000
