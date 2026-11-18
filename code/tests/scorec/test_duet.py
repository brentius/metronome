"""Duet: two Metronomes compiled from ONE score, one per role, wired back to back on the v2 cycle-level model.

This is the executable form of "one score, both roles": neither side is a behavioural model or a codec waveform.  Each
chip sees the other's pins one cycle late (a wire plus an input register).  The bus is also decoded by the independent
reference codec (and, for I2C, the independent `i2c_decode` checker), so agreement is not just two copies of the same
compiler bug agreeing with each other.

Evidence class: verified in simulation (model only), not RTL lockstep and not hardware.
"""
import random
import sys

import pytest
from harness import *

sys.path.insert(0, str(ROOT / "code" / "tests" / "checkers"))
import protocols as ind  # noqa: E402

from scorec.bus import controller_rx, controller_tx, target_rx  # noqa: E402

from test_i2c import BEAT, checker_view, clean, ideal, od, wand, want_records  # noqa: E402


def no_flags(chip):
    assert all(t.LATE == 0 and t.OVR == 0 for t in chip.threads) and chip.ctrl.CONFLICT == 0
    assert all(ln.TAPMISS == 0 for ln in chip.lines)


# ---- UART: sender chip -> receiver chip ---------------------------------------------------------------------------
@pytest.mark.parametrize("seed", range(3))
def test_uart_duet(seed):
    rng = random.Random(seed)
    data = bytes(rng.randrange(256) for _ in range(rng.randrange(1, 7)))
    a = new_chip(scorec.compile_score(spec_block(0), "sender", "tx=O8"))
    b = new_chip(scorec.compile_score(spec_block(0), "receiver", "tx=P5"))
    pending, statuses, tx, trace = list(data), [], 1, []
    for _ in range(40):
        a.step(IDLE, 0)
        b.step(IDLE, 1 << 5)
    for _ in range(int((len(data) * 10 + 4) * 520.9)):
        if pending and a.host.INV == 0:
            hostin(a, pending.pop(0))
        uo, _, _ = a.step(IDLE, 0)
        b.step(IDLE, tx << 5)
        tx = (uo >> 2) & 1
        trace.append(tx)
        if b.host.OUTV:
            statuses.append(b.host.OUTB)
            b.host.OUTV = 0
    assert bytes(b.mem.data[0x400:0x400 + b.mem.streams[0].POS]) == data
    assert statuses == [0] * len(data)
    r = Codec(parse(spec_block(0))).decode("receiver", {"tx": trace})
    assert r.ok and r.events == [("data", x) for x in data], r.notes
    no_flags(a)
    no_flags(b)


# ---- SPI mode 0: controller chip <-> peripheral chip, full duplex ---------------------------------------------------
@pytest.mark.parametrize("seed", range(3))
def test_spi_duet(seed):
    rng = random.Random(20 + seed)
    n = rng.randrange(1, 5)
    mo = bytes(rng.randrange(256) for _ in range(n))
    mi = bytes(rng.randrange(256) for _ in range(n))
    a = new_chip(scorec.compile_score(spec_block(2), "controller", "sck=O8 cs_n=O9 mosi=O10 miso=P1"))
    b = new_chip(scorec.compile_score(spec_block(2), "peripheral", "sck=P0 mosi=P1 cs_n=P2 miso=O8"))
    for _ in range(20):
        a.step(IDLE, 0)
        b.step(IDLE, 0b100)
    a.backdoor_write(HM["DATA_BASE"], mo)
    stream_reg(a, 0, "LEN", n, 2)
    stream_reg(a, 1, "LEN", 992, 2)
    stream_rewind(a, 0)
    stream_rewind(a, 1)
    b.backdoor_write(HM["DATA_BASE"], mi)
    stream_reg(b, 0, "LEN", n + 2, 2)
    stream_rewind(b, 0)
    for _ in range(60):
        a.step(IDLE, 0)
        b.step(IDLE, 0b100)
    hostin(a, 1)
    a_to_b, miso = 0b100, 0
    bus = {"sck": [], "cs_n": [], "mosi": [], "miso": []}
    for _ in range((n * 8 + 8) * 60 + 600):
        uo_a, _, _ = a.step(IDLE, miso << 1)
        uo_b, _, _ = b.step(IDLE, a_to_b)
        sck, cs, mosi = (uo_a >> 2) & 1, (uo_a >> 3) & 1, (uo_a >> 4) & 1
        a_to_b, miso = sck | (mosi << 1) | (cs << 2), (uo_b >> 2) & 1
        for k, v in (("sck", sck), ("cs_n", cs), ("mosi", mosi), ("miso", miso)):
            bus[k].append(v)
    assert bytes(b.mem.data[0x400:0x400 + b.mem.streams[1].POS]) == mo         # peripheral received MOSI
    assert bytes(a.mem.data[0x400:0x400 + a.mem.streams[1].POS])[:n] == mi     # controller received MISO
    want = [("select",)] + [e for x, y in zip(mo, mi) for e in (("out", x), ("in", y))] + [("deselect",)]
    r = Codec(parse(spec_block(2))).decode("peripheral", bus)
    assert r.ok and r.events == want, r.notes
    no_flags(a)
    no_flags(b)


# ---- I2C: controller chip and target chip on one open-drain wired-AND bus -----------------------------------------
@pytest.mark.parametrize("seed", range(3))
def test_i2c_duet(seed):
    rng = random.Random(40 + seed)
    my = rng.randrange(8, 120)
    other = my ^ (1 << rng.randrange(7))
    reqs = [(my, "w", bytes(rng.randrange(256) for _ in range(rng.randrange(1, 3)))),
            (my, "r", rng.randrange(1, 3))]
    if seed == 2:
        reqs = [(other, "w", b"\x99")]                                         # address NACK: nobody answers
    rbytes = bytes(rng.randrange(256) for _ in range(4))
    a = new_chip(scorec.compile_score(spec_block(1), "controller", "scl=P0/O0 sda=P1/O1"))
    b = new_chip(scorec.compile_score(spec_block(1), "target", "scl=P0 sda=P1/O1", follow_period=4 * BEAT,
                                      params={"my_addr": my}))
    for _ in range(20):
        a.step(IDLE, 0b11)
        b.step(IDLE, 0b11)
    tx = controller_tx(reqs)
    a.backdoor_write(HM["DATA_BASE"], tx)
    stream_reg(a, 0, "LEN", len(tx), 2)
    stream_rewind(a, 0)
    stream_rewind(a, 1)
    b.backdoor_write(HM["DATA_BASE"], rbytes)
    stream_reg(b, 0, "LEN", len(rbytes), 2)
    stream_rewind(b, 0)
    stream_rewind(b, 1)
    for _ in range(60):
        a.step(IDLE, 0b11)
        b.step(IDLE, 0b11)
    hostin(a, 1)
    beats = 6 + sum(10 + 9 * (len(x) if k == "w" else x) for _, k, x in reqs)
    _, ua, oa = a.step(IDLE, 0b11)
    _, ub, ob = b.step(IDLE, 0b11)
    bus = {"scl": [], "sda": []}
    for _ in range(beats * BEAT):
        scl = wand(od(oa, ua, 0), od(ob, ub, 0))
        sda = wand(od(oa, ua, 1), od(ob, ub, 1))
        bus["scl"].append(scl)
        bus["sda"].append(sda)
        _, ua, oa = a.step(IDLE, scl | (sda << 1))
        _, ub, ob = b.step(IDLE, scl | (sda << 1))
    # what the independent checker saw on the wire
    txs = ind.i2c_decode(bus["scl"], bus["sda"])
    assert len(txs) == 1
    if seed == 2:
        assert txs[0].events == [("S",), ("B", other << 1, False), ("P",)]
        assert a.host.OUTV == 1 and a.host.OUTB == 1                            # controller: address not acknowledged
        clean(a)
        clean(b)
        return
    # controller side: write acks and the bytes read from the target's stream
    s1 = a.mem.streams[1]
    got = controller_rx(reqs, bytes(a.mem.data[0x400:0x400 + s1.POS]), s1.POS * 8 + s1.BIDX)
    nr = reqs[1][2]
    assert got == [(0, [0] * len(reqs[0][2])), (0, list(rbytes[:nr]))]
    assert a.host.OUTV == 1 and a.host.OUTB == 0
    # target side: the records it stored are those of the transaction on the wire
    ev = [("start",), ("addr", my), ("rw", 0), ("ack", 0)]
    ev += [e for d in reqs[0][2] for e in (("data", d), ("dack", 0))]
    ev += [("rstart",), ("start",), ("addr", my), ("rw", 1), ("ack", 0)]
    ev += [e for i in range(nr) for e in (("data", rbytes[i]), ("more", 1 if i == nr - 1 else 0))]
    ev.append(("stop",))
    assert txs[0].events == checker_view(ev)
    r = Codec(parse(spec_block(1)), params={"my_addr": my}).decode("target", ideal(bus))
    assert r.ok and r.events == ev, r.notes
    s1b = b.mem.streams[1]
    assert target_rx(bytes(b.mem.data[0x400:0x400 + s1b.POS]), my) == want_records(ev, my)
    clean(a)
    clean(b)


# ---- 10BASE-T: sender chip -> receiver chip, one direction ---------------------------------------------------------
@pytest.mark.parametrize("n", [1, 46])
def test_ethernet_duet(n):
    import zlib
    body = bytes(random.Random(70 + n).randrange(256) for _ in range(n))
    a = new_chip(scorec.compile_score(spec_block(3), "sender", "td=O0 tdn=O1", skip_periodic=True))
    b = new_chip(scorec.compile_score(spec_block(3), "receiver", "td=P2 tdn=P3", skip_periodic=True))
    for _ in range(60):
        a.step(IDLE, 0)
        b.step(IDLE, 0)
    send_frame_go(a, body)                     # steps only `a` while it settles
    status, td, tr = [], 0, []
    for _ in range((64 + 8 * n + 32 + 2 + 110) * 6 + 2500):
        _, uio, _ = a.step(IDLE, 0)
        b.step(IDLE, (td << 2) | ((1 - td) << 3))
        td = uio & 1
        tr.append(td)
        if b.host.OUTV:
            status.append(b.host.OUTB)
            b.host.OUTV = 0
    assert status == [0], status
    pos = b.mem.streams[0].POS
    assert bytes(b.mem.data[0x400:0x400 + pos]) == body + zlib.crc32(body).to_bytes(4, "little")
    r = Codec(parse(spec_block(3))).decode("receiver", {"td": tr})
    assert r.ok, r.notes
    no_flags(a)
    no_flags(b)
