"""I2C (spec 16.2): compiled controller and target on the v2 cycle-level model, open-drain wired-AND bus.

Chip as controller: a behavioural I2C target written here (not from the score) answers on the bus; the resolved bus
is decoded by the reference codec (as the target role) and by the independent checker `i2c_decode`.
Chip as target: the reference codec's controller drive waveform is resolved against the chip's SDA; the bus is
decoded by the codec (as the controller role) and by the independent checker.
"""
import random
import sys

import pytest
from harness import *

sys.path.insert(0, str(ROOT / "code" / "tests" / "checkers"))
import protocols as ind  # noqa: E402

from scorec.bus import controller_rx, controller_tx, target_rx  # noqa: E402

BEAT = 600                      # chip cycles per beat at 100 kHz
CTL_BIND = "scl=P0/O0 sda=P1/O1"
TGT_BIND = "scl=P0 sda=P1/O1"


@pytest.fixture(scope="module")
def i2c_score():
    return parse(spec_block(1))


@pytest.fixture(scope="module")
def ctl_compiled():
    return scorec.compile_score(spec_block(1), "controller", CTL_BIND)


def od(oe, out, k):
    """Open-drain drive of uio pin k: 0 when enabled, None when released.  Driving 1 is a bug."""
    if (oe >> k) & 1:
        assert not (out >> k) & 1, f"O{k} drives high on an open-drain wire"
        return 0
    return None


def wand(*d):
    return 0 if 0 in d else 1


class PyTarget:
    """Behavioural I2C target (independent of the score): 7-bit address, ACKs writes, returns `rbytes` on reads,
    optional clock stretching after the address acknowledge."""

    def __init__(self, my, rbytes=(), stretch=0):
        self.my, self.rq, self.stretch = my, list(rbytes), stretch
        self.mode, self.k, self.sh, self.cur = "idle", 0, 0, 0
        self.sda, self.scl, self.hold = None, None, 0
        self.ps, self.pd = 1, 1
        self.writes, self.reads = [], []

    def step(self, scl, sda):
        rise, fall = scl and not self.ps, (not scl) and self.ps
        if scl and self.ps and sda != self.pd:
            if not sda:                     # START / repeated START
                self.mode, self.k, self.sh, self.sda = "addr", 0, 0, None
            else:                           # STOP
                self.mode, self.sda = "idle", None
        elif rise and self.mode in ("addr", "w", "r"):
            self.k += 1
            if self.k <= 8 and self.mode != "r":
                self.sh = (self.sh << 1) | sda
            if self.mode == "r" and self.k == 9 and sda:
                self.mode = "done"          # controller NACK: last byte
        elif fall and self.mode in ("addr", "w", "r"):
            k = self.k
            if self.mode == "addr" and k == 8:
                if (self.sh >> 1) == self.my:
                    self.sda, self.rw = 0, self.sh & 1
                else:
                    self.mode, self.sda = "ignore", None
            elif self.mode == "addr" and k == 9:
                self.mode, self.k, self.sda = ("r" if self.rw else "w"), 0, None
                self.hold = self.stretch
                if self.rw:
                    self.load()
            elif self.mode == "w" and k == 8:
                self.writes.append(self.sh & 0xFF)
                self.sda = 0
            elif self.mode == "w" and k == 9:
                self.k, self.sh, self.sda = 0, 0, None
            elif self.mode == "r" and k < 8:
                self.sda = None if (self.cur >> (7 - k)) & 1 else 0
            elif self.mode == "r" and k == 8:
                self.sda = None
            elif self.mode == "r" and k == 9:
                self.k = 0
                self.load()
        if self.hold:
            self.hold -= 1
            self.scl = 0
        else:
            self.scl = None
        self.ps, self.pd = scl, sda
        return self.scl, self.sda

    def load(self):
        self.cur = self.rq.pop(0) if self.rq else 0xFF
        self.reads.append(self.cur)
        self.sda = None if self.cur & 0x80 else 0


def run_controller(compiled, requests, peer, extra=0):
    chip = new_chip(compiled)
    for _ in range(20):
        chip.step(IDLE, 0b11)
    tx = controller_tx(requests)
    chip.backdoor_write(HM["DATA_BASE"], tx)
    stream_reg(chip, 0, "LEN", len(tx), 2)
    stream_rewind(chip, 0)
    stream_rewind(chip, 1)
    for _ in range(40):
        chip.step(IDLE, 0b11)
    hostin(chip, 1)
    beats = 4 + len(requests) + sum(10 + 9 * (len(a) if k == "w" else a) for _, k, a in requests)
    scl_l, sda_l = [], []
    uo, uio, oe = chip.step(IDLE, 0b11)
    for _ in range(beats * BEAT + extra):
        ps, pd = peer.scl, peer.sda
        scl = wand(od(oe, uio, 0), ps)
        sda = wand(od(oe, uio, 1), pd)
        scl_l.append(scl)
        sda_l.append(sda)
        uo, uio, oe = chip.step(IDLE, scl | (sda << 1))
        peer.step(scl, sda)
    return chip, {"scl": scl_l, "sda": sda_l}


def expected_events(requests, my, peer_reads):
    ev, rd = [("start",)], list(peer_reads)
    for i, (a, kind, arg) in enumerate(requests):
        if i:
            ev += [("rstart",), ("start",)]
        ev += [("addr", a), ("rw", 0 if kind == "w" else 1)]
        if a != my:
            ev.append(("ack", 1))
            break
        ev.append(("ack", 0))
        if kind == "w":
            for d in arg:
                ev += [("data", d), ("dack", 0)]
        else:
            for j in range(arg):
                ev += [("data", rd.pop(0)), ("more", 1 if j == arg - 1 else 0)]
    ev.append(("stop",))
    return ev


def checker_view(events):
    """The independent checker's events for a transaction given as codec events."""
    out, hdr, prev = [], None, None
    for e in events:
        if e[0] == "start" and prev == "rstart":
            pass                                    # `rstart start`: one repeated START (16.2)
        elif e[0] in ("start", "rstart"):
            out.append(("S",) if e[0] == "start" else ("Sr",))
        elif e[0] == "addr":
            hdr = e[1] << 1
        elif e[0] == "rw":
            hdr |= e[1]
        elif e[0] == "ack":
            out.append(("B", hdr, e[1] == 0))
        elif e[0] == "data":
            d = e[1]
        elif e[0] in ("dack", "more"):
            out.append(("B", d, e[1] == 0))
        elif e[0] == "stop":
            out.append(("P",))
        prev = e[0]
    return out


def ideal(bus):
    """Codec view of a real bus.  The score's symbols put every SDA change at the controller's beat boundary, the
    middle of the SCL-low phase; a follower target changes SDA right after the falling SCL edge, which the I2C
    rule allows (SDA may change anywhere while SCL is low).  Move each change inside an SCL-low phase to the
    middle of that phase.  Levels while SCL is high (data, START, STOP) are untouched."""
    scl, sda = bus["scl"], list(bus["sda"])
    i, n = 0, len(scl)
    while i < n:
        if scl[i] == 0:
            j = i
            while j < n and scl[j] == 0:
                j += 1
            a, b = sda[i], sda[j - 1]
            mid = (i + j) // 2
            for k in range(i, j):
                sda[k] = a if k < mid else b
            i = j
        else:
            i += 1
    return {"scl": list(scl), "sda": sda}


def clean(chip):
    assert all(t.LATE == 0 and t.OVR == 0 for t in chip.threads), [(t.LATE, t.OVR) for t in chip.threads]
    assert chip.ctrl.CONFLICT == 0
    assert all(ln.TAPMISS == 0 for ln in chip.lines)


def rand_requests(rng, my, n=None):
    reqs = []
    for _ in range(n or rng.randrange(1, 3)):
        if rng.random() < 0.5:
            reqs.append((my, "w", bytes(rng.randrange(256) for _ in range(rng.randrange(0, 3)))))
        else:
            reqs.append((my, "r", rng.randrange(1, 3)))
    return reqs


# ---- controller ---------------------------------------------------------------------------------------------
@pytest.mark.parametrize("seed", range(4))
def test_controller_transactions_decode_and_receive(i2c_score, ctl_compiled, seed):
    rng = random.Random(seed)
    my = rng.randrange(8, 120)
    reqs = rand_requests(rng, my)
    rb = [rng.randrange(256) for _ in range(8)]
    peer = PyTarget(my, rb)
    chip, bus = run_controller(ctl_compiled, reqs, peer)
    want = expected_events(reqs, my, peer.reads)
    r = Codec(i2c_score, params={"my_addr": my}).decode("target", ideal(bus))
    assert r.ok, r.notes
    assert r.events == want
    txs = ind.i2c_decode(bus["scl"], bus["sda"])
    assert len(txs) == 1 and txs[0].events == checker_view(want)
    # what the controller received, unpacked by the host helper
    s1 = chip.mem.streams[1]
    nbits = s1.POS * 8 + s1.BIDX
    assert s1.BIDX == 0, "the stop flushes the receive stream"
    got = controller_rx(reqs, bytes(chip.mem.data[0x400:0x400 + s1.POS]), nbits)
    exp, rd = [], list(peer.reads)
    for a, kind, arg in reqs:
        exp.append((0, [0] * len(arg) if kind == "w" else [rd.pop(0) for _ in range(arg)]))
    assert got == exp
    assert [d for a, k, arg in reqs if k == "w" for d in arg] == peer.writes
    assert chip.host.OUTV == 1 and chip.host.OUTB == 0
    clean(chip)


def test_controller_stops_on_address_nack(i2c_score, ctl_compiled):
    my = 0x42
    reqs = [(0x17, "w", b"\x55"), (my, "r", 1)]
    peer = PyTarget(my, [0xA5])
    chip, bus = run_controller(ctl_compiled, reqs, peer)
    want = [("start",), ("addr", 0x17), ("rw", 0), ("ack", 1), ("stop",)]
    r = Codec(i2c_score, params={"my_addr": my}).decode("target", ideal(bus))
    assert r.ok and r.events == want, r
    assert ind.i2c_decode(bus["scl"], bus["sda"])[0].events == [("S",), ("B", 0x17 << 1, False), ("P",)]
    assert chip.host.OUTV == 1 and chip.host.OUTB == 1
    assert peer.writes == [] and peer.reads == []
    clean(chip)


def test_controller_waits_for_clock_stretching(i2c_score, ctl_compiled):
    """The target holds SCL low for 3 beats after the address acknowledge: the controller's line holds (part B 3.2a)
    and the transfer still decodes; the data bit after the stretch is sampled after SCL is released."""
    my = 0x21
    reqs = [(my, "r", 2), (my, "w", b"\x3C")]
    peer = PyTarget(my, [0x96, 0x0F], stretch=3 * BEAT)
    chip, bus = run_controller(ctl_compiled, reqs, peer, extra=8 * BEAT)
    want = expected_events(reqs, my, peer.reads)
    # the reference codec decodes at the nominal beat and cannot follow a stretched one: the checker is the oracle
    assert ind.i2c_decode(bus["scl"], bus["sda"])[0].events == checker_view(want)
    # the longest SCL low run covers the stretch
    run = best = 0
    for v in bus["scl"]:
        run = run + 1 if v == 0 else 0
        best = max(best, run)
    assert best >= 3 * BEAT
    s1 = chip.mem.streams[1]
    got = controller_rx(reqs, bytes(chip.mem.data[0x400:0x400 + s1.POS]), s1.POS * 8)
    assert got == [(0, [0x96, 0x0F]), (0, [0])]
    clean(chip)


# ---- target -------------------------------------------------------------------------------------------------
def run_target(events, my, rbytes=b"", rate=None, tail=4):
    kw = {"rate_hz": rate} if rate else {}
    c = scorec.compile_score(spec_block(1), "target", TGT_BIND, follow_period=4 * BEAT,
                             params={"my_addr": my}, **kw)
    chip = new_chip(c)
    for _ in range(20):
        chip.step(IDLE, 0b11)
    chip.backdoor_write(HM["DATA_BASE"], bytes(rbytes) or b"\x00")
    stream_reg(chip, 0, "LEN", max(1, len(rbytes)), 2)
    stream_rewind(chip, 0)
    stream_rewind(chip, 1)
    for _ in range(60):
        chip.step(IDLE, 0b11)
    codec = Codec(parse(spec_block(1)), params={"my_addr": my}, rate=rate)
    enc = codec.encode_all(events, lead=int(2 * codec.P), tail=int(tail * codec.P))
    ctl = enc.drives["controller"]
    scl_l, sda_l = [], []
    uo, uio, oe = chip.step(IDLE, 0b11)
    for t in range(ctl.n):
        scl = wand(ctl["scl"][t])
        sda = wand(ctl["sda"][t], od(oe, uio, 1))
        scl_l.append(scl)
        sda_l.append(sda)
        uo, uio, oe = chip.step(IDLE, scl | (sda << 1))
    return c, chip, {"scl": scl_l, "sda": sda_l}


def tgt_case(rng, my):
    ev, ctl_bits, rbytes = [("start",)], [], []
    for k in range(rng.randrange(1, 4)):
        if k:
            ev += [("rstart",), ("start",)]
        addr = my if rng.random() < 0.75 else (my ^ (1 << rng.randrange(7)))
        rw = rng.randrange(2)
        ev += [("addr", addr), ("rw", rw), ("ack", 0 if addr == my else 1)]
        ctl_bits += [(addr >> (6 - i)) & 1 for i in range(7)] + [rw]
        if addr != my:
            continue
        if rw == 0:
            for _ in range(rng.randrange(0, 3)):
                d = rng.randrange(256)
                ev += [("data", d), ("dack", 0)]
                ctl_bits += [(d >> (7 - i)) & 1 for i in range(8)]
        else:
            n = rng.randrange(1, 3)
            for i in range(n):
                d = rng.randrange(256)
                rbytes.append(d)
                ev += [("data", d), ("more", 1 if i == n - 1 else 0)]
                ctl_bits.append(1 if i == n - 1 else 0)
    ev.append(("stop",))
    return ev, ctl_bits, rbytes


def rx_records(chip, my):
    s1 = chip.mem.streams[1]
    assert s1.BIDX == 0, "the STOP flushes the receive stream"
    return target_rx(bytes(chip.mem.data[0x400:0x400 + s1.POS]), my)


def want_records(ev, my):
    out, cur, a, rw = [], None, None, None
    for e in ev:
        if e[0] in ("start", "rstart"):
            cur = [] if cur is None else cur
        elif e[0] == "addr":
            a = e[1]
        elif e[0] == "rw":
            rw = e[1]
            cur.append((a, rw, None if a != my else []))
        elif e[0] == "data" and rw == 0:
            cur[-1][2].append(e[1])
        elif e[0] == "more":
            cur[-1][2].append(e[1])
        elif e[0] == "stop":
            out.append(cur)
            cur = None
    return out


@pytest.mark.parametrize("seed", range(5))
def test_target_answers_codec_controller(i2c_score, seed):
    rng = random.Random(50 + seed)
    my = rng.randrange(8, 120)
    ev, ctl_bits, rbytes = tgt_case(rng, my)
    c, chip, bus = run_target(ev, my, rbytes)
    r = Codec(i2c_score, params={"my_addr": my}).decode("controller", ideal(bus))
    assert r.ok, r.notes
    assert r.events == ev
    assert ind.i2c_decode(bus["scl"], bus["sda"])[0].events == checker_view(ev)
    assert rx_records(chip, my) == want_records(ev, my)
    assert chip.host.OUTV == 1
    clean(chip)


@pytest.mark.parametrize("rate", [400e3, 25e3])
def test_target_follows_other_rates(i2c_score, rate):
    my = 0x5A
    ev = [("start",), ("addr", my), ("rw", 0), ("ack", 0), ("data", 0xC3), ("dack", 0),
          ("rstart",), ("start",), ("addr", my), ("rw", 1), ("ack", 0), ("data", 0x81), ("more", 0), ("data", 0x7E),
          ("more", 1), ("stop",)]
    c, chip, bus = run_target(ev, my, b"\x81\x7E", rate=rate)
    r = Codec(i2c_score, params={"my_addr": my}, rate=rate).decode("controller", ideal(bus))
    assert r.ok and r.events == ev, r
    assert ind.i2c_decode(bus["scl"], bus["sda"])[0].events == checker_view(ev)
    clean(chip)


def test_target_abort_on_stop_then_new_transaction(i2c_score):
    """`on stop_c -> bus`: a STOP inside the address abandons it; the next transaction is answered normally and
    nothing is driven at the next START's falling SCL edge."""
    my = 0x10
    ev = [("start",), ("addr", 0x11), ("abort", "stop_c"),
          ("start",), ("addr", my), ("rw", 0), ("ack", 0), ("data", 0x55), ("dack", 0), ("stop",)]
    c, chip, bus = run_target(ev, my)
    r = Codec(i2c_score, params={"my_addr": my}).decode("controller", ideal(bus))
    assert r.events == ev, r
    recs = rx_records(chip, my)
    assert recs[-1] == [(my, 0, [0x55])]           # the aborted header leaves its own partial record before it
    clean(chip)


def test_target_param_takes_effect_at_next_start(i2c_score):
    """The address parameter is a data RAM byte (host map), re-read after every START."""
    c = scorec.compile_score(spec_block(1), "target", TGT_BIND, follow_period=4 * BEAT, params={"my_addr": 0x33})
    assert c.host["params"]["my_addr"]["initial"] == 0x33
    my = 0x44
    ev = [("start",), ("addr", my), ("rw", 0), ("ack", 0), ("data", 0x01), ("dack", 0), ("stop",)]
    _, chip, _ = run_target(ev, 0x33)              # compiled for 0x33: does not answer 0x44
    assert rx_records(chip, 0x33) == [[(my, 0, None)]]
    # rerun with the parameter byte rewritten by the host before the transaction
    chip2 = new_chip(c)
    chip2.backdoor_write(HM["DATA_BASE"] + c.host["params"]["my_addr"]["data_addr"], bytes([my]))
    codec = Codec(parse(spec_block(1)), params={"my_addr": my})
    enc = codec.encode_all(ev, lead=int(2 * codec.P), tail=int(4 * codec.P))
    ctl = enc.drives["controller"]
    uo, uio, oe = chip2.step(IDLE, 0b11)
    scl_l, sda_l = [], []
    for t in range(ctl.n):
        scl, sda = wand(ctl["scl"][t]), wand(ctl["sda"][t], od(oe, uio, 1))
        scl_l.append(scl)
        sda_l.append(sda)
        uo, uio, oe = chip2.step(IDLE, scl | (sda << 1))
    r = codec.decode("controller", ideal({"scl": scl_l, "sda": sda_l}))
    assert r.ok and r.events == ev, r


def test_both_roles_compile_and_fit(ctl_compiled):
    rep = ctl_compiled.report
    assert "hold on scl at tap 1" in rep and ctl_compiled.ok
    t = scorec.compile_score(spec_block(1), "target", TGT_BIND, follow_period=4 * BEAT, params={"my_addr": 1})
    assert t.ok and "PINA.FALL" in t.mas and "watch0" in t.mas
