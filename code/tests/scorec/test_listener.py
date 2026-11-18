"""Listener projection (scorec/listener.py): an input-only role from the same score, on the v2 cycle-level model.

Oracles: the reference codec (the clean waveforms), the stress transforms (faults placed on the beat by the unchanged
sender compiler), and the chip's own pin outputs (the listener must never drive anything).  Model-level evidence only."""
import random

import pytest
from harness import *
from scorec.listener import ListenerDecoder, split_spi_payload
from scorec.plan import CompileError
from scorec.stress import compile_stressed

from test_uart import run_sender

UART_P = 3125 / 6


class Listen:
    """Run a compiled listener on a pin trace; collect pin activity to prove it never drives."""

    def __init__(self, compiled, idle_pins):
        self.c = compiled
        self.chip = new_chip(compiled)
        self.oe_seen = 0
        self.uo_seen = set()
        self.idle = idle_pins
        self.statuses = []

    def step(self, ui, uio):
        uo, uio_o, oe = self.chip.step(ui, uio)
        self.oe_seen |= oe
        self.uo_seen.add(uo)
        if self.chip.host.OUTV:
            self.statuses.append(self.chip.host.OUTB)
            self.chip.host.OUTV = 0

    def settle(self, n):
        for _ in range(n):
            self.step(*self.idle)

    def log(self, n_records):
        size = self.c.host["listener"]["record_bytes"]
        return bytes(self.chip.mem.data[:n_records * size])

    def never_drove(self):
        assert self.oe_seen == 0                            # no output enable on any cycle
        assert len(self.uo_seen) == 1, self.uo_seen         # the dedicated outputs never move either

    def clean_run(self):
        ch = self.chip
        assert all(t.LATE == 0 and t.OVR == 0 for t in ch.threads) and ch.ctrl.CONFLICT == 0


def uart_listen(trace, lead=40, tail=3000, **kw):
    c = scorec.compile_listener(spec_block(0), "tx=P5", **kw)
    ln = Listen(c, (IDLE, 1 << 5))
    for _ in range(lead):
        ln.step(IDLE, 1 << 5)
    for lvl in list(trace) + [1] * tail:
        ln.step(IDLE, (lvl & 1) << 5)
    return c, ln


def decode(c, ln, n):
    return ListenerDecoder(c.host["listener"]).decode_log(ln.log(n), n)


@pytest.mark.parametrize("seed", range(4))
def test_uart_clean_frames_no_violations_and_exact_bytes(seed):
    rng = random.Random(seed)
    data = bytes(rng.randrange(256) for _ in range(rng.randrange(2, 8)))
    enc = Codec(parse(spec_block(0))).encode_all([("data", b) for b in data])
    c, ln = uart_listen(enc.bus["tx"])
    recs = decode(c, ln, len(data))
    assert [r.clean for r in recs] == [True] * len(data)
    assert bytes(ln.chip.mem.data[0x400:0x400 + ln.chip.mem.streams[0].POS]) == data
    assert ln.statuses == [0] * len(data)
    gaps = [b.end_tick - a.end_tick for a, b in zip(recs, recs[1:])]
    assert all(g == 10 for g in gaps), gaps               # one character = 10 beats = 10 ruler ticks
    ln.never_drove()
    ln.clean_run()


def test_uart_listener_info_documents_the_record():
    c = scorec.compile_listener(spec_block(0), "tx=P5")
    h = c.host["listener"]
    assert h["record_bytes"] == 3 and h["fields"] == ["status", "ts_lo", "ts_hi"] and h["frame_beats"] == 10
    assert [(p["terminal"], p["beat"]) for p in h["positions"]] == [("bit(0)", 0), ("bit(1)", 9)]
    assert ".out" not in c.mas                              # no output pin table at all


def test_listener_refuses_pins_that_drive_and_i2c_is_a_documented_gap():
    with pytest.raises(CompileError) as e:
        scorec.compile_listener(spec_block(0), "tx=O8")
    assert e.value.code == "E-BIND"
    with pytest.raises(CompileError) as e:
        scorec.compile_listener(spec_block(1), "scl=P0 sda=P1")
    assert e.value.code == "E-UNSUPPORTED"


def test_uart_stop_bit_fault_gives_framing_violation_with_timestamp():
    st = [("terminal", 1, (0,))]                        # stop bit(1) sent as bit(0), by the stressed sender
    s = compile_stressed(spec_block(0), "sender", "tx=O8", st)
    _, tr1 = run_sender(s, bytes([0x81]))               # one character: exactly one framing error
    c, ln = uart_listen(tr1)
    recs = decode(c, ln, 1)
    assert len(recs) == 1 and len(recs[0].violations) == 1
    v = recs[0].violations[0]
    assert (v.code, v.terminal, v.beat_in_frame) == ("framing", "bit(1)", 9)
    start = next(i for i in range(1, len(tr1)) if tr1[i] == 0 and tr1[i - 1] == 1)
    expect = (40 + start) / UART_P + 9.5                # ruler ticks (= beats) from the chip start to the stop sample
    assert abs(v.beat - expect) <= 2, (v.beat, expect)
    assert ln.statuses == [recs[0].status] and recs[0].status & 0x10
    ln.never_drove()


def test_uart_start_bit_glitch_gives_grammar_violation_at_the_start_terminal():
    enc = Codec(parse(spec_block(0))).encode_all([("data", 0xFF)])
    tr = list(enc.bus["tx"])
    start = next(i for i in range(1, len(tr)) if tr[i] == 0 and tr[i - 1] == 1)
    for i in range(start + int(UART_P / 4), start + int(UART_P) + 2):      # the low lasts only a quarter of a bit
        tr[i] = 1
    c, ln = uart_listen(tr)
    recs = decode(c, ln, 1)
    assert [(v.code, v.terminal) for v in recs[0].violations] == [("grammar", "bit(0)")]
    assert recs[0].violations[0].beat_in_frame == 0
    ln.never_drove()


@pytest.mark.parametrize("ppm", [-20000, 20000])
def test_uart_tempo_inside_tolerance_stays_clean(ppm):
    s = compile_stressed(spec_block(0), "sender", "tx=O8", [("tempo", ppm)])
    _, tr = run_sender(s, bytes([0xA5, 0x3C]))
    c, ln = uart_listen(tr)
    assert all(r.clean for r in decode(c, ln, 2))
    assert ln.statuses == [0, 0]


# ---- Ethernet: crc and constant faults through the same record -------------------------------------------------------
def eth_trace(stresses, body):
    if stresses:
        c = compile_stressed(spec_block(3), "sender", "td=O0 tdn=O1", stresses, skip_periodic=True)
    else:
        c = scorec.compile_score(spec_block(3), "sender", "td=O0 tdn=O1", skip_periodic=True)
    chip = new_chip(c)
    for _ in range(20):
        chip.step(IDLE, 0)
    send_frame_go(chip, body)
    td = []
    for _ in range((64 + 8 * len(body) + 32 + 2 + 110) * 6 + 300):
        uo, uio, oe = chip.step(IDLE, 0)
        td.append(uio & 1)
    return td


def eth_listen(td):
    c = scorec.compile_listener(spec_block(3), "td=P2 tdn=P3", skip_periodic=True)
    ln = Listen(c, (IDLE, 0))
    ln.settle(60)
    for lvl in list(td) + [0] * 2500:
        ln.step(IDLE, (lvl & 1) << 2)
    return c, ln


def test_ethernet_clean_crc_fault_and_sfd_fault():
    body = bytes(range(1, 21))
    c, ln = eth_listen(eth_trace([], body))
    r = decode(c, ln, 1)
    assert len(r) == 1 and r[0].clean, r
    ln.never_drove()
    c, ln = eth_listen(eth_trace([("crc_init", 5)], body))
    assert [v.code for v in decode(c, ln, 1)[0].violations] == ["crc"]
    c, ln = eth_listen(eth_trace([("const", 7, 0)], body))
    assert [v.code for v in decode(c, ln, 1)[0].violations] == ["const"]


# ---- SPI mode 0: two data wires, chip-select framed -------------------------------------------------------------------
SPI_BIND = "sck=P1 cs_n=P2 mosi=P0 miso=P3"
IDLE_SPI = pins_in({1: 0, 2: 1, 0: 0, 3: 0})


def spi_listen(bus, period, tail=400):
    c = scorec.compile_listener(spec_block(2), SPI_BIND, follow_period=period)
    ln = Listen(c, IDLE_SPI)
    ln.settle(80)
    for i in range(len(bus["sck"])):
        ln.step(*pins_in({1: bus["sck"][i], 2: bus["cs_n"][i], 0: bus["mosi"][i], 3: bus["miso"][i]}))
    ln.settle(tail)
    return c, ln


def spi_bus(transfers, period):
    sc = parse(spec_block(2))
    out = {w: [] for w in ("sck", "cs_n", "mosi", "miso")}
    for pairs in transfers:
        ev = [("select",)]
        for a, b in pairs:
            ev += [("out", a), ("in", b)]
        ev.append(("deselect",))
        W = Codec(sc, rate=60e6 / period).encode_all(ev).bus
        for w in out:
            out[w] += list(W.wires[w])
        for w, v in (("sck", 0), ("cs_n", 1), ("mosi", 0), ("miso", 0)):
            out[w] += [v] * (2 * period)
    return out


@pytest.mark.parametrize("period", [60, 120])
@pytest.mark.parametrize("seed", range(3))
def test_spi_clean_transactions_two_wires(seed, period):
    rng = random.Random(seed)
    txs = [[(rng.randrange(256), rng.randrange(256)) for _ in range(rng.randrange(1, 4))] for _ in range(3)]
    c, ln = spi_listen(spi_bus(txs, period), period)
    recs = decode(c, ln, 3)
    assert [r.clean for r in recs] == [True] * 3
    assert [r.bits for r in recs] == [8 * len(t) for t in txs]
    h = c.host["listener"]
    streams = {w: bytes(ln.chip.mem.data[b:b + h["stream_len"]]) for w, b in h["stream_base"].items()}
    for t, p in zip(txs, split_spi_payload(recs, streams)):
        assert p["mosi"] == bytes(a for a, _ in t) and p["miso"] == bytes(b for _, b in t)
    assert ln.statuses == [0, 0, 0]
    assert all(b.end_tick > a.end_tick for a, b in zip(recs, recs[1:]))
    ln.never_drove()
    ln.clean_run()


def test_spi_transaction_ending_inside_a_byte_is_a_framing_violation():
    period = 60
    W = Codec(parse(spec_block(2)), rate=60e6 / period).encode_all(
        [("select",), ("out", 0xA5), ("in", 0x3C), ("out", 0x5A), ("in", 0xC3), ("deselect",)]).bus
    bus = {w: list(W.wires[w]) for w in ("sck", "cs_n", "mosi", "miso")}
    rises = [i for i in range(1, len(bus["sck"])) if bus["sck"][i] == 1 and bus["sck"][i - 1] == 0]
    cut = rises[10] + period // 2 + 5                    # cs_n rises after the 11th sck rise
    for w, v in (("sck", 0), ("cs_n", 1), ("mosi", 0), ("miso", 0)):
        bus[w][cut:] = [v] * (len(bus[w]) - cut)
    c, ln = spi_listen(bus, period)
    recs = decode(c, ln, 1)
    assert recs[0].bits == 11 and [v.code for v in recs[0].violations] == ["framing"]
    assert ln.statuses == [2]
    ln.never_drove()
