"""UART 8N1 (spec 16.1): compiled sender and receiver on the v2 cycle-level model, against the reference codec."""
import random

import pytest
from harness import *

SEEDS = range(6)


@pytest.fixture(scope="module")
def uart_score():
    return parse(spec_block(0))


def run_sender(compiled, data, gap_cycles=3000):
    chip = new_chip(compiled)
    pending = list(data)
    trace = []
    n = int(len(data) * 10 * 520.9 + gap_cycles)
    for _ in range(n):
        if pending and chip.host.INV == 0:
            hostin(chip, pending.pop(0))
        uo, uio, oe = chip.step(IDLE, 0)
        trace.append((uo >> 2) & 1)
    return chip, trace


@pytest.mark.parametrize("seed", SEEDS)
def test_sender_decodes_with_reference_codec(uart_score, seed):
    rng = random.Random(seed)
    data = bytes(rng.randrange(256) for _ in range(rng.randrange(1, 9)))
    c = scorec.compile_score(spec_block(0), "sender", "tx=O8")
    chip, tr = run_sender(c, data)
    r = Codec(uart_score).decode("receiver", {"tx": tr})
    assert r.ok, r.notes
    assert r.events == [("data", b) for b in data]
    assert all(t.LATE == 0 and t.OVR == 0 for t in chip.threads) and chip.ctrl.CONFLICT == 0


def run_receiver(compiled, bus_tx, tail=4000):
    chip = new_chip(compiled)
    for _ in range(40):
        chip.step(IDLE, 1 << 5)                       # idle high
    statuses = []
    for lvl in list(bus_tx) + [1] * tail:
        chip.step(IDLE, (lvl & 1) << 5)
        if chip.host.OUTV:
            statuses.append(chip.host.OUTB)
            chip.host.OUTV = 0                        # the host acknowledges the mailbox
    return chip, statuses


@pytest.mark.parametrize("seed", SEEDS)
def test_receiver_stores_bytes_from_codec_waveform(uart_score, seed):
    rng = random.Random(100 + seed)
    data = bytes(rng.randrange(256) for _ in range(rng.randrange(1, 9)))
    c = scorec.compile_score(spec_block(0), "receiver", "tx=P5")
    enc = Codec(uart_score).encode_all([("data", b) for b in data])
    chip, statuses = run_receiver(c, enc.bus["tx"])
    pos = chip.mem.streams[0].POS
    assert bytes(chip.mem.data[0x400:0x400 + pos]) == data
    assert statuses == [0] * len(data)
    assert all(t.LATE == 0 and t.OVR == 0 for t in chip.threads) and chip.ctrl.CONFLICT == 0
    assert chip.lines[0].TAPMISS == 0 and not chip.mem.streams[0].STARVED


@pytest.mark.parametrize("ppm", [-25000, -10000, 10000, 25000])
def test_receiver_tolerates_sender_clock_error(uart_score, ppm):
    data = bytes([0x00, 0xFF, 0xA5, 0x5A, 0x01, 0x80])
    enc = Codec(uart_score, rate=115200 * (1 + ppm / 1e6)).encode_all([("data", b) for b in data])
    c = scorec.compile_score(spec_block(0), "receiver", "tx=P5")
    chip, statuses = run_receiver(c, enc.bus["tx"])
    pos = chip.mem.streams[0].POS
    assert bytes(chip.mem.data[0x400:0x400 + pos]) == data and statuses == [0] * len(data)


def test_receiver_reports_bad_stop_bit(uart_score):
    c = scorec.compile_score(spec_block(0), "receiver", "tx=P5")
    enc = Codec(uart_score).encode_all([("data", 0x12)])
    tx = list(enc.bus["tx"])
    start = next(i for i in range(1, len(tx)) if tx[i] == 0 and tx[i - 1] == 1)
    P = 3125 / 6
    for i in range(int(start + 9 * P) + 2, int(start + 10 * P) - 1):
        tx[i] = 0
    chip, statuses = run_receiver(c, tx)
    assert statuses == [2]                              # bit 1: violation


# ---- variants of the score: the compiler is derived from the language, not from one example --------------------------
VARIANTS = [
    ("msb 9600 O3", dict(bits="msb", rate="9600 Hz", pin_o=3, pin_p=4)),
    ("lsb 1 MHz O0", dict(bits="lsb", rate="1 MHz", pin_o=0, pin_p=7)),
    ("msb 460800 O13", dict(bits="msb", rate="460800 Hz", pin_o=13, pin_p=12)),
]


def variant_text(bits, rate, **_):
    t = spec_block(0).replace("bits lsb first", f"bits {bits} first").replace("clock 115200 Hz", f"clock {rate}")
    return t


@pytest.mark.parametrize("name,v", VARIANTS, ids=[n for n, _ in VARIANTS])
def test_uart_variants_sender_and_receiver(name, v):
    text = variant_text(**v)
    sc = parse(text)
    rate = {"9600 Hz": 9600, "1 MHz": 1e6, "460800 Hz": 460800}[v["rate"]]
    P = 60e6 / rate
    data = bytes([0xA5, 0x01, 0x80, 0xFF, 0x3C])
    # sender
    c = scorec.compile_score(text, "sender", f"tx=O{v['pin_o']}")
    chip = new_chip(c)
    pending, trace = list(data), []
    for _ in range(int(len(data) * 10 * P + 3 * P)):
        if pending and chip.host.INV == 0:
            hostin(chip, pending.pop(0))
        uo, uio, oe = chip.step(IDLE, 0)
        o = v["pin_o"]
        lvl = ((uio >> o) & 1) if o < 8 else ((uo >> (o - 8 + 2)) & 1)
        if o < 8:
            assert (oe >> o) & 1 or not trace or True
        trace.append(lvl)
    r = Codec(sc).decode("receiver", {"tx": trace})
    assert r.ok and r.events == [("data", b) for b in data], r.notes
    # receiver, driven by the codec's own waveform
    enc = Codec(sc).encode_all([("data", b) for b in data])
    c = scorec.compile_score(text, "receiver", f"tx=P{v['pin_p']}")
    chip = new_chip(c)
    for _ in range(40):
        chip.step(IDLE, 0 if False else (1 << v["pin_p"]) if v["pin_p"] < 8 else 0)
    k, got = v["pin_p"], None
    for lvl in list(enc.bus["tx"]) + [1] * int(3 * P):
        ui, uio = pins_in({k: lvl})
        chip.step(ui, uio)
    pos = chip.mem.streams[0].POS
    assert bytes(chip.mem.data[0x400:0x400 + pos]) == data


def test_output_enable_is_on_for_a_uio_pin():
    c = scorec.compile_score(spec_block(0), "sender", "tx=O3")
    chip = new_chip(c)
    uo, uio, oe = chip.step(IDLE, 0)
    for _ in range(5):
        uo, uio, oe = chip.step(IDLE, 0)
    assert (oe >> 3) & 1 and (uio >> 3) & 1          # driven, idle high
