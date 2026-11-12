"""SPI mode 0 (spec 16.3): compiled controller and peripheral on the v2 cycle-level model vs the reference codec."""
import random

import pytest
from harness import *

CPU = 60       # chip cycles per SCK period at 1 MHz


@pytest.fixture(scope="module")
def spi_score():
    return parse(spec_block(2))


def run_controller(mo, mi, cycles=None):
    """Chip = controller (SCK O8, CS_N O9, MOSI O10, MISO P1).  A behavioural mode-0 peripheral (in Python) drives
    MISO from the chip's SCK/CS_N: first bit when CS_N falls, next bit after every SCK fall."""
    c = scorec.compile_score(spec_block(2), "controller", "sck=O8 cs_n=O9 mosi=O10 miso=P1")
    chip = new_chip(c)
    for _ in range(20):
        chip.step(IDLE, 0)
    chip.backdoor_write(HM["DATA_BASE"], bytes(mo))
    stream_reg(chip, 0, "LEN", len(mo), 2)
    stream_reg(chip, 1, "LEN", 992, 2)
    stream_rewind(chip, 0)
    stream_rewind(chip, 1)
    for _ in range(40):
        chip.step(IDLE, 0)
    hostin(chip, 1)
    bits = [(b >> (7 - i)) & 1 for b in mi for i in range(8)]
    n = (len(mo) * 8 + 8) * CPU + 600
    sck, cs, mosi, miso = [], [], [], []
    k, prev_sck, prev_cs, cur = 0, 0, 1, 0
    for _ in range(n):
        uo, uio, oe = chip.step(IDLE, cur << 1)
        s, c_, m_ = (uo >> 6) & 1, (uo >> 7) & 1, (uo >> 8) & 1
        # O8 = uo_out[2], O9 = uo_out[3], O10 = uo_out[4]
        s, c_, m_ = (uo >> 2) & 1, (uo >> 3) & 1, (uo >> 4) & 1
        if prev_cs == 1 and c_ == 0:
            k = 0
            cur = bits[0] if bits else 0
        elif c_ == 0 and prev_sck == 1 and s == 0:
            k += 1
            cur = bits[k] if k < len(bits) else 0
        prev_sck, prev_cs = s, c_
        sck.append(s); cs.append(c_); mosi.append(m_); miso.append(cur)
    return c, chip, {"sck": sck, "cs_n": cs, "mosi": mosi, "miso": miso}


@pytest.mark.parametrize("seed", range(6))
def test_controller_roundtrip_with_codec_decode(spi_score, seed):
    rng = random.Random(seed)
    n = rng.randrange(1, 5)
    mo = [rng.randrange(256) for _ in range(n)]
    mi = [rng.randrange(256) for _ in range(n)]
    c, chip, bus = run_controller(mo, mi)
    want = [("select",)]
    for a, b in zip(mo, mi):
        want += [("out", a), ("in", b)]
    want.append(("deselect",))
    r = Codec(spi_score).decode("peripheral", bus)
    assert r.ok, r.notes
    assert r.events == want
    pos = chip.mem.streams[1].POS
    assert bytes(chip.mem.data[0x400:0x400 + pos])[:n] == bytes(mi)
    assert all(t.LATE == 0 and t.OVR == 0 for t in chip.threads) and chip.ctrl.CONFLICT == 0
    assert chip.lines[0].TAPMISS == 0


@pytest.mark.parametrize("period", [60, 120])
@pytest.mark.parametrize("seed", range(2))
def test_peripheral_full_duplex_follows_mode0_controller(spi_score, seed, period):
    rng = random.Random(100 + seed)
    outgoing = bytes(rng.randrange(256) for _ in range(rng.randrange(1, 4)))
    incoming = bytes(rng.randrange(256) for _ in outgoing)
    c = scorec.compile_score(spec_block(2), "peripheral", "sck=P1 cs_n=P2 mosi=P0 miso=O8",
                             follow_period=period)
    chip = new_chip(c)
    # The peripheral owns the stream contents; an external controller begins a
    # transaction with CS_N high and SCK low, then asserts CS_N before clocking.
    chip.backdoor_write(HM["DATA_BASE"], outgoing)
    stream_reg(chip, 0, "LEN", len(outgoing), 2)
    stream_reg(chip, 1, "LEN", 0x3E0, 2)
    stream_rewind(chip, 0)
    stream_rewind(chip, 1)
    idle_ui, idle_uio = pins_in({1: 0, 2: 1, 0: 0})
    for _ in range(80):
        chip.step(idle_ui, idle_uio)

    frame_events = [("select",)]
    for a, b in zip(incoming, outgoing):
        frame_events.extend([("out", a), ("in", b)])
    frame_events.append(("deselect",))
    peer = Codec(spi_score, rate=60e6 / period)
    first = peer.encode("controller", frame_events, lead=4, tail=4)
    second = peer.encode("controller", frame_events, lead=4, tail=4)
    bus = {"sck": [], "cs_n": [], "mosi": [], "miso": []}
    starve_cycles = []

    def drive(wave):
        for i in range(wave.n):
            sck = wave.wires["sck"][i]
            cs_n = wave.wires["cs_n"][i]
            mosi = wave.wires["mosi"][i]
            ui, uio = pins_in({1: sck, 2: cs_n, 0: mosi})
            uo, _, _ = chip.step(ui, uio)
            if chip.mem.streams[0].STARVED and not starve_cycles:
                starve_cycles.append(len(bus["sck"]))
            bus["sck"].append(sck)
            bus["cs_n"].append(cs_n)
            bus["mosi"].append(mosi)
            bus["miso"].append((uo >> 2) & 1)  # O8 = uo_out[2]

    drive(first)
    # Separate transactions with an idle-high select interval while preserving
    # the TX stream image; the peripheral's CS thread rewinds its stream.
    for _ in range(2 * period):
        uo, _, _ = chip.step(idle_ui, idle_uio)
        bus["sck"].append(0); bus["cs_n"].append(1); bus["mosi"].append(0)
        bus["miso"].append((uo >> 2) & 1)
    drive(second)

    decoded = Codec(spi_score, rate=60e6 / period).decode("controller", bus)
    want = []
    for _ in range(2):
        want.extend(frame_events)
    assert decoded.ok, decoded.notes
    assert decoded.events == want
    pos = chip.mem.streams[1].POS
    got_rx = bytes(chip.mem.data[0x400:0x400 + pos])
    assert got_rx == incoming, f"RX={got_rx.hex()} expected={incoming.hex()} POS={pos}"
    assert all(t.LATE == 0 and t.OVR == 0 for t in chip.threads) and chip.ctrl.CONFLICT == 0
    assert bus["cs_n"][-period:] == [1] * period and bus["miso"][-period:] == [0] * period, (
        f"MISO did not return to idle low after CS_N rose: {bus['miso'][-period:]}"
    )
    starved = [i for i, s in enumerate(chip.mem.streams) if s.STARVED]
    assert not starved and chip.lines[0].TAPMISS == 0, (
        f"STARVED streams={starved}, first cycle={starve_cycles}; POS={[s.POS for s in chip.mem.streams]}, "
        f"LEN={[s.LEN for s in chip.mem.streams]}, TAPMISS={chip.lines[0].TAPMISS}; decoded={decoded.events}"
    )


def test_peripheral_aborts_to_idle_when_cs_rises_while_sck_high(spi_score):
    period = CPU
    c = scorec.compile_score(spec_block(2), "peripheral", "sck=P1 cs_n=P2 mosi=P0 miso=O8",
                             follow_period=period)
    chip = new_chip(c)
    chip.backdoor_write(HM["DATA_BASE"], b"\xff")
    stream_reg(chip, 0, "LEN", 1, 2)
    stream_reg(chip, 1, "LEN", 0x3E0, 2)
    stream_rewind(chip, 0)
    stream_rewind(chip, 1)

    def tick(sck, cs_n, mosi=0):
        ui, uio = pins_in({1: sck, 2: cs_n, 0: mosi})
        uo, _, _ = chip.step(ui, uio)
        return (uo >> 2) & 1

    for _ in range(80):
        tick(0, 1)
    selected = [tick(0, 0) for _ in range(period)]
    assert selected[-8:] == [1] * 8, f"peripheral did not stage first 1 bit: {selected[-8:]}"
    for _ in range(period // 2):
        tick(1, 0)
    abort_trace = [tick(1, 1) for _ in range(period)]  # CS_N rises while SCK remains high
    assert abort_trace[10:] == [0] * (period - 10), (
        f"peripheral failed to return MISO to idle low after CS_N rose during SCK high; "
        f"MISO={abort_trace}, L1.RUN={chip.lines[1].RUN}, "
        f"L1.SYM={chip.lines[1].COMMITTED}/STAGED={chip.lines[1].STAGED}, "
        f"threads={[ (t.READY, t.RUNNING, t.OVR, t.LATE) for t in chip.threads[:4] ]}"
    )




def run_peripheral(mo, mi, rate=1e6, nbytes=None):
    """Chip = peripheral (SCK P0, MOSI P1, CS_N P2, MISO O8).  The reference codec supplies the controller's wires."""
    sc = parse(spec_block(2))
    events = [("select",)]
    for a, b in zip(mo, mi):
        events += [("out", a), ("in", b)]
    events.append(("deselect",))
    enc = Codec(sc, rate=rate).encode_all(events)
    c = scorec.compile_score(spec_block(2), "peripheral", "sck=P0 mosi=P1 cs_n=P2 miso=O8")
    chip = new_chip(c)
    chip.backdoor_write(HM["DATA_BASE"], bytes(mi))
    stream_reg(chip, 0, "LEN", len(mi) + 2, 2)
    stream_rewind(chip, 0)
    for _ in range(60):
        chip.step(IDLE, 0b100)                       # CS_N high
    miso = []
    bus = enc.bus
    for t in range(bus.n):
        uio = (bus["sck"][t]) | (bus["mosi"][t] << 1) | (bus["cs_n"][t] << 2)
        uo, _, _ = chip.step(IDLE, uio)
        miso.append((uo >> 2) & 1)
    for _ in range(200):
        chip.step(IDLE, 0b100)
    return c, chip, enc, miso


def sample_at_rises(bus, trace, delay=2):
    sck = bus["sck"]
    return [trace[t - delay] for t in range(1, bus.n) if sck[t] and not sck[t - 1]]


@pytest.mark.parametrize("seed", range(6))
def test_peripheral_miso_and_mosi_at_nominal_rate(seed):
    rng = random.Random(10 + seed)
    n = rng.randrange(1, 5)
    mo = [rng.randrange(256) for _ in range(n)]
    mi = [rng.randrange(256) for _ in range(n)]
    c, chip, enc, miso = run_peripheral(mo, mi)
    got = sample_at_rises(enc.bus, miso)
    want = [(b >> (7 - i)) & 1 for b in mi for i in range(8)]
    assert got == want
    pos = chip.mem.streams[1].POS
    assert bytes(chip.mem.data[0x400:0x400 + pos]) == bytes(mo)
    assert all(t.LATE == 0 and t.OVR == 0 for t in chip.threads) and chip.ctrl.CONFLICT == 0
    assert chip.lines[0].TAPMISS == 0 and chip.lines[1].TAPMISS == 0


@pytest.mark.parametrize("rate", [0.5e6, 1.7e6, 2.5e6])
def test_peripheral_follows_any_clock_rate(rate):
    mo, mi = [0xA5, 0x3C, 0xFF], [0x96, 0x0F, 0xE1]
    c, chip, enc, miso = run_peripheral(mo, mi, rate=rate)
    got = sample_at_rises(enc.bus, miso)
    assert got == [(b >> (7 - i)) & 1 for b in mi for i in range(8)]
    pos = chip.mem.streams[1].POS
    assert bytes(chip.mem.data[0x400:0x400 + pos]) == bytes(mo)


def test_peripheral_two_transactions_rewinds_between():
    sc = parse(spec_block(2))
    mo1, mo2, mi = [0x12, 0x34], [0xAB, 0xCD], [0x5A, 0xC3]
    events = [("select",)]
    for a, b in zip(mo1, mi):
        events += [("out", a), ("in", b)]
    events += [("deselect",), ("select",)]
    for a, b in zip(mo2, mi):
        events += [("out", a), ("in", b)]
    events.append(("deselect",))
    enc = Codec(sc).encode_all(events)
    c = scorec.compile_score(spec_block(2), "peripheral", "sck=P0 mosi=P1 cs_n=P2 miso=O8")
    chip = new_chip(c)
    chip.backdoor_write(HM["DATA_BASE"], bytes(mi))
    stream_reg(chip, 0, "LEN", 4, 2)
    stream_rewind(chip, 0)
    for _ in range(60):
        chip.step(IDLE, 0b100)
    miso, bus = [], enc.bus
    for t in range(bus.n):
        uo, _, _ = chip.step(IDLE, bus["sck"][t] | (bus["mosi"][t] << 1) | (bus["cs_n"][t] << 2))
        miso.append((uo >> 2) & 1)
    want = [(b >> (7 - i)) & 1 for b in mi for i in range(8)] * 2
    assert sample_at_rises(bus, miso) == want
    pos = chip.mem.streams[1].POS
    assert pos == 2 and bytes(chip.mem.data[0x400:0x402]) == bytes(mo2)     # the receive stream restarts at each select
    assert miso[-1] == 0                                                    # output returns to idle
