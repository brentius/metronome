"""Reference codec: random-frame encode -> decode round trips and independent decoders (code/tests/checkers)."""
import os
import random
import zlib

import protocols as ind
import pytest
from score import Codec, parse
from score.codec import Waveform, resolve

CLK = 60_000_000
SEEDS = range(12)


def split_events(events):
    return [e for e in events if e[0] != "tpidl"]


# ---- UART ----------------------------------------------------------------------------------------------------
@pytest.mark.parametrize("seed", SEEDS)
def test_uart_roundtrip_and_checker(examples, seed):
    rng = random.Random(seed)
    c = Codec(examples["uart"])
    data = bytes(rng.randrange(256) for _ in range(rng.randrange(1, 9)))
    enc = c.encode_all([("data", b) for b in data])
    r = c.decode("receiver", enc.bus)
    assert r.ok and r.events == [("data", b) for b in data]
    got = ind.uart_decode(enc.bus["tx"], CLK / 115200)
    assert [f.value for f in got] == list(data) and not any(f.framing_error for f in got)


@pytest.mark.parametrize("seed", range(4))
def test_uart_decodes_checker_stimulus(examples, seed):
    rng = random.Random(100 + seed)
    data = bytes(rng.randrange(256) for _ in range(5))
    tx = ind.uart_encode(data, CLK / 115200)
    r = Codec(examples["uart"]).decode("receiver", {"tx": tx})
    assert r.ok and r.events == [("data", b) for b in data]


@pytest.mark.parametrize("ppm", [-25000, -10000, 10000, 25000])
def test_uart_receiver_tolerates_clock_error(examples, ppm):
    """Sender clock off by up to 2.5 %: the receiver restarts on every start bit, so drift cannot accumulate."""
    data = bytes([0x00, 0xFF, 0xA5, 0x5A, 0x01, 0x80])
    rate = 115200 * (1 + ppm / 1e6)
    enc = Codec(examples["uart"], rate=rate).encode_all([("data", b) for b in data])
    r = Codec(examples["uart"]).decode("receiver", enc.bus)
    assert r.ok and r.events == [("data", b) for b in data]


def test_uart_detects_bad_stop_bit(examples):
    c = Codec(examples["uart"])
    enc = c.encode_all([("data", 0x12)])
    tx = list(enc.bus["tx"])
    start = next(i for i in range(1, len(tx)) if tx[i] == 0 and tx[i - 1] == 1)
    stop_mid = int(start + 9.5 * c.P)
    for i in range(int(start + 9 * c.P) + 2, int(start + 10 * c.P) - 1):
        tx[i] = 0                                     # stop bit forced low
    r = c.decode("receiver", {"tx": tx})
    assert not r.ok and any("violation" == e[0] for e in r.events)


# ---- I2C -----------------------------------------------------------------------------------------------------
def i2c_case(rng, my_addr):
    events, expect = [("start",)], [("S",)]
    nreq = rng.randrange(1, 4)
    for k in range(nreq):
        if k:
            events.append(("rstart",))
            expect.append(("Sr",))
        addr = my_addr if rng.random() < 0.7 else rng.randrange(128)
        rw = rng.randrange(2)
        match = addr == my_addr
        events += [("addr", addr), ("rw", rw)]
        events.append(("ack", 0 if match else 1))
        expect.append(("B", (addr << 1) | rw, match))
        if match:
            if rw == 0:
                for _ in range(rng.randrange(0, 4)):
                    d = rng.randrange(256)
                    events += [("data", d), ("dack", 0)]
                    expect.append(("B", d, True))
            else:
                n = rng.randrange(1, 4)
                for i in range(n):
                    d = rng.randrange(256)
                    last = i == n - 1
                    events += [("data", d), ("more", 1 if last else 0)]
                    expect.append(("B", d, not last))
    events.append(("stop",))
    expect.append(("P",))
    return events, expect


@pytest.mark.parametrize("seed", SEEDS)
def test_i2c_roundtrip_both_roles_and_checker(examples, seed):
    rng = random.Random(seed)
    my = rng.randrange(128)
    c = Codec(examples["i2c"], params={"my_addr": my})
    events, expect = i2c_case(rng, my)
    # the matching target computes ack itself: drop the ack events and let `= EXPR` produce them
    given = [e for e in events if e[0] != "ack"]
    enc = c.encode_all(given)
    for role in ("controller", "target"):
        r = c.decode(role, enc.bus)
        assert r.ok, r.notes
        assert r.events == events
    txs = ind.i2c_decode(enc.bus["scl"], enc.bus["sda"])
    assert len(txs) == 1 and txs[0].events == expect


def test_i2c_both_roles_drive_open_drain_wired_and(examples):
    my = 0x2A
    c = Codec(examples["i2c"], params={"my_addr": my})
    ev = [("start",), ("addr", my), ("rw", 0), ("data", 0x81), ("dack", 0), ("stop",)]
    enc = c.encode_all(ev)
    ctl, tgt, bus = enc.drives["controller"], enc.drives["target"], enc.bus
    # the target drives only when it owns a beat (ack beats): its waveform is mostly released
    assert tgt["sda"].count(0) > 0 and tgt["sda"].count(0) < ctl["sda"].count(0) + 400
    assert all(v in (0, None) for v in ctl["sda"] + tgt["sda"])      # open drain: never driven high
    for t in range(bus.n):
        drivers = [d["sda"][t] for d in (ctl, tgt)]
        assert bus["sda"][t] == (0 if 0 in drivers else 1)
    # NACK: the controller addresses someone else; nobody pulls sda low in the ack beat
    nack = c.encode_all([("start",), ("addr", my ^ 1), ("rw", 0), ("stop",)])
    assert nack.drives["target"]["sda"].count(0) == 0
    txs = ind.i2c_decode(nack.bus["scl"], nack.bus["sda"])
    assert txs[0].events[1] == ("B", ((my ^ 1) << 1), False)


def test_i2c_follower_tolerates_any_rate(examples):
    """Decode does not depend on the controller's rate beyond the nominal beat (target follows scl)."""
    my = 5
    events = [("start",), ("addr", my), ("rw", 1), ("ack", 0), ("data", 0xC3), ("more", 1), ("stop",)]
    for rate in (100e3, 99e3, 101e3):
        enc = Codec(examples["i2c"], params={"my_addr": my}, rate=rate).encode_all(events)
        r = Codec(examples["i2c"], params={"my_addr": my}).decode("target", enc.bus)
        assert r.ok and r.events == events


def test_i2c_abort_on_stop_and_start(examples):
    """`on stop_c -> bus` / `on start_c -> request`: an unexpected STOP or START abandons the production."""
    my = 0x10
    c = Codec(examples["i2c"], params={"my_addr": my})
    ev = [("start",), ("addr", 0x11), ("abort", "stop_c"),
          ("start",), ("addr", my), ("rw", 0), ("ack", 0), ("data", 0x55), ("dack", 0), ("stop",)]
    enc = c.encode_all(ev)
    r = c.decode("target", enc.bus)
    assert r.events == ev, r
    ev2 = [("start",), ("addr", 0x11), ("abort", "start_c"),
           ("addr", my), ("rw", 1), ("ack", 0), ("data", 0x55), ("more", 1), ("stop",)]
    enc2 = c.encode_all(ev2)
    r2 = c.decode("target", enc2.bus)
    assert r2.events == ev2, r2


# ---- SPI -----------------------------------------------------------------------------------------------------
@pytest.mark.parametrize("seed", SEEDS)
def test_spi_duplex_roundtrip_and_checker(examples, seed):
    rng = random.Random(seed)
    c = Codec(examples["spi"])
    transfers, events = [], []
    for _ in range(rng.randrange(1, 4)):
        n = rng.randrange(1, 5)
        mo = [rng.randrange(256) for _ in range(n)]
        mi = [rng.randrange(256) for _ in range(n)]
        transfers.append((mo, mi))
        events.append(("select",))
        for a, b in zip(mo, mi):
            events += [("out", a), ("in", b)]
        events.append(("deselect",))
    enc = c.encode_all(events)
    for role in ("controller", "peripheral"):
        r = c.decode(role, enc.bus)
        assert r.ok, r.notes
        assert r.events == events
    b = enc.bus
    assert ind.spi_decode(b["sck"], b["mosi"], b["miso"], b["cs_n"], mode=0) == transfers
    # each role drives only its own wires
    assert set(enc.drives["peripheral"]["miso"]) - {None} <= {0, 1}
    assert all(v is None for v in enc.drives["controller"]["miso"])
    assert all(v is None for v in enc.drives["peripheral"]["sck"])


# ---- 10BASE-T ------------------------------------------------------------------------------------------------
@pytest.mark.parametrize("n", [1, 5, 46, 60, 100])
def test_ethernet_roundtrip_fcs_and_checker(examples, n):
    rng = random.Random(n)
    body = bytes(rng.randrange(256) for _ in range(n))
    c = Codec(examples["ethernet"])
    enc = c.encode_all([("body", body)])
    r = c.decode("receiver", enc.bus)
    assert r.ok, r.notes
    d = dict((e[0], e[1] if len(e) > 1 else None) for e in r.events)
    assert d["body"] == body and d["fcs"] == zlib.crc32(body)
    frames = ind.eth_decode(enc.bus["td"], 6.0)
    assert len(frames) == 1 and frames[0].data == body and frames[0].fcs_ok
    # mirror pair carries the complement
    assert all(a + b == 1 for a, b in zip(enc.bus["td"], enc.bus["tdn"]))


def test_ethernet_two_frames_with_gap(examples):
    c = Codec(examples["ethernet"])
    b1, b2 = os.urandom(20), os.urandom(33)
    enc = c.encode_all([("body", b1), ("body", b2)])
    r = c.decode("receiver", enc.bus)
    assert r.ok and [e[1] for e in r.events if e[0] == "body"] == [b1, b2]
    assert [f.data for f in ind.eth_decode(enc.bus["td"], 6.0)] == [b1, b2]


@pytest.mark.parametrize("n", [3, 40, 64])
def test_ethernet_decodes_checker_stimulus(examples, n):
    body = os.urandom(n)
    td = ind.eth_encode(body)
    r = Codec(examples["ethernet"]).decode("receiver", {"td": td})
    assert r.ok, r.notes
    assert [e[1] for e in r.events if e[0] == "body"] == [body]


def test_ethernet_detects_bad_fcs(examples):
    c = Codec(examples["ethernet"])
    body = os.urandom(30)
    enc = c.encode_all([("body", body), ("fcs", zlib.crc32(body) ^ 1)])
    r = c.decode("receiver", enc.bus)
    assert not r.ok and any("fcs" in n or "crc" in n for n in r.notes)
    td = ind.eth_decode(enc.bus["td"], 6.0)
    assert td and not td[0].fcs_ok


def test_ethernet_recovered_clock_tolerates_drift(examples):
    """Sender 1.5 % fast or slow: edges inside the 33..67 % window re-align the receiver every beat."""
    body = os.urandom(50)
    for rate in (10e6 * 0.985, 10e6 * 1.015):
        enc = Codec(examples["ethernet"], rate=rate).encode_all([("body", body)])
        r = Codec(examples["ethernet"]).decode("receiver", enc.bus)
        assert r.ok and [e[1] for e in r.events if e[0] == "body"] == [body], rate


# ---- tether --------------------------------------------------------------------------------------------------
def tether_events(rng, n=None):
    n = rng.randrange(0, 12) if n is None else n
    payload = bytes(rng.choice([0x00, 0xFF, 0xFF, rng.randrange(256)]) for _ in range(n))
    return [("mark",), ("mark",), ("addr", rng.randrange(256)), ("len", n), ("payload", payload)]


@pytest.mark.parametrize("seed", SEEDS)
def test_tether_roundtrip(examples, seed):
    rng = random.Random(seed)
    c = Codec(examples["tether"])
    ev = tether_events(rng) + tether_events(rng, 0)
    enc = c.encode_all(ev)
    for role in ("host", "node"):
        r = c.decode(role, enc.bus)
        assert r.ok, r.notes
        got = [e for e in r.events if e[0] not in ("check", "ack")]
        assert got == ev
        assert [e for e in r.events if e[0] == "ack"] == [("ack", 0), ("ack", 0)]
    # the acknowledge slot is driven by the node only, the rest by the host only
    assert any(v == 0 for v in enc.drives["node"]["d"])
    assert all(v is None for v in enc.drives["host"]["d"][-1:])
    assert not any(a == 0 and b == 0 for a, b in zip(enc.drives["host"]["d"], enc.drives["node"]["d"]))


def test_tether_stuffing_breaks_runs(examples):
    c = Codec(examples["tether"])
    enc = c.encode_all(tether_events(random.Random(1), 0)[:2] + [("addr", 0xFF), ("len", 4),
                                                              ("payload", b"\xff\xff\xff\xff")])
    nbeats = sum(1 for p in enc.plan if p.kind == "beat")
    # 2 marks + 8+8+32 data + 8 crc + 1 ack = 59 data beats; stuffing adds beats
    assert nbeats > 2 + 8 + 8 + 32 + 8 + 1
    assert Codec(examples["tether"]).decode("node", enc.bus).ok


def test_tether_crc_error_detected(examples):
    c = Codec(examples["tether"])
    ev = [("mark",), ("mark",), ("addr", 3), ("len", 1), ("payload", b"\x42"), ("check", 0x55)]
    enc = c.encode_all(ev)
    r = c.decode("node", enc.bus)
    assert not r.ok and any("c8" in n for n in r.notes)


# ---- projection ----------------------------------------------------------------------------------------------
def test_projection_i2c(examples):
    from score import project
    p_t = project(examples["i2c"], "target")
    p_c = project(examples["i2c"], "controller")
    assert "ack" in p_t.computed and "ack" in p_c.host_rx
    assert "addr" in p_c.host_tx and "addr" in p_t.host_rx
    assert "data" in p_t.host_tx and "data" in p_t.host_rx          # read data it sends, write data it receives
    acts = {n.info.get("name"): n.info.get("action") for n in p_t.root.walk() if n.kind == "sym"}
    assert acts["start"] == "expect" and acts["stop"] == "expect"
    acts = {n.info.get("name"): n.info.get("action") for n in p_c.root.walk() if n.kind == "sym"}
    assert acts["start"] == "transmit"


def test_projection_spi_duplex(examples):
    from score import project
    c, p = project(examples["spi"], "controller"), project(examples["spi"], "peripheral")
    assert c.host_tx == ["out"] and c.host_rx == ["in"]
    assert p.host_tx == ["in"] and p.host_rx == ["out"]


def test_projection_ethernet_crc(examples):
    from score import project
    s, r = project(examples["ethernet"], "sender"), project(examples["ethernet"], "receiver")
    assert "fcs" in s.computed and "fcs" in r.checked
    assert s.host_tx == ["body"] and r.host_rx == ["body"]


def test_tether_absent_node_reads_as_nack(examples):
    """Differential coding on an open-drain wire: acknowledge = a level change from the released bus (idle
    high), so a node that does not pull the wire low leaves the bus high, which reads as no change."""
    c = Codec(examples["tether"])
    ev = [("mark",), ("mark",), ("addr", 9), ("len", 0), ("payload", b""), ("ack", 1)]
    enc = c.encode_all(ev)
    assert all(v is None for v in enc.drives["node"]["d"])          # nothing pulls the wire low
    r = c.decode("host", enc.bus)
    assert r.ok and ("ack", 1) in r.events


@pytest.mark.parametrize("name,role", [("uart", "receiver"), ("i2c", "target"), ("spi", "peripheral"),
                                       ("ethernet", "receiver"), ("tether", "node")])
def test_idle_bus_decodes_to_nothing(examples, name, role):
    c = Codec(examples[name], params={"my_addr": 1})
    enc = c.encode_all([])
    r = c.decode(role, enc.bus)
    assert r.ok and r.events == []


@pytest.mark.parametrize("ppm", [-15000, 15000])
def test_tether_wrapped_window_tolerates_drift(examples, ppm):
    """Differential data edges sit on beat boundaries: the 80 %..20 % window re-aligns the node on each of them."""
    ev = [("mark",), ("mark",), ("addr", 0xA5), ("len", 6), ("payload", bytes([0x00, 0xFF, 0x12, 0x80, 0x01, 0xFE]))]
    enc = Codec(examples["tether"], rate=500e3 * (1 + ppm / 1e6)).encode_all(ev)
    r = Codec(examples["tether"]).decode("node", enc.bus)
    assert r.ok, r.notes
    assert [e for e in r.events if e[0] not in ("check", "ack")] == ev
