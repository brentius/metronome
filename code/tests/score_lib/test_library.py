"""Library-wide checks: every score in code/score/lib parses and passes the static checks, the compile status of every role
is pinned (so wiki/PROTOCOL_LIBRARY.md cannot drift from what scorec does), and the language gaps the library ran into
are reproduced as small scores."""
import pytest
from libharness import *
from score import check, parse

NAMES = ["uart_8n1", "ws2812", "dmx512", "wiegand26", "hdlc", "onewire", "swd", "jtag", "mdio", "spi_mode0", "i2c",
         "pattern_gen", "logic_analyser"]


@pytest.mark.parametrize("name", NAMES)
def test_every_library_score_parses_and_checks(name):
    assert [str(d) for d in check(parse(lib_text(name))) if d.code.startswith("E-")] == []


def test_the_library_directory_has_no_unlisted_score():
    from harness import ROOT
    assert sorted(p.stem for p in (ROOT / "code/score/lib").glob("*.score")) == sorted(NAMES)


# score, role, bind, extra kwargs -> None when it compiles, else (error code, fragment of the message)
COMPILE = [
    ("ws2812", "sender", "din=O8", {}, None),
    ("ws2812", "led", "din=P1", {}, ("E-UNSUPPORTED", "exactly one sample point on one wire")),
    ("dmx512", "sender", "dmx=O8", {}, None),
    ("dmx512", "fixture", "dmx=P1", {}, ("E-UNSUPPORTED", "receive of symbol 'brk' as a grammar terminal")),
    ("wiegand26", "reader", "d0=O8 d1=O9", {"rate_hz": 20000}, None),
    ("wiegand26", "panel", "d0=P1 d1=P2", {}, ("E-UNSUPPORTED", "checking parity field 'po' is not compiled")),
    ("hdlc", "sender", "clk=O8 d=O9", {}, ("E-UNSUPPORTED", "stuff")),  # refused since 2026-11-16 (was a silent miscompile)
    ("hdlc", "receiver", "clk=P1 d=P2", {"follow_period": 240}, ("E-UNSUPPORTED", "stuff")),  # stuffing refusal now precedes the follower-template refusal
    ("onewire", "master", "dq=P0/O0", {}, ("E-UNSUPPORTED", "most significant bit first")),
    ("onewire", "device", "dq=P0/O0", {}, ("E-UNSUPPORTED", "most significant bit first")),
    ("swd", "host", "swclk=O8 swdio=P0/O0", {}, ("E-UNSUPPORTED", "parity fields are not compiled")),
    ("swd", "target", "swclk=P1 swdio=P0/O0", {"follow_period": 240}, ("E-UNSUPPORTED", "parity fields are not compiled")),
    ("mdio", "sta", "mdc=O8 mdio=P0/O0", {}, ("E-UNSUPPORTED", "START REQUEST")),
    ("mdio", "phy", "mdc=P1 mdio=P0/O0", {"follow_period": 240}, ("E-UNSUPPORTED", "START REQUEST")),
    ("jtag", "probe", "tck=O8 tms=O9 tdi=O10 tdo=P0", {}, ("E-UNSUPPORTED", "'dup' in a sender frame")),
    ("jtag", "device", "tck=P1 tms=P2 tdi=P3 tdo=O8", {"follow_period": 240}, ("E-UNSUPPORTED", "follower template")),
    ("spi_mode0", "controller", "sck=O8 cs_n=O9 mosi=O10 miso=P1", {}, None),
    ("spi_mode0", "peripheral", "sck=P0 mosi=P1 cs_n=P2 miso=O8", {}, None),
    ("i2c", "controller", "scl=P0/O0 sda=P1/O1", {}, None),
    ("i2c", "target", "scl=P0 sda=P1/O1", {"follow_period": 2400, "params": {"my_addr": 0x42}}, None),
    ("pattern_gen", "generator", "pin=O8", {"rate_hz": 1e6}, None),
    ("logic_analyser", "analyser", "pin=P5", {"rate_hz": 1e6}, None),
]


@pytest.mark.parametrize("name,role,bind,kw,want", COMPILE, ids=[f"{c[0]}/{c[1]}" for c in COMPILE])
def test_compile_status_is_pinned(name, role, bind, kw, want):
    import scorec
    if want is None:
        c = scorec.compile_score(lib_text(name), role, bind, **kw)
        assert c.image and not c.errors
    else:
        with pytest.raises(scorec.CompileError) as e:
            scorec.compile_score(lib_text(name), role, bind, **kw)
        assert e.value.code == want[0] and want[1] in str(e.value), str(e.value)[:300]


# ---- language gaps, reproduced ------------------------------------------------------------------------------
GAP = """protocol t
roles a, b
wire w out push-pull idle low by a
wire v out push-pull idle low by a
clock 1 MHz
  a: generated
  b: generated
symbols
  bit(m, n) w "m" v "n"
bits msb first
grammar
  f = %s
"""


def codes(grammar):
    return [d.code for d in check(parse(GAP % grammar)) if d.code.startswith("E-")]


def test_gap_two_data_bits_per_beat_from_one_owner_is_rejected():
    """QSPI nibbles, JTAG TMS+TDI, a parallel pattern bus: `||` needs two owners (spec 7.8), so one owner cannot put two
    independent data bits in one beat."""
    assert codes("{ p:u8 by a || q:u8 by a }*") == ["E-DUPLEX"]


def test_gap_leading_parity_over_later_fields_is_rejected():
    """Wiegand 26's first bit is an even parity over the bits that follow: fields are L-attributed (spec 7.5)."""
    assert codes("pe: parity even over p..q p:u8 q:u8") == ["E-NAMES", "E-NAMES"]


NRZI = """protocol nrzi
roles sender, receiver
wire tx out push-pull idle high by sender
clock 1 MHz
  sender: generated
  receiver: started by tx fall
  tolerance 3%
symbols
  bit(d) tx "d" sample tx at 50%
bits lsb first, differential on 0
grammar
  line = f*
  f = bit(0) data:u8 bit(1) gap 0 beats
"""


def test_compiled_sender_refuses_differential_coding():
    """scorec refuses `differential` with E-UNSUPPORTED (2026-11-16) instead of silently sending plain NRZ."""
    import scorec
    with pytest.raises(scorec.CompileError) as e:
        scorec.compile_score(NRZI, "sender", "tx=O8")
    assert e.value.code == "E-UNSUPPORTED" and "differential" in str(e.value)
