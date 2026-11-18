"""Language extensions, SPEC_V2_SCORE.md part A 18: constraints and the timing certificate (18.1), layering (18.2),
state and enums (18.3) and the role-consistency rule (18.4). Reference codec only; nothing here is compiled."""
from pathlib import Path

import pytest

from score import Codec, ScoreError, errors, parse
from score.constrain import format_certificate, measure
from score.layer import ByteCodec, LayeredCodec
from spec_blocks import spec_examples

UART_HEAD = """
protocol seq_uart
roles    sender, receiver

wire tx out push-pull idle high by sender

clock 115200 Hz
  sender:   generated
  receiver: started by tx fall

symbols
  bit(d)   tx "d"          sample tx at 50%

bits lsb first
"""

SEQ_UART = UART_HEAD + """
enum kind : u2
  DATA = 0
  ACK  = 1
  NAK  = 2

state
  seq : u4 = 0

grammar
  line  = frame*
  frame = bit(0)
          k:kind
          n:u4 expect seq
          pad:u2 = 0
          bit(1)
          gap 1 beats
          seq <- seq + 1
"""

MODBUS = (Path(__file__).resolve().parents[2] / "score/examples/modbus_rtu.score").read_text(encoding="utf-8")

I2C_CONSTRAIN = """
constrain
  fSCL     scl rise -> scl rise                  >= 10 us
  tLOW     scl fall -> scl rise                  >= 4.7 us
  tHIGH    scl rise -> scl fall                  >= 4 us
  tSU_DAT  sda change when scl low -> scl rise   >= 250 ns
  tHD_STA  start_c -> scl fall                   >= 4 us
  tSU_STA  scl rise -> start_c                   >= 4.7 us
  tSU_STO  scl rise -> stop_c                    >= 4 us
  tBUF     stop_c -> start_c                     >= 4.7 us
"""


def codes(src):
    return {d.code for d in errors(parse(src))}


# ---- 18.3 enums and state ------------------------------------------------------------------------------------
def test_enum_field_takes_its_width_and_member_names():
    s = parse(SEQ_UART)
    assert errors(s) == []
    f = s.prods[1].body.items[1]
    assert f.type.kind == "u" and f.type.width == 2 and f.type.enum == "kind"
    assert s.consts() == {"DATA": 0, "ACK": 1, "NAK": 2}


def test_state_carries_across_frames_on_both_sides():
    s = parse(SEQ_UART)
    c = Codec(s)
    ev = [("k", "DATA"), ("n", 0), ("k", "ACK"), ("n", 1), ("k", 2), ("n", 2)]
    enc = c.encode_all(ev)
    r = c.decode("receiver", enc.bus)
    assert r.ok, r.notes
    assert r.events == [("k", 0), ("n", 0), ("pad", 0), ("k", 1), ("n", 1), ("pad", 0), ("k", 2), ("n", 2),
                        ("pad", 0)]
    assert c.state[("decode", "receiver")] == {"seq": 3}
    assert c.state[("encode", None)] == {"seq": 3}


def test_state_expectation_catches_a_skipped_sequence_number():
    s = parse(SEQ_UART)
    c = Codec(s)
    enc = c.encode_all([("k", 0), ("n", 0), ("k", 0), ("n", 2)])        # the sender skips 1
    r = c.decode("receiver", enc.bus)
    assert not r.ok and any("expected 1, got 2" in n for n in r.notes)


def test_received_value_outside_the_enum_is_a_mismatch():
    s = parse(SEQ_UART)
    c = Codec(s)
    enc = c.encode_all([("k", 3), ("n", 0)])
    r = c.decode("receiver", enc.bus)
    assert not r.ok and any("not a member of enum kind" in n for n in r.notes)


def test_state_wraps_at_its_width():
    s = parse(SEQ_UART)
    c = Codec(s)
    ev = []
    for i in range(17):
        ev += [("k", 0), ("n", i % 16)]
    r = c.decode("receiver", c.encode_all(ev).bus)
    assert r.ok, r.notes
    assert c.state[("decode", "receiver")] == {"seq": 1}


@pytest.mark.parametrize("bad, code", [
    ("n:u4 expect seq\n          other <- 1", "E-NAMES"),                         # update of an undeclared state
    ("n:u4 expect nosuch", "E-NAMES"),                                            # unknown name
])
def test_state_name_errors(bad, code):
    assert code in codes(SEQ_UART.replace("n:u4 expect seq", bad))


def test_unknown_type_is_a_names_error():
    with pytest.raises(ScoreError) as e:
        parse(SEQ_UART.replace("k:kind", "k:knd"))
    assert e.value.code == "E-NAMES"


def test_enum_member_value_must_fit():
    with pytest.raises(ScoreError):
        parse(SEQ_UART.replace("NAK  = 2", "NAK  = 4"))


# ---- 18.4 role consistency -----------------------------------------------------------------------------------
def test_spec_examples_satisfy_the_role_rule():
    for src in spec_examples():
        assert "E-ROLE" not in codes(src)


@pytest.mark.parametrize("old, new", [
    ("body(rw) if ack == 0", "body(rw) if my_addr == 5"),                      # a condition on a private value
    ("body(rw) if ack == 0", "body(my_addr & 1)"),                             # it picks a production variant
    ("addr:u7  by controller", "addr:u7  by controller = my_addr"),            # the controller cannot know it
])
def test_private_parameter_in_shared_decision_is_rejected(old, new):
    i2c = spec_examples()[1]
    assert old in i2c
    assert "E-ROLE" in codes(i2c.replace(old, new))


def test_private_parameter_in_owners_value_is_allowed():
    i2c = spec_examples()[1]
    assert "my_addr" in i2c and "E-ROLE" not in codes(i2c)          # ack:bit by target = (addr == my_addr) ? 0 : 1


def test_state_update_may_not_use_a_private_parameter():
    src = SEQ_UART.replace("seq <- seq + 1", "seq <- seq + step") + "\nparam\n  step : u4 = 1 for receiver\n"
    assert "E-ROLE" in codes(src)
    assert "E-ROLE" not in codes(src.replace(" for receiver", ""))


# ---- 18.1 constraints and the certificate --------------------------------------------------------------------
def i2c_with(constrain):
    return parse(spec_examples()[1] + constrain)


def i2c_bus(s, ev):
    c = Codec(s, params={"my_addr": 0x50})
    return c.encode_all(ev, lead=1200, tail=1200).bus


TX = [("start",), ("addr", 0x50), ("rw", 0), ("data", 0x81), ("dack", 0), ("data", 0x3C), ("dack", 0), ("stop",)]
# write one byte, repeated START, read two
TXR = [("start",), ("addr", 0x50), ("rw", 0), ("data", 0x81), ("dack", 0), ("rstart",), ("start",), ("addr", 0x50),
       ("rw", 1), ("data", 0x5A), ("more", 0), ("data", 0xA5), ("more", 1), ("stop",)]


def test_constraints_parse_and_check():
    s = i2c_with(I2C_CONSTRAIN)
    assert errors(s) == []
    assert [c.name for c in s.constraints][:3] == ["fSCL", "tLOW", "tHIGH"]
    c = s.constraints[3]
    assert (c.a.wire, c.a.edge, c.a.when_wire, c.a.when_level, c.b.edge, c.op) == \
        ("sda", "change", "scl", "low", "rise", ">=")


@pytest.mark.parametrize("line, code", [
    ("tX  sdx rise -> scl rise >= 1 us", "E-NAMES"),           # unknown wire
    ("tX  nosuch -> scl rise >= 1 us", "E-NAMES"),             # not an event
    ("tX  scl rise -> scl rise >= 1 us\n  tX  scl fall -> scl fall >= 1 us", "E-NAMES"),    # declared twice
])
def test_constraint_name_errors(line, code):
    assert code in {d.code for d in errors(i2c_with("\nconstrain\n  " + line + "\n"))}


def test_constraint_needs_a_time_unit():
    with pytest.raises(ScoreError):
        i2c_with("\nconstrain\n  tX  scl rise -> scl rise >= 10 kHz\n")


def test_certificate_of_the_spec_i2c_example():
    """UM10204 standard mode against the 16.2 example at 100 kHz, with a repeated START. START holds SDA low for half
    a beat (5.0 us) before SCL falls; the repeated START's first beat raises SCL a beat (10 us) before SDA falls.
    Before O7 was closed, START held for one quarter beat (2.5 us) and failed tHD;STA = 4.0 us."""
    s = i2c_with(I2C_CONSTRAIN)
    lines = {ln.name: ln for ln in measure(s, i2c_bus(s, TXR))}
    print(format_certificate(list(lines.values()), "I2C 16.2 at 100 kHz"))
    for k in ("fSCL", "tLOW", "tHIGH", "tSU_DAT", "tSU_STO"):
        assert lines[k].status == "PASS", lines[k]
    assert lines["fSCL"].worst_ns == pytest.approx(10_000)
    assert lines["tLOW"].worst_ns == pytest.approx(5_000) and lines["tLOW"].margin_ns == pytest.approx(300)
    assert lines["tHD_STA"].status == "PASS" and lines["tHD_STA"].pairs == 2
    assert lines["tHD_STA"].worst_ns == pytest.approx(5_000) and lines["tHD_STA"].margin_ns == pytest.approx(1_000)
    assert lines["tSU_STA"].status == "PASS" and lines["tSU_STA"].worst_ns == pytest.approx(10_000)
    assert lines["tBUF"].status == "UNTESTED" and lines["tBUF"].pairs == 0     # one transaction: no STOP->START


def test_certificate_sees_bus_free_time_between_transactions():
    s = i2c_with(I2C_CONSTRAIN)
    lines = {ln.name: ln for ln in measure(s, i2c_bus(s, TX + TX))}
    assert lines["tBUF"].pairs == 1 and lines["tBUF"].status in ("PASS", "FAIL")


def test_certificate_upper_bound_and_scaling():
    s = i2c_with("\nconstrain\n  tHIGHmax  scl rise -> scl fall <= 4 us\n  beat  scl rise -> scl rise <= 1 beats\n")
    lines = {ln.name: ln for ln in measure(s, i2c_bus(s, TX))}
    assert lines["tHIGHmax"].status == "FAIL" and lines["tHIGHmax"].margin_ns == pytest.approx(-1_000)
    assert lines["beat"].status == "PASS" and lines["beat"].bound_ns == pytest.approx(10_000)


# ---- 18.2 layering -------------------------------------------------------------------------------------------
def test_modbus_reference_frame():
    """Modbus RTU 'read holding registers 0..9 of slave 1' is 01 03 00 00 00 0A C5 CD (CRC low byte first)."""
    bc = ByteCodec(parse(MODBUS))
    toks = bc.encode([("slave", 1), ("func", "READ_HOLDING"), ("start", 0), ("count", 10)])
    assert bytes(t[1] for t in toks if t[0] == "byte") == bytes.fromhex("010300000 00AC5CD".replace(" ", ""))
    assert toks[-1][0] == "gap" and toks[-1][1].unit == "chars"


def test_modbus_over_uart_round_trip():
    s = parse(MODBUS)
    lc = LayeredCodec(s)
    ev = [("slave", 1), ("func", 3), ("start", 0), ("count", 10),
          ("slave", 17), ("func", 16), ("start", 1), ("count", 2), ("regs", bytes([0, 10, 1, 2])),
          ("slave", 5), ("func", "WRITE_SINGLE"), ("reg", 7), ("value", 0xBEEF)]
    bus, toks = lc.encode_all(ev)
    out, ok, notes = lc.decode("slave", bus)
    assert ok, notes
    want = [(k, (s.enums["fn"].members[v] if isinstance(v, str) else v)) for k, v in ev]
    want.insert(8, ("nbytes", 4))
    assert out == want
    assert lc.bc.state == {"encode": {"sent": 3}, "decode": {"sent": 3}}
    assert lc.char_cycles == pytest.approx(10 * 60e6 / 115200)


def test_modbus_bad_crc_is_a_mismatch():
    s = parse(MODBUS.replace("crc crc16_modbus over", "fcs:crc crc16_modbus over"))     # named: injectable
    lc = LayeredCodec(s)
    bus, _ = lc.encode_all([("slave", 1), ("func", 3), ("start", 0), ("count", 10), ("fcs", 0x1234)])
    out, ok, notes = lc.decode("slave", bus)
    assert not ok and any("crc crc16_modbus" in n for n in notes)


def test_modbus_frames_split_on_silence():
    """Two frames sent back to back without the 3.5 char gap read as one frame: the second slave byte lands
    inside the first frame and the CRC fails."""
    bc = ByteCodec(parse(MODBUS))
    a = [t for t in bc.encode([("slave", 1), ("func", 3), ("start", 0), ("count", 10)]) if t[0] == "byte"]
    ok_frames = bc.decode(a + [("eof",)] + a + [("eof",)])
    merged = bc.decode(a + a + [("eof",)])
    assert ok_frames[1] and not merged[1]


@pytest.mark.parametrize("old, new, code", [
    ("slave:u8", "slave:u8 by slave", "E-OWNER"),                   # only the master sends over uart.char
    ("slave:u8", "slave:u4", "E-LAYER"),                             # not whole bytes
    ("use uart_8n1 as uart", "use uart_9n1 as uart", "E-NAMES"),     # no such library
    ("over uart.char", "over uart.line", "E-LAYER"),                 # not a byte carrier
    ("gap 3.5 chars", "gap 3 beats", "E-LAYER"),                     # beats belong to the lower protocol
])
def test_layering_errors(old, new, code):
    assert old in MODBUS
    assert code in codes(MODBUS.replace(old, new))


def test_layered_score_has_no_physical_sections():
    src = MODBUS.replace("grammar", "wire tx out push-pull idle high by master\n\ngrammar", 1)
    assert "E-LAYER" in codes(src)


def test_physical_score_may_not_import_a_protocol():
    assert "E-NAMES" in codes("use uart_8n1 as uart\n" + SEQ_UART)
