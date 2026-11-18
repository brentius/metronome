"""Section 16 examples parse and pass every static check; negative cases raise the spec's diagnostics."""
import pytest
from spec_blocks import spec_examples
from score import ScoreError, check, check_binding, parse

NAMES = ["uart_8n1", "i2c", "spi_mode0", "ethernet_10baset", "tether"]


@pytest.mark.parametrize("i", range(5))
def test_example_parses_and_checks(i):
    sc = parse(spec_examples()[i])
    assert sc.name == NAMES[i]
    assert [str(d) for d in check(sc)] == []


def codes(src):
    return {d.code for d in check(parse(src))}


BASE = """protocol t
roles a, b
wire w out push-pull idle low by a
clock 1 MHz
  a: generated
  b: started by w rise
symbols
  bit(d)  w "d"  sample w at 50%
  m1      w "1"
  m2      w "0"
bits msb first
grammar
  g = {GRAM}
"""


def mk(gram):
    return BASE.replace("{GRAM}", gram)


def test_base_ok():
    assert codes(mk("x:u8 m1")) == set()


def test_e_ambig_two_symbols():
    # both alternatives start with m1: one symbol of lookahead cannot choose
    assert "E-AMBIG" in codes(mk("(m1 m2 | m1 x:u8)"))


def test_decidable_choice_ok():
    assert "E-AMBIG" not in codes(mk("(m1 x:u8 | m2 y:u8)"))


def test_e_ambig_loop_follow_overlap():
    assert "E-AMBIG" in codes(mk("(m1)* m1"))


def test_e_names_unknown_ref_and_field():
    assert "E-NAMES" in codes(mk("zzz"))
    assert "E-NAMES" in codes(mk("x:u8 = y"))
    assert "E-NAMES" in codes(mk("x:u8 y:u8 if q == 1"))


def test_e_owner():
    # b drives wire w, which is out by a
    assert "E-OWNER" not in codes(mk("m1 by b"))          # no value in the wave: the wire's owner drives it (D29)
    assert "E-OWNER" in codes(mk("x:u8 by b"))            # b's data bit would have to appear in a's wire
    assert "E-OWNER" not in codes(mk("bit(1) by b"))      # a constant argument is known to every role


DUPLEX = BASE.replace("wire w out", "wire v out push-pull idle low by b\nwire w out").replace(
    'bit(d)  w "d"  sample w at 50%', 'bit(p, q)  w "p"  v "q"  sample w at 50%')


def test_e_duplex_lengths():
    src = DUPLEX.replace("g = {GRAM}", "g = x:u8 by a || y:u16 by b")
    assert "E-DUPLEX" in codes(src)
    assert "E-DUPLEX" not in codes(DUPLEX.replace("g = {GRAM}", "g = x:u8 by a || y:u8 by b"))


def test_e_duplex_same_owner():
    src = DUPLEX.replace("g = {GRAM}", "g = x:u8 by a || y:u8 by a")
    assert "E-DUPLEX" in codes(src)


def test_e_fit_seg_wave_length():
    assert "E-FIT-SEG" in codes(mk("x:u8").replace('m2      w "0"', 'm2      w "01010"'))


def test_e_fit_seg_too_many_splits():
    src = mk("x:u8").replace("b: started by w rise", "b: started by w rise\n  split 20% 40% 60% 80%")
    assert "E-FIT-SEG" in codes(src)


def four_seg(src, sample):
    """Four segments; m1 changes level inside the beat, so the sender needs the split taps (R3)."""
    return src.replace("b: started by w rise", "b: started by w rise\n  split 25% 50% 75%").replace(
        'w "d"  sample w at 50%', f'w "dddd"  sample w at {sample}').replace('m1      w "1"', 'm1      w "1110"').replace(
        'm2      w "0"', 'm2      w "0000"')


def test_e_fit_tap():
    assert "E-FIT-TAP" in codes(four_seg(mk("x:u8 m1"), "62%"))


def test_split_sample_share_tap_ok():
    assert "E-FIT-TAP" not in codes(four_seg(mk("x:u8 m1"), "50%"))


def one_wire(waves):
    syms = "\n".join(f'  s{i}  w "{x}"' for i, x in enumerate(waves))
    return f"""protocol t
roles a, b
wire w out push-pull idle low by a
clock 1 MHz
  a: generated
  b: generated
symbols
{syms}
grammar
  g = s0
"""


def test_e_fit_enc_too_many_waveforms():
    assert "E-FIT-ENC" in codes(one_wire(["00", "01", "10", "11", "0z", "1z", "z0", "z1", "zz"]))


def test_fit_enc_eight_waveforms_ok():
    assert "E-FIT-ENC" not in codes(one_wire(["00", "01", "10", "11", "0z", "1z", "z0", "z1"]))


def test_e_fit_sym_over_16():
    assert "E-FIT-SYM" in codes(one_wire(["0"] * 17))


def test_e_fit_smp_three_wires():
    src = """protocol t
roles a, b
wire x out push-pull idle low by a
wire y out push-pull idle low by a
wire z out push-pull idle low by a
clock 1 MHz
  a: generated
  b: generated
symbols
  s  x "1"  y "1"  z "1"  sample x at 50%  sample y at 50%  sample z at 50%
grammar
  g = s
"""
    assert "E-FIT-SMP" in codes(src)


def test_e_fit_pin_nine_open_drain():
    wires = "\n".join(f"wire w{i} shared open-drain idle high" for i in range(9))
    src = f"""protocol t
roles a, b
{wires}
clock 1 MHz
  a: generated
  b: generated
symbols
  s  w0 "0"
grammar
  g = s
"""
    assert "E-FIT-PIN" in codes(src)


def test_syntax_errors_have_positions():
    with pytest.raises(ScoreError) as e:
        parse(mk("x:u8 ("))
    assert e.value.pos is not None and e.value.pos == (13, 13)
    with pytest.raises(ScoreError) as e:
        parse("protocol t\nroles a, b\nwire w sideways\n")
    assert e.value.pos == (3, 8)
    with pytest.raises(ScoreError):
        parse(mk("x:q9"))


def test_binding(examples):
    i2c = examples["i2c"]
    assert any(d.code == "E-BIND" for d in check_binding(i2c, "controller", "scl=P3/O4 sda=P4/O4"))
    assert check_binding(i2c, "controller", "scl=P0/O0 sda=P1/O1") == []
    bad = check_binding(i2c, "controller", "scl=P0/O9 sda=P1/O1")
    assert any("O0..O7" in d.msg for d in bad)
    uart = examples["uart"]
    assert check_binding(uart, "sender", "tx=-/O12") == []          # push-pull output may use O0..O13
    assert check_binding(uart, "receiver", "tx=P5") == []
    assert check_binding(uart, "sender", "tx=-/O14") != []
    assert check_binding(uart, "sender", "") != []
    spi = examples["spi"]
    assert check_binding(spi, "controller", "sck=-/O0 cs_n=-/O1 mosi=-/O2 miso=P0") == []
    assert check_binding(spi, "controller", "sck=-/O0 cs_n=-/O1 mosi=-/O2 miso=P13") != []


def test_expression_precedence_and_cond():
    from score.lexer import tokenize
    from score.model import eval_expr
    from score.parser import TS, parse_vexpr
    ln = tokenize("(1 + 2 * 3 == 7) ? (a & 0xF0) >> 4 : 9")[0]
    e = parse_vexpr(TS(ln.toks))
    assert eval_expr(e, {"a": 0xAB}) == 0xA


def test_wrapping_recovery_window_parses():
    sc = parse(spec_examples()[4])
    assert sc.clock.roles["node"].win[0] > sc.clock.roles["node"].win[1]
    with pytest.raises(ScoreError):
        parse(BASE.replace("started by w rise", "recovered from w edges, window 40%..40%").replace(
            "{GRAM}", "x:u8"))
