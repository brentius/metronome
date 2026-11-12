"""Assembler syntax, errors and directive packing (checked against the v2 model's own decode of the host writes)."""
import pytest
from common import *
from metronome2_tools._md import M
from metronome2_tools.asm import assemble_text
from metronome2_tools.encode import decode
from metronome2_tools.model import AsmError

CFG = """
.clock 60e6
.line 2
    inc 3
    mod 1000
    taps 100 600 -
    preset 7
    window 120 500
    edge P4 fall
    t0edge uio[5] both
    snap tap1
    pins A=P3 B=P9
    in0 a0 ^ a1
    in1 maj(a0, a1, a2) & rem
    hold P8 high tap1
    ctl run arm
.end
.line 0
    period 8
    follow
    edge P0 rise
.end
.thread 4
    core 1
    line 2
    trigger L2.TAP1
    watch0 F3 -> h0
    watch1 SH0.DONE -> h1
    start go
.end
.out O9
    line 2
    sel 3 1 0
    lut b0 ^ (seg & 1)
    oe never
.end
.out O3
    line none
    lut 1
    oe always
.end
.stream 1
    mode rx
    order msb
    start 0x123
    len 77
    mark 5
.end
.lfsr 0 poly=0x04C11DB7 init=0xFFFFFFFF
.core 1
.org 0x10
go:   nop pause goto go
h0:   nop pause goto go
h1:   nop pause goto go
"""


def test_directives_become_the_configuration_the_model_decodes():
    prog = assemble_text(CFG)
    chip = Chip()
    load(chip, prog)
    ln = chip.lines[2]
    assert (ln.INC, ln.MOD, ln.T, ln.PRE, ln.WLO, ln.WHI) == (3, 1000, [100, 600, 1000], 7, 120, 500)
    assert (ln.EDGE_PIN, ln.EDGE_POL, ln.WEN, ln.FOLLOW) == (4, 2, 1, 0)
    assert (ln.T0E_PIN, ln.T0E_POL, ln.T0SRC) == (5, 3, 1) and ln.SNAP == 1 and (ln.PINA, ln.PINB) == (3, 9)
    assert ln.LUT0 == lut(lambda i: (i ^ (i >> 1)) & 1)
    assert ln.LUT1 == lut(lambda i: (((i & 1) + ((i >> 1) & 1) + ((i >> 2) & 1) >= 2) & (i >> 4)) & 1)
    assert (ln.HPIN, ln.HLVL, ln.HTAP, ln.HEN) == (8, 1, 1, 1)
    assert (ln.RUN, ln.ARM, ln.REN) == (1, 1, 0)
    l0 = chip.lines[0]
    assert (l0.INC, l0.MOD, l0.FOLLOW, l0.EDGE_POL) == (1, 8, 1, 1)
    th = chip.threads[4]
    assert (th.CORE, th.LINE, th.TRIG) == (1, 2, M.TRIG_ID["L2.TAP1"])
    assert (th.W0C, th.W1C, th.W0H, th.W1H) == (M.GUARD_ID["F3"], M.GUARD_ID["SH0.DONE"], 0x11, 0x12)
    assert th.PC == 0x10 and th.EN == 1
    o = chip.out[9]
    assert (o.LINE, o.BOUND, o.SEL, o.OE) == (2, 1, [3, 1, 0], 0)
    assert o.LUT == lut(lambda i: ((i & 1) ^ ((i >> 3) & 1)) & 1)
    o3 = chip.out[3]
    assert (o3.BOUND, o3.LUT, o3.OE) == (0, 0xFFFFFFFF, 0xFFFFFFFF)
    s = chip.mem.streams[1]
    assert (s.MODE, s.MSB, s.START, s.LEN, s.MARK) == (1, 1, 0x123, 77, 5)
    assert chip.lf[0].POLY == prog.lfsrs[0].poly == 0xEDB88320 and chip.ctrl.RUN == 1


def test_missing_window_wrap_and_default_taps_disabled():
    p = assemble_text(".line 0\n period 10\n taps - 4\n.end\n")
    ln = p.lines[0]
    assert [ln.tap_enabled(k) for k in range(3)] == [False, True, False] and ln.tap(0) == 10


def test_jump_condition_is_separate_from_the_move_condition():
    p = assemble_text("""
x:  when PIN7 ? R1 -> R0, ! R2 -> R0 goto x if CNT1.Z
    when F2 ? R2 -> R1 goto x ifnot
    goto x if SH0.DONE
    goto x
""")
    i0, i1, i2, i3 = (p.code[0][a].insn for a in range(4))
    assert (i0.cond, i0.jmode, i0.jcond) == ("PIN7", "if", "CNT1.Z")        # PIN7 only guards moves
    assert (i1.cond, i1.jmode, i1.jcond) == ("F2", "ifnot", "F2")           # bare 'ifnot' uses the when condition
    assert (i2.cond, i2.jmode, i2.jcond) == ("TRUE", "if", "SH0.DONE")
    assert (i3.jmode, i3.jcond) == ("always", "TRUE")
    assert decode(p.code[0][0].word).moves[:2] == i0.moves


@pytest.mark.parametrize("src,msg", [
    ("goto 0 if PIN3", "not a jump condition"),                       # per-pin levels are move guards only
    ("goto 0 if F9", "not a jump condition"),                          # flags 8..15 likewise
    ("goto 0 if L0.RUN", "not a jump condition"),
    ("goto 0 if", "needs a jump condition"),
    ("? #1 -> R0", "needs a condition"),
    ("when F0 ? #1 -> R0, #2 -> R1 goto 5", "shared by the jump target"),
    ("when F0 ? R0 -> ACC.LD, R1 -> ACC.ADD", "same group"),
    ("R0 -> L.SYM, R1 -> L.XOR", "same group"),
    ("R1 -> R0, R2 -> R0", "same group"),
    ("#1 -> R0, #2 -> R1, #3 -> R2, #4 -> R3", "at most 3"),
    ("#300 -> R0", "does not fit"),
    ("ZERO -> NOPE", "unknown destination"),
    ("S0.BIT -> L.SYM, never ZERO -> L.SYM", None),
    ("when NOPE ? #1 -> R0", "unknown condition"),
])
def test_instruction_errors(src, msg):
    if msg is None:
        assemble_text(src)
        return
    with pytest.raises(AsmError, match=msg):
        assemble_text(src)


@pytest.mark.parametrize("src,msg", [
    (".line 0\n baud 115200\n bogus 1\n.end", "unknown line setting"),
    (".line 0\n edge P13\n period 4\n.end", "out of range"),
    (".line 4\n period 4\n.end", "line must be"),
    (".line 0\n.end", "needs 'rate'"),
    (".thread 6\n.end", "thread must be"),
    (".thread 0\n trigger L9.BEAT\n.end", "unknown trigger"),
    (".thread 0\n watch0 TRUE -> x\n.end\n.core 0\nx: nop", "hijack"),
    (".thread 0\n start nowhere\n.end", "unknown label"),
    (".out O14\n.end", "out of range"),
    (".out O0\n sel 0 1 4\n.end", "symbol bit"),
    (".stream 2\n.end", "stream must be"),
    (".stream 0\n len 2049\n.end", "outside"),
    (".data 2047 1 2", "exceeds"),
    (".line 0\n period 4\n", "missing .end"),
])
def test_directive_errors(src, msg):
    with pytest.raises(AsmError, match=msg):
        assemble_text(src)


def test_rate_directive_gives_exact_fraction_and_warns_when_inexact():
    p = assemble_text(".clock 60e6\n.line 0\n baud 115200\n.end")
    assert (p.lines[0].inc, p.lines[0].mod) == (6, 3125) and not p.warnings
    p = assemble_text(".clock 60e6\n.line 0\n baud 1234567\n.end")
    assert p.warnings and p.lines[0].inc < p.lines[0].mod <= 0xFFFF


def test_labels_org_and_cores():
    p = assemble_text(".core 1\n.org 5\na: nop\nb: nop goto a\n")
    assert p.labels["a"] == (1, 5) and p.labels["b"] == (1, 6) and p.code[1][6].insn.imm == 5
