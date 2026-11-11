import pytest

from metronome_tools import image as I
from metronome_tools._md import M
from metronome_tools.asm import AsmError, assemble_text, rev_bits
from metronome_tools.image import apply_writes, host_writes

SRC = """
.clock 60e6
.equ BAUD, 115200
.beatgen 1
    baud BAUD
    taps MOD//4 MOD//2 -
    preset 4*INC
    window 100, 3000
    edge P8 fall
    ctl arm
.end
.beatgen 2
    inc 3
    mod 7
    phase 5
    ctl run, ren
.end
.engine 4
    core 1
    trigger BG1.TAP1
    pins A=P8 B=uio[2]
    in0 maj(a0, a1, a2)
    in1 b1 & ~a1
    watch0 F3 -> h0
    watch1 SH2.DONE -> h1
    start go
.end
.engine 5
    core 0
    beatgen 3
    trigger PINA.EDGE
    pina ui[7]
    lut0 0xBEEF
    disable
.end
.out O8
    engine 4
    seg0: 1 0 0 0
    seg1: 0 1 0 0
    seg2: 0 0 1 0
    seg3: 0 0 0 1
.end
.out uio[3]
    engine 4
    lut sym == 3
    oe 1 if seg == 2 else 0
.end
.out O2
    engine none
    oe always
.end
.lfsr 0 width=32 poly=0x04C11DB7 init=0xFFFFFFFF
.lfsr 1 width=16 poly=0x1021
.data 0x10  1, 2, "AB", 0xFF
.irqen outv error
.core 1
go:     nop
h0:     nop
h1:     pause
"""


@pytest.fixture(scope="module")
def mem():
    return apply_writes(host_writes(assemble_text(SRC)))


def rd(mem, addr, n):
    return int.from_bytes(bytes(mem[addr + i] for i in range(n)), "little")


def bgreg(mem, g, name):
    off, size = {v[0]: (k, v[1]) for k, v in M.BG_REGS.items()}[name]
    return rd(mem, M.HOST_MAP["BG_BASE"] + g * 0x20 + off, size)


def engreg(mem, e, name):
    off, size = {v[0]: (k, v[1]) for k, v in M.ENG_REGS.items()}[name]
    return rd(mem, M.HOST_MAP["ENG_BASE"] + e * 0x20 + off, size)


def outreg(mem, o, name):
    off, size = {v[0]: (k, v[1]) for k, v in M.OUT_REGS.items()}[name]
    return rd(mem, M.HOST_MAP["OUT_BASE"] + o * 8 + off, size)


def test_beatgen_rate_and_taps(mem):
    assert (bgreg(mem, 1, "INC"), bgreg(mem, 1, "MOD")) == (6, 3125)       # 115200 baud at 60 MHz
    assert (bgreg(mem, 1, "T0"), bgreg(mem, 1, "T1")) == (781, 1562)
    assert bgreg(mem, 1, "T2") == 3125                                      # disabled tap = MOD
    assert bgreg(mem, 1, "PRE") == 24
    assert (bgreg(mem, 1, "WLO"), bgreg(mem, 1, "WHI")) == (100, 3000)
    assert bgreg(mem, 1, "EDGE") == 8 | (2 << 4)                            # P8, falling
    assert bgreg(mem, 1, "CTL") == 0b1010                                   # ARM + WEN (window given)
    assert bgreg(mem, 2, "PHASE") == 5 and bgreg(mem, 2, "CTL") == 0b101
    assert bgreg(mem, 2, "T0") == 7                                         # unset taps disabled, not 0


def test_engine_registers(mem):
    assert engreg(mem, 4, "CFG") == 1 | (1 << 1) | (1 << 2)                 # EN, core 1, BG1 (from trigger)
    assert engreg(mem, 4, "TRIG") == M.TRIG_ID["BG1.TAP1"]
    assert engreg(mem, 4, "PINS") == 8 | (M.IN_PINS.index("uio[2]") << 4)
    assert engreg(mem, 4, "PC") == 0
    assert engreg(mem, 4, "W0C") == M.GUARD_ID["F3"] and engreg(mem, 4, "W0H") == 1
    assert engreg(mem, 4, "W1C") == M.GUARD_ID["SH2.DONE"] and engreg(mem, 4, "W1H") == 2
    # in0 = majority of a0,a1,a2 (b1 ignored); index = a0 + 2 a1 + 4 a2 + 8 b1
    maj = sum(1 << i for i in range(16) if bin(i & 7).count("1") >= 2)
    assert engreg(mem, 4, "LUT0") == maj
    assert engreg(mem, 4, "LUT1") == sum(1 << i for i in range(16) if (i >> 3) & 1 and not (i >> 1) & 1)
    assert engreg(mem, 5, "CFG") == 0 | (0 << 1) | (3 << 2)                 # disabled, BG3
    assert engreg(mem, 5, "LUT0") == 0xBEEF
    assert engreg(mem, 5, "PINS") == M.IN_PINS.index("ui[7]") | (15 << 4)


def test_output_cells(mem):
    assert outreg(mem, 8, "LUT") == sum(1 << (s * 4 + s) for s in range(4))   # diagonal
    assert outreg(mem, 3, "LUT") == sum(1 << (s * 4 + 3) for s in range(4))
    assert outreg(mem, 3, "OE") == 0x0F00                                     # seg 2
    assert outreg(mem, 3, "ENG") == 4
    assert outreg(mem, 2, "ENG") == 7 and outreg(mem, 2, "OE") == 0xFFFF
    assert (M.HOST_MAP["OUT_BASE"] + 8 * 8 + 4) not in mem                    # O8 has no OE register written


def test_lfsr_and_data_and_ctrl(mem):
    assert rd(mem, M.HOST_MAP["UNIT_BASE"], 4) == 0xEDB88320                  # reflected CRC-32 polynomial
    assert rd(mem, M.HOST_MAP["UNIT_BASE"] + 8, 4) == rev_bits(0x1021, 16)
    assert [mem[M.HOST_MAP["DATA_BASE"] + 0x10 + i] for i in range(5)] == [1, 2, 65, 66, 255]
    assert rd(mem, M.HOST_MAP["CTRL_BASE"] + 2, 1) == 3                       # IRQEN
    assert rd(mem, M.HOST_MAP["CTRL_BASE"], 1) == 1                           # RUN


def test_order_run_last_ctl_late():
    w = host_writes(assemble_text(SRC))
    assert w[-1][2] == "CTRL.RUN"
    notes = [n for _, _, n in w]
    assert notes.index("BG1.CTL") > notes.index("E4.CFG") > notes.index("BG1.INC")
    assert notes.index("CTRL.IRQEN") > notes.index("BG2.CTL")


def test_crc_helper_symbols():
    p = assemble_text(".lfsr 0 poly=0x04C11DB7 init=0xFFFFFFFF\n#LF0_INIT_B3 -> R0")
    assert p.symbols["LF0_POLY"] == 0xEDB88320 and p.symbols["LF0_INIT"] == 0xFFFFFFFF
    assert p.code[0][0].insn.imm == 0xFF
    p = assemble_text(".lfsr 0 width=16 poly=0x1021 init=0x8000")
    assert p.symbols["LF0_INIT_B0"] == 0x01 and p.symbols["LF0_INIT_B1"] == 0
    p = assemble_text(".lfsr 0 poly=0xEDB88320 init=0 reflected")
    assert p.symbols["LF0_POLY"] == 0xEDB88320


def test_rate_warning_when_inexact():
    p = assemble_text(".beatgen 0\n rate 12345\n.end")
    assert (p.bgs[0].inc, p.bgs[0].mod) != (0, 0) and p.warnings


@pytest.mark.parametrize("src,msg", [
    (".beatgen 0\n.end", "needs 'rate'"),
    (".beatgen 0\n rate 1000\n taps 2000 100\n.end", "T0 <= T1"),
    (".beatgen 0\n rate 1000\n taps 70000\n.end", "below mod"),
    (".beatgen 0\n rate 1000\n bogus 1\n.end", "unknown beatgen setting"),
    (".beatgen 0\n inc 5\n mod 5\n.end", "inc < mod"),
    (".engine 0\n trigger BG0.BEET\n.end", "did you mean BG0.BEAT"),
    (".engine 9\n.end", "engine must be"),
    (".engine 0\n watch0 TRUE -> x\n.end", "hijack"),
    (".engine 0\n start nowhere\n.end", "unknown label"),
    (".engine 0\n core 1\n start a\n.end\na: nop", "core 0 but the engine runs on core 1"),
    (".out O99\n.end", "out of range"),
    (".out O1\n seg0: 1 2 3\n.end", "four values"),
    (".beatgen 0\n rate 1000", "missing .end"),
    (".data 2047 1 2", "exceeds"),
    (".budget engine 0 foo 3", "budget"),
])
def test_directive_errors(src, msg):
    with pytest.raises(AsmError, match=msg):
        assemble_text(src)


def test_program_words_in_writes():
    p = assemble_text(".core 1\n.org 3\nnop\nZERO -> R0\n")
    w = host_writes(p)
    addr = I.prog_addr(1, 3)
    assert w[0][0] == addr and len(w[0][1]) == 16
    assert int.from_bytes(w[0][1][8:], "little") == p.code[1][4].word
