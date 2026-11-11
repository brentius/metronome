import zlib

from helpers import *     # noqa: F401,F403
from metronome.units import Acc, Counter, Lfsr, Shifter


def test_acc_ops():
    a = Acc()
    a.op("LD", 0x80)
    assert (a.A, a.Z, a.N) == (0x80, 0, 1)
    a.op("ADD", 0x80)
    assert (a.A, a.C, a.Z, a.N) == (0, 1, 1, 0)
    a.A = 5
    a.op("SUB", 7)
    assert (a.A, a.C, a.Z, a.N) == (0xFE, 0, 0, 1)
    a.A = 5
    a.op("SUB", 5)
    assert (a.A, a.C, a.Z) == (0, 1, 1)
    a.A = 5
    a.op("CMP", 5)
    assert (a.A, a.C, a.Z, a.N) == (5, 1, 1, 0)
    a.op("CMP", 6)
    assert (a.A, a.C, a.Z, a.N) == (5, 0, 0, 1)
    a.A = 0xF0
    a.op("AND", 0x3C)
    assert a.A == 0x30
    a.op("OR", 0x01)
    assert a.A == 0x31
    a.op("XOR", 0x31)
    assert (a.A, a.Z) == (0, 1)
    a.C = 1
    a.op("AND", 0xFF)
    assert a.C == 1                                       # logic ops leave C alone


def test_shifter_lsb_first_and_done():
    s = Shifter()
    s.cfg(3)                                              # LEN=3, LSB first
    s.ld(0b101)
    assert (s.D, s.CNT, s.out, s.done) == (5, 3, 1, 0)
    s.sh(1)
    assert (s.D, s.CNT) == (0x82, 2)
    s.sh(0)
    s.sh(1)
    assert (s.D, s.CNT, s.done) == (0xA0, 0, 1)
    s.sh(0)
    assert s.CNT == 0                                     # saturates


def test_shifter_msb_first_len0_means_8():
    s = Shifter()
    s.cfg(0x10)
    s.ld(0x81)
    assert (s.CNT, s.out) == (8, 1)
    s.sh(1)
    assert (s.D, s.CNT, s.out) == (0x03, 7, 0)


def test_counter():
    c = Counter()
    c.op("LO", 0x34)
    c.op("HI", 0x12)
    assert c.V == 0x1234
    c.op("DEC", 0)
    assert c.V == 0x1233
    c.V = 0
    c.op("DEC", 0)
    assert c.V == 0


def test_lfsr_is_reflected_crc32():
    l = Lfsr()
    l.POLY = 0xEDB88320
    l.S = 0xFFFFFFFF
    for byte in b"123456789":
        for i in range(8):
            l.step((byte >> i) & 1)
    assert l.S ^ 0xFFFFFFFF == zlib.crc32(b"123456789") == 0xCBF43926
    l.set_byte(2, 0xAB)
    assert (l.S >> 16) & 0xFF == 0xAB


def test_units_through_moves():
    chip = Chip()
    oneshot(chip, [
        I(("IMM", "ACC.LD"), ("IMM", "R1"), ("IMM", "FLAGS.SET"), imm=0x0B),     # A=0x0B, R1=0x0B, flag 11
        I(("IMM", "SH0.CFG"), ("IMM", "CNT0.LO"), imm=0x13),                       # LEN=3 MSB=1 ; CNT0=0x13
        I(("IMM", "SH0.LD"), ("IMM", "CNT1.HI"), ("IMM", "LF0.B1"), imm=0xA5),
        I(("IMM", "SH0.SH"), ("IMM", "ACC.ADD"), ("IMM", "CNT0.DEC"), imm=0x01, pause=True),
    ])
    assert chip.acc.A == 0x0C and chip.acc.R[1] == 0x0B
    assert chip.flags.F == 1 << 11
    assert chip.sh[0].D == ((0xA5 << 1) & 0xFF | 1) and chip.sh[0].CNT == 2 and chip.sh[0].MSB == 1
    assert chip.cnt[0].V == 0x13 - 1 and chip.cnt[1].V == 0xA500
    assert (chip.lf[0].S >> 8) & 0xFF == 0xA5


def test_flags_fp_tracks_previous_cycle():
    chip = Chip()
    chip.flags.F = 3
    step(chip, 1)
    assert chip.flags.FP == 3


def test_write_group_conflicts():
    # same group in one instruction: lowest move index wins
    chip = Chip()
    oneshot(chip, [I(("IMM", "ACC.LD"), ("ZERO", "ACC.ADD"), imm=5, pause=True)])
    assert chip.acc.A == 5 and chip.ctrl.CONFLICT == 1
    # different groups: no conflict
    for a, b in [("SH0.LD", "SH0.CFG"), ("R0", "R1"), ("SH0.LD", "SH1.LD"), ("FLAGS.SET", "ACC.LD"),
                 ("CNT0.LO", "CNT1.LO"), ("LF0.ST", "LF1.ST")]:
        chip = Chip()
        oneshot(chip, [I(("IMM", a), ("IMM", b), imm=1, pause=True)])
        assert chip.ctrl.CONFLICT == 0, (a, b)
    # same group
    for a, b in [("SH0.LD", "SH0.SH"), ("CNT0.LO", "CNT0.HI"), ("FLAGS.SET", "FLAGS.CLR"), ("LF0.ST", "LF0.B0"),
                 ("P0.AL", "P0.W"), ("BG0.CTL", "BG0.CTL")]:
        chip = Chip()
        oneshot(chip, [I(("IMM", a), ("IMM", b), imm=1, pause=True)])
        assert chip.ctrl.CONFLICT == 1, (a, b)
    # disabled moves do not conflict
    chip = Chip()
    oneshot(chip, [I(("IMM", "R0"), ("IMM", "R0", "never"), imm=1, pause=True)])
    assert chip.ctrl.CONFLICT == 0


def test_conflict_across_cores_lowest_core_wins():
    chip = Chip()
    load(chip, [I(("IMM", "R0"), imm=11, pause=True)], core=0)
    load(chip, [I(("IMM", "R0"), imm=22, pause=True)], core=1)
    eng_cfg(chip, 0, CFG=eng_cfgbyte(1, 0, 0))
    eng_cfg(chip, 1, CFG=eng_cfgbyte(1, 1, 0))
    ctrl(chip, "RUN", 1)
    chip.backdoor_write(m.HOST_MAP["CTRL_BASE"] + 3, b"\x03")
    step(chip, 2)
    assert chip.acc.R[0] == 11 and chip.ctrl.CONFLICT == 1


def test_sticky_register_w1c():
    chip = Chip()
    chip.ctrl.CONFLICT = chip.ctrl.MEMHAZ = 1
    a = m.HOST_MAP["CTRL_BASE"] + 1
    assert chip.backdoor_read(a) == 3
    chip.backdoor_write(a, b"\x01")
    assert chip.backdoor_read(a) == 2
    chip.backdoor_write(a, b"\x02")
    assert chip.backdoor_read(a) == 0


def test_source_ports():
    chip = Chip()
    chip.flags.F = 0xA55A
    for _ in range(4):
        chip.step(IDLE | 0xF8, 0xC3)                       # ui[3..7]=1 -> P8..P12 ; uio=0xC3 -> P0..P7
    oneshot(chip, [
        I(("FLAGS.LO", "R0"), ("PINS.HI", "R3"), ("PINS.LO", "R2")),      # read before the pins (now 0) propagate
        I(("FLAGS.HI", "R1"), pause=True)])
    assert chip.acc.R == [0x5A, 0xA5, 0xC3, 0x1F]
