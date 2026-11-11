from helpers import *     # noqa: F401,F403
from metronome.beatgen import BeatGen


def bgo(**kw):
    g = BeatGen(0)
    for k, v in kw.items():
        setattr(g, k, v)
    return g


def test_synchroniser_delay_and_rise_start():
    chip = Chip()
    bg_cfg(chip, 0, PRE=7, EDGE=0x10, CTL=0b010)          # pin P0 rising edge, ARM
    chip.step(IDLE, 1)                                    # cycle 0: raw pin high -> s1
    assert chip.bg[0].RUN == 0
    chip.step(IDLE, 1)                                    # cycle 1: s2 high, sp low is seen in cycle 2
    assert chip.bg[0].RUN == 0
    chip.step(IDLE, 1)                                    # cycle 2: RISE evaluated, start
    g = chip.bg[0]
    assert (g.RUN, g.ARM, g.PH) == (1, 0, 7)


def test_fall_edge_on_ui_pin_and_pin_numbering():
    chip = Chip()
    bg_cfg(chip, 0, EDGE=8 | (2 << 4), CTL=0b010)         # P8 = ui_in[3], falling
    for _ in range(4):
        chip.step(IDLE | (1 << 3), 0)
    assert chip.bg[0].RUN == 0
    for i in range(3):
        chip.step(IDLE, 0)
    assert chip.bg[0].RUN == 1


def test_pins_13_to_15_read_zero():
    chip = Chip()
    for _ in range(4):
        chip.step(0xFF, 0xFF)
    lv, rs, fl = chip.pins.levels()
    assert lv == 0x1FFF and lv >> 13 == 0


def test_rational_rate_6_per_3125():
    chip = Chip()
    bg_cfg(chip, 0, INC=6, MOD=3125, CTL=1)
    beats = []
    for t in range(3125):
        chip.step(IDLE, 0)
        if chip.bg[0].beat:
            beats.append(t)
    assert len(beats) == 6
    assert beats[0] == 520          # PH=3120 at cycle 520, 3120+6 >= 3125
    # long-run: exactly 6 beats per 3125 cycles, again
    n = 0
    for t in range(3125):
        chip.step(IDLE, 0)
        n += chip.bg[0].beat
    assert n == 6


def test_taps_nowrap_wrap_and_tk_ge_mod():
    g = bgo(RUN=1, MOD=10, INC=3, T0=5, T1=1, T2=10, PH=3)
    g.comb(0, 0)
    assert (g.beat, g.taps) == (0, (1, 0, 0))             # 3 -> 6 crosses 5
    g.PH = 8                                              # 8 -> 11 wraps to 1: T1=1 reached after the wrap
    g.comb(0, 0)
    assert g.beat == 1 and g.taps == (0, 1, 0) and g._nx["PH"] == 1
    g.PH = 8
    g.T0 = 9                                              # 9 > PH (8): passed before the wrap
    g.comb(0, 0)
    assert g.taps[0] == 1
    g.PH = 9                                              # already at 9: not re-tapped
    g.comb(0, 0)
    assert g.taps[0] == 0
    g.T2 = 12                                             # Tk >= MOD never taps
    g.PH = 8
    g.comb(0, 0)
    assert g.taps[2] == 0


def test_seg():
    g = bgo(MOD=100, T0=10, T1=20, T2=30, PH=25)
    g.comb(0, 0)
    assert g.seg == 2
    g.T2 = 100                                            # disabled (>= MOD)
    g.PH = 99
    g.comb(0, 0)
    assert g.seg == 2


def test_idle_generator_holds():
    g = bgo(MOD=10, INC=3, PH=4)
    g.comb(0, 0)
    assert g.beat == 0 and g.taps == (0, 0, 0) and g._nx["PH"] == 4


def test_window_accept_reject_and_wrapped_window():
    base = dict(RUN=1, REN=1, WEN=1, MOD=100, INC=1, PRE=50, EDGE_PIN=0, EDGE_POL=1, WLO=10, WHI=20)
    for ph, ok in [(15, True), (10, True), (20, True), (21, False), (9, False)]:
        g = bgo(PH=ph, **base)
        g.comb(1, 0)
        assert (g._nx["PH"] == 50, g.beat) == (ok, 0) if ok else (g._nx["PH"] == ph + 1)
        assert g._nx["SC"] == int(ok)
    for ph, ok in [(95, True), (3, True), (50, False)]:
        g = bgo(PH=ph, **{**base, "WLO": 90, "WHI": 5})
        g.comb(1, 0)
        assert (g._nx["PH"] == 50) == ok
    g = bgo(PH=15, **{**base, "REN": 0})                 # REN low: no accept, free-runs
    g.comb(1, 0)
    assert g._nx["PH"] == 16
    g = bgo(PH=60, **{**base, "WEN": 0})                 # window disabled: any phase accepts
    g.comb(1, 0)
    assert g._nx["PH"] == 50


def test_accept_suppresses_beat_and_taps():
    g = bgo(RUN=1, REN=1, MOD=10, INC=9, PH=5, PRE=0, T0=7, EDGE_POL=1)
    g.comb(1, 0)
    assert g.beat == 0 and g.taps == (0, 0, 0)


def test_sc_sp_over_beats():
    g = bgo(RUN=1, REN=1, MOD=4, INC=1, PRE=0, EDGE_POL=1)
    g.comb(1, 0); g.commit()                              # accept at PH=0
    assert (g.SC, g.SP) == (1, 0)
    for _ in range(3):
        g.comb(0, 0); g.commit()
    assert (g.PH, g.SC, g.SP) == (3, 1, 0)
    g.comb(0, 0); assert g.beat == 1; g.commit()          # beat: SP <- SC, SC <- 0
    assert (g.PH, g.SC, g.SP) == (0, 0, 1)
    for _ in range(4):
        g.comb(0, 0); g.commit()
    assert (g.SC, g.SP) == (0, 0)


def test_arm_start_once_and_ctl_move_override():
    g = bgo(ARM=1, PRE=3, EDGE_POL=1, MOD=10, INC=1)
    g.comb(1, 0)
    assert g._nx["RUN"] == 1 and g._nx["ARM"] == 0 and g._nx["PH"] == 3
    g.commit(ctl_move=0b110)                              # move overrides RUN', ARM'; sets REN
    assert (g.RUN, g.ARM, g.REN, g.PH) == (0, 1, 1, 3)


def test_ctl_move_and_phase_host_write_priority():
    chip = Chip()
    bg_cfg(chip, 0, INC=1, MOD=100, CTL=1)
    chip.step(IDLE, 0)
    chip.backdoor_write(m.HOST_MAP["BG_BASE"] + 0x10, le(77, 2))
    assert chip.bg[0].PH == 77
    assert chip.backdoor_read(m.HOST_MAP["BG_BASE"] + 0x10) == 77
    bg_cfg(chip, 0, CTL=0b1101)
    assert chip.backdoor_read(m.HOST_MAP["BG_BASE"] + 0x12) == 0b1101
