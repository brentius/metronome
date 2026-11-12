"""SPEC v2 section 3: beat generator, taps and fired bits, follower mode, capture, snapshot."""
import random

from helpers_v2 import *     # noqa: F401,F403


def collect(chip, n, l=0, uio=lambda t: 0):
    """Step n cycles; return per-cycle (beat, taps, SEG-after) for line l."""
    out = []
    for _ in range(n):
        t = chip.cycle
        chip.step(IDLE, uio(t))
        ln = chip.lines[l]
        out.append((ln.beat, tuple(ln.tap), ln.SEG))
    return out


def test_generated_beats_taps_once_and_seg():
    chip = Chip()
    blk(chip, "LINE", 0, INC=1, MOD=6, T0=0, T1=2, T2=4)
    run_line(chip, 0)
    tr = collect(chip, 60)
    beats = [i for i, x in enumerate(tr) if x[0]]
    assert beats[0] == 5 and all(b - a == 6 for a, b in zip(beats, beats[1:]))
    for a, b in zip(beats, beats[1:]):
        window = tr[a + 1:b + 1]                 # taps of the beat that starts at boundary a (T0 fires at a)
        fires = [sum(x[1][k] for x in [tr[a]] + window[:-1]) for k in range(3)]
        assert fires == [1, 1, 1]
    # SEG equals v1's phase formula (calculated equivalence, SPEC 3.4)
    chip2 = Chip()
    blk(chip2, "LINE", 0, INC=1, MOD=6, T0=0, T1=2, T2=4)
    run_line(chip2, 0)
    for _ in range(40):
        chip2.step(IDLE)
        ln = chip2.lines[0]
        assert ln.SEG == sum(ln.PH >= t for t in ln.T)
    assert chip.lines[0].TAPMISS == 0


def test_start_counts_taps_behind_phase_as_fired():
    chip = Chip()
    blk(chip, "LINE", 0, INC=1, MOD=8, T0=0, T1=1, T2=6, PRE=3)
    blk(chip, "LINE", 0, EDGE=edge(0, 1))
    run_line(chip, 0, ctl=0b010)                 # ARM
    steps(chip, 3, uio=0)
    steps(chip, 4, uio=1)                        # rising edge on P0 starts the line at PH = PRE = 3
    ln = chip.lines[0]
    assert ln.RUN and ln.FIRED == 0b011
    steps(chip, 20, uio=1)
    assert ln.TAPMISS == 0


def test_phase_jump_over_tap_sets_tapmiss():
    chip = Chip()
    blk(chip, "LINE", 0, INC=1, MOD=10, T0=0, T1=5, T2=0xFFFF)
    run_line(chip, 0)
    steps(chip, 12)
    assert chip.lines[0].TAPMISS == 0
    while chip.lines[0].PH != 2:
        chip.step(IDLE)
    blk(chip, "LRT", 0, PHASE=8)                # host jumps past T1
    steps(chip, 4)
    assert chip.lines[0].TAPMISS == 1
    assert chip.backdoor_read(m.HOST_MAP["CTRL_BASE"] + 8) & 4      # ERRSUM any TAPMISS
    blk(chip, "LRT", 0, STAT=1)
    assert chip.lines[0].TAPMISS == 0


def manchester_rx(chip, period, jitter, seed, ncycles, T, PRE, WLO, WHI):
    """Drive P0 with a clock-like signal, one mid-beat edge per period with jitter; count tap fires per beat."""
    rnd = random.Random(seed)
    edges, t, lvl = [], 10, 0
    while t < ncycles:
        edges.append(t + rnd.randint(-jitter, jitter))
        t += period
    level = []
    for c in range(ncycles):
        while edges and edges[0] <= c:
            edges.pop(0)
            lvl ^= 1
        level.append(lvl)
    blk(chip, "LINE", 0, INC=1, MOD=period, T0=T[0], T1=T[1], T2=T[2], PRE=PRE, WLO=WLO, WHI=WHI,
        EDGE=edge(0, 3, wen=1))
    run_line(chip, 0, ctl=0b101)                 # RUN, REN
    return collect(chip, ncycles, uio=lambda c: level[c])


def test_recovered_clock_taps_outside_window_fire_exactly_once():
    # MOD 6, window 2..3, re-align to PRE 3; taps satisfy SPEC 10.4: T < WLO and T <= PRE, or T > WHI + INC, T > PRE
    for seed in range(5):
        chip = Chip()
        tr = manchester_rx(chip, 6, 1, seed, 600, T=(0, 1, 5), PRE=3, WLO=2, WHI=3)
        assert chip.lines[0].TAPMISS == 0, seed
        beats = [i for i, x in enumerate(tr) if x[0]]
        assert len(beats) > 80
        for k in range(3):
            assert sum(x[1][k] for x in tr) in (len(beats), len(beats) + 1)


def test_tap_inside_window_never_fires_twice():
    # T1 = 3 sits inside the window; a late edge jumps back over it. Fired bits stop a second fire.
    chip = Chip()
    tr = manchester_rx(chip, 6, 1, 7, 600, T=(0, 3, 0xFFFF), PRE=2, WLO=2, WHI=4)
    beats = [i for i, x in enumerate(tr) if x[0]]
    for a, b in zip(beats, beats[1:]):
        assert sum(x[1][1] for x in tr[a + 1:b + 1]) <= 1


def test_follower_mode_spi_target_capture():
    """Boundary on SCK fall (P0), tap 0 on SCK rise captures MOSI (P1); clock period varies."""
    chip = Chip()
    blk(chip, "LINE", 0, INC=1, MOD=200, T1=0xFFFF, T2=0xFFFF, PRE=0, EDGE=edge(0, 2, follow=1),
        T0EDGE=edge(0, 1) | 0x40, PINS=1, SNAP=0, LUT0=lut(lambda i: i & 1))
    run_line(chip, 0, ctl=0b101)
    rnd = random.Random(1)
    data = [rnd.randint(0, 1) for _ in range(40)]
    wave = []
    for bit in data:
        half = rnd.randint(4, 12)
        wave += [(bit << 1)] * half + [1 | (bit << 1)] * half
    got = []
    for w in wave:
        chip.step(IDLE, w)
        if chip.lines[0].snap:
            got.append(chip.lines[0].W & 1)
    assert got == data
    assert chip.lines[0].TAPMISS == 0
    assert chip.lines[0].SP == 1
    steps(chip, 400, uio=0)                      # clock stops: a wrap with no edge clears SYNC
    assert chip.lines[0].SP == 0


def test_snapshot_is_atomic_and_remembered_bit_decodes_differential():
    """IN1 = sample XOR REM (NRZI-like); IN changes only in the cycle after a snapshot."""
    chip = Chip()
    blk(chip, "LINE", 0, INC=1, MOD=6, T0=1, T1=3, T2=0xFFFF, SNAP=1, PINS=0,
        LUT1=lut(lambda i: ((i >> 1) & 1) ^ ((i >> 4) & 1)), LUT0=lut(lambda i: (i >> 1) & 1))
    run_line(chip, 0)
    rnd = random.Random(3)
    levels = [rnd.randint(0, 1) for _ in range(30)]
    prev_in = chip.lines[0].IN
    samples, ins = [], []
    for lv in levels:
        for _ in range(6):
            chip.step(IDLE, lv)
            ln = chip.lines[0]
            if ln.IN != prev_in:                 # state after the step: changes only with that cycle's snapshot
                assert ln.snap, "IN changed without a snapshot"
            if ln.snap:
                samples.append(ln.W >> 1 & 1)
                ins.append(ln.IN)
            prev_in = ln.IN
    assert len(samples) > 25
    # after snapshot j: IN0 = sample j, IN1 = sample j ^ REM, and REM = IN1 before the snapshot
    for j in range(1, len(samples)):
        assert ins[j] & 1 == samples[j]
        assert ins[j] >> 1 == samples[j] ^ (ins[j - 1] >> 1)
