"""v4 additions in the metronome2 cycle model (wiki/SPEC_V2.md section 13, model only; no RTL yet):
configuration written by the cores (13.1, `CW.AL`, `CW.AH`, `CW.D`) and edge replay from S0 (13.2, `ECTL.RPL`, `RLV`).

Each feature has a check function; `test_mutant_*` runs a check against an obvious mutant of the model and requires
it to fail.

    python -m pytest code/tests/md2/test_v4_model.py -q
"""
from __future__ import annotations

import random
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
sys.path[:0] = [str(ROOT / "sim/reference"), str(ROOT / "sim/reference/tests_v2")]

from metronome2 import Chip, asm, m, spi  # noqa: E402
from metronome2 import chip as chip_mod, regs as regs_mod  # noqa: E402
from helpers_v2 import IDLE, blk, steps, thread  # noqa: E402

I = asm.insn
LINE1_INC = m.HOST_MAP["LINE_BASE"] + m.HOST_STRIDE["LINE"] * 1 + 0x00


def cw_program(writes, gap=1, stop=True):
    """Instructions writing (addr, byte) pairs through CW: AL, AH, then D; `gap` NULL instructions between D moves."""
    prog = []
    for a, v in writes:
        prog += [I(("IMM", "CW.AL"), imm=a & 0xFF), I(("IMM", "CW.AH"), imm=a >> 8)]
        prog += [I(("IMM", "CW.D"), imm=v)] + [I()] * gap
    prog.append(I(("ZERO", "T.STOP"), pause=1) if stop else I(pause=1))
    return prog


def start(ch, prog, core=0, t=0):
    ch.load_program(core, prog)
    thread(ch, t, core=core, trig="ALWAYS")
    blk(ch, "CTRL", RUN=1)


def d_cycles(ch):
    """Cycles in which a CW.D move executed."""
    did = m.DST_ID["CW.D"]
    out = []
    for cyc, c, t, pc in ch.trace:
        w = ch.cores[c].prog[pc]
        if any(((w >> m.FIELD[f"m{i}_dst"].lsb) & 63) == did for i in range(m.N_MOVES)):
            out.append(cyc)
    return out


# ================================================================================================ 13.1 CW
def check_cw_timing():
    """A CW.D executed in cycle t is visible to the logic from t+3 (pending at t+1, bank write in t+1, then the
    W+2 latch rule)."""
    ch = Chip()
    steps(ch, 3)
    start(ch, cw_program([(LINE1_INC, 0x5A)]))
    seen = None
    for _ in range(40):
        before = ch.cycle
        ch.step(IDLE)
        if seen is None and ch.lines[1].INC == 0x5A:
            seen = before + 1                      # first cycle in which the logic sees it
    (t,) = d_cycles(ch)
    assert seen == t + 3, (seen, t)
    assert not ch.ctrl.CWOVR and ch.contract_violations == []


def test_cw_timing():
    check_cw_timing()


def test_mutant_cw_drains_without_bank_rule(monkeypatch):
    # mutant: the drained write is applied one cycle early (no pipeline stage) -> timing check fails
    orig = chip_mod.Chip._bank

    def early(self, hw, hdec, core_ok):
        bank, rt, drain = orig(self, hw, hdec, core_ok)
        if bank is not None and drain:
            regs_mod.apply_config(self, *bank)
        return bank, rt, drain
    monkeypatch.setattr(chip_mod.Chip, "_bank", early)
    with pytest.raises(AssertionError):
        check_cw_timing()


def test_cw_rate_and_overrun():
    # one write per two cycles is sustained; three CW.D in consecutive cycles lose the third (CWOVR)
    ch = Chip()
    steps(ch, 3)
    a = LINE1_INC
    prog = [I(("IMM", "CW.AL"), imm=a & 0xFF), I(("IMM", "CW.AH"), imm=a >> 8)]
    prog += [I(("IMM", "CW.D"), imm=0x11), I(), I(("IMM", "CW.D"), imm=0x22), I(),
             I(("ZERO", "T.STOP"), pause=1)]
    start(ch, prog)
    steps(ch, 30)
    assert ch.lines[1].INC == 0x2211 and not ch.ctrl.CWOVR
    ch = Chip()
    steps(ch, 3)
    prog = [I(("IMM", "CW.AL"), imm=a & 0xFF), I(("IMM", "CW.AH"), imm=a >> 8)]
    prog += [I(("IMM", "CW.D"), imm=1), I(("IMM", "CW.D"), imm=2), I(("IMM", "CW.D"), imm=3),
             I(("ZERO", "T.STOP"), pause=1)]
    start(ch, prog)
    steps(ch, 30)
    assert ch.ctrl.CWOVR == 1
    assert regs_mod.errsum(ch) >> 6 & 1 and regs_mod.read(ch, m.HOST_MAP["CTRL_BASE"] + 1) >> 2 & 1
    assert ch.lines[1].INC == 0x0201              # first two landed, the third was dropped
    blk(ch, "CTRL", STICKY=4)
    assert ch.ctrl.CWOVR == 0


def test_cw_runtime_and_unmapped():
    # CW reaches the DBG runtime registers ECTL/EMASK/RLV; other non-configuration addresses are ignored
    ch = Chip()
    steps(ch, 3)
    dbg = m.HOST_MAP["DBG_BASE"]
    start(ch, cw_program([(dbg + 0x08, 0x0F), (dbg + 0x12, 0x05), (m.HOST_MAP["CTRL_BASE"], 0),
                          (m.HOST_MAP["DATA_BASE"], 0x77)], gap=2))
    steps(ch, 60)
    assert ch.EMASK == 0x0F and ch.RLV == 0x05
    assert ch.ctrl.RUN == 1 and ch.mem.data[0] == 0 and not ch.ctrl.CWOVR


def test_cw_contract_flags_core_writes():
    ch = Chip()
    steps(ch, 3)
    blk(ch, "LRT", 1, CTL=1)                      # line 1 runs
    start(ch, cw_program([(LINE1_INC, 3)]))
    steps(ch, 20)
    assert any(r.startswith("core: line 1") for _, _, r in ch.contract_violations)


def check_bank_spacing_random(seed):
    """Random CW.D streams from both cores against host SPI configuration writes: the bank is never written in two
    consecutive cycles, and every accepted write lands exactly once, in order per source."""
    rnd = random.Random(seed)
    ch = Chip()
    steps(ch, 3)
    base = m.HOST_MAP["THREAD_BASE"] + m.HOST_STRIDE["THREAD"] * 5       # thread 5 W0H..: unused by the program
    targets = [m.HOST_MAP["LINE_BASE"] + 0x20 * l + o for l in (2, 3) for o in range(0, 16)]
    for c in (0, 1):
        prog = []
        for _ in range(12):
            a = rnd.choice(targets)
            prog += [I(("IMM", "CW.AL"), imm=a & 0xFF), I(("IMM", "CW.AH"), imm=a >> 8),
                     I(("IMM", "CW.D"), imm=rnd.randrange(256))]
            prog += [I()] * rnd.choice([0, 0, 1, 2])
        prog.append(I(("ZERO", "T.STOP"), pause=1))
        ch.load_program(c, prog)
        thread(ch, c, core=c, trig="ALWAYS")
    log, prev = [], []
    orig = ch._bank

    def spy(hw, hdec, core_ok):
        r = orig(hw, hdec, core_ok)
        log.append(r[0])
        return r
    ch._bank = spy
    blk(ch, "CTRL", RUN=1)
    for _ in range(6):
        ch.run(spi.write_frames(base + 3, [rnd.randrange(256)], half_period=rnd.choice([1, 2, 8])))
    steps(ch, 200)
    for x, y in zip(log, log[1:]):
        assert x is None or y is None, "bank written in consecutive cycles"
    host_writes = [w for w in log if w is not None and w[0] == base + 3]
    assert len(host_writes) == 6
    return ch


@pytest.mark.parametrize("seed", range(8))
def test_bank_spacing_random(seed):
    check_bank_spacing_random(seed)


def test_mutant_bank_spacing(monkeypatch):
    orig = chip_mod.Chip._bank

    def nospace(self, hw, hdec, core_ok):
        self.BWP = 0
        return orig(self, hw, hdec, core_ok)
    monkeypatch.setattr(chip_mod.Chip, "_bank", nospace)
    with pytest.raises(AssertionError):
        for s in range(8):
            check_bank_spacing_random(s)


# ================================================================================================ 13.2 replay
def capture(ch, waves, pin_mask, n):
    """Run n cycles with raw uio values from waves(t); return lv per cycle."""
    out = []
    for t in range(n):
        ch.step(IDLE, waves(t))
        out.append(ch.lv)
    return out


def check_replay_mirror(seed, min_gap=3):
    rnd = random.Random(seed)
    ch = Chip()
    steps(ch, 3)
    pin = 3
    tog, t = set(), 40
    while t < 1800:
        tog.add(t)
        t += rnd.randint(min_gap, 40)
    level, lvl_at = 1, {}
    for t in range(2000):
        if t in tog:
            level ^= 1
        lvl_at[t] = level
    wave = lambda t: lvl_at[t] << pin
    steps(ch, 4, uio=1 << pin)                   # idle high, synchronised
    blk(ch, "STREAM", 0, MODE=1, START=0, LEN=2048)
    blk(ch, "SRT", 0, CTL=1)
    blk(ch, "DBG", EMASK=1 << pin, ECTL=1)
    cap = capture(ch, wave, 1 << pin, 2000)
    n_rec = ch.mem.streams[0].POS // 4
    assert not ch.mem.streams[0].STARVED and n_rec == len(tog)
    # replay: pads held low (the replay must not see them), RLV = the idle level
    blk(ch, "DBG", ECTL=0)
    blk(ch, "STREAM", 0, MODE=0, START=0, LEN=4 * n_rec)
    blk(ch, "SRT", 0, CTL=1)
    blk(ch, "DBG", RLV=1 << pin, ECTL=2)
    rep = capture(ch, lambda t: 0, 1 << pin, 2000)
    s0 = ch.mem.streams[0]
    mism = [i for i in range(2000) if (cap[i] >> pin) & 1 != (rep[i] >> pin) & 1]
    return mism, s0


@pytest.mark.parametrize("seed", range(6))
def test_replay_mirrors_capture(seed):
    mism, s0 = check_replay_mirror(seed)
    assert mism == [] and not s0.STARVED and s0.END


def test_replay_short_intervals_starve():
    mism, s0 = check_replay_mirror(1, min_gap=1)
    assert s0.STARVED


def test_mutant_replay_off_by_one(monkeypatch):
    orig = chip_mod.Chip._levels

    def lag(self):
        lv, rs, fl = orig(self)
        if self.RPL:
            mk = self.EMASK
            lv = (lv & ~mk) | (self.RLVP & mk)
        return lv, rs, fl
    monkeypatch.setattr(chip_mod.Chip, "_levels", lag)
    mism, _ = check_replay_mirror(0)
    assert mism != []


def test_replay_drives_edge_triggers():
    # replayed edges are machine edges: a PINA.FALL thread counts them
    ch = Chip()
    steps(ch, 3)
    for i, (dc, lvl) in enumerate([(50, 0), (10, 1), (10, 0), (10, 1)]):
        ch.mem.data[4 * i:4 * i + 4] = ((dc << 13) | (lvl << 3)).to_bytes(4, "little")
    blk(ch, "LINE", 0, PINS=3)
    x = I(("IMM", "ACC.ADD"), imm=1, pause=1, jmode="always")     # pauses back at word 1 (imm is the target too)
    ch.load_program(0, [x, x])
    thread(ch, 0, trig="PINA.FALL")
    blk(ch, "CTRL", RUN=1)
    blk(ch, "STREAM", 0, MODE=0, START=0, LEN=16)
    blk(ch, "SRT", 0, CTL=1)
    blk(ch, "DBG", EMASK=1 << 3, RLV=1 << 3, ECTL=2)
    steps(ch, 120, uio=1 << 3)
    assert ch.acc.A == 2
    assert regs_mod.read(ch, m.HOST_MAP["DBG_BASE"] + 2) == 2
