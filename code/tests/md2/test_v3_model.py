"""v3 additions in the metronome2 cycle model (wiki/SPEC_V2.md section 12): live-pin table inputs (12.1), the
execution digest (12.2), freeze/step/readback (12.3), edge capture into S0 (12.4) and the program-load contract
diagnostic (12.5).

Each feature has a check function. The `test_*` cases run it on the model; the `test_mutant_*` cases run the same
check against an obvious mutant of the model (monkeypatched) and require it to fail (red/green on the checks).

    python -m pytest code/tests/md2/test_v3_model.py -q
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
sys.path[:0] = [str(ROOT / "sim/reference"), str(ROOT / "sim/reference/tests_v2")]

from metronome2 import Chip, asm, m, spi  # noqa: E402
from metronome2 import chip as chip_mod, memory as mem_mod, regs as regs_mod  # noqa: E402
from helpers_v2 import IDLE, blk, lut, run_line, steps, thread  # noqa: E402

I = asm.insn


def dbg_addr(name):
    for off, r in m.DBG_REGS.items():
        if r[0] == name:
            return m.HOST_MAP["DBG_BASE"] + off
    raise KeyError(name)


def rd(ch, name, n=1):
    a = dbg_addr(name)
    return int.from_bytes(bytes(regs_mod.read(ch, a + k) for k in range(n)), "little")


# ================================================================================================ 12.1 live pins
def check_live_pin():
    ch = Chip()
    steps(ch, 3)
    blk(ch, "LINE", 0, PINS=3 | (5 << 4))                   # PINA = P3, PINB = P5; the line need not run
    blk(ch, "OUT", 0, BIND=0b100 | (1 << 3), LUT=lut(lambda i: (i >> 2) & 1), OE=lut(lambda i: 1 - ((i >> 2) & 1)))
    blk(ch, "OUT", 1, BIND=0b100 | (2 << 3), LUT=lut(lambda i: (i >> 1) & 1))
    blk(ch, "OUT", 2, BIND=0b100, LUT=lut(lambda i: (i >> 2) & 1))   # LIVE = 0: v2, COMMITTED = 0
    seq3 = [0, 1, 1, 0, 1, 0, 0, 0, 1, 1]
    seq5 = [1, 0, 0, 1, 1, 1, 0, 1, 0, 0]
    outs = [ch.step(IDLE, (a << 3) | (b << 5)) for a, b in zip(seq3 + [0, 0], seq5 + [0, 0])]
    for t in range(len(seq3)):
        _, uio, oe = outs[t + 2]                  # raw in cycle t -> PIN in t+2 -> output register after t+2
        assert uio & 1 == seq3[t], t
        assert (oe & 1) == 1 - seq3[t], t
        assert (uio >> 1) & 1 == seq5[t], t
        assert (uio >> 2) & 1 == 0, t


def test_live_pin():
    check_live_pin()


def test_mutant_live_pin_ignored(monkeypatch):
    def v2_compute(self, ch):
        if not self.BOUND:
            return 0, 0
        ln = ch.lines[self.LINE]
        c = ln.COMMITTED
        idx = (ln.SEG << 3) | (((c >> self.SEL[2]) & 1) << 2) | (((c >> self.SEL[1]) & 1) << 1) | ((c >> self.SEL[0]) & 1)
        return (self.LUT >> idx) & 1, (self.OE >> idx) & 1
    monkeypatch.setattr(chip_mod.OutPin, "compute", v2_compute)
    with pytest.raises(AssertionError):
        check_live_pin()


# ================================================================================================ 12.2 digest
def misr_ref(mv, d):
    """Independent form: M(x) * x + D(x) mod P(x), with P = x^32 + 0x04C11DB7."""
    v = (mv << 1) ^ d
    if v >> 32:
        v ^= (1 << 32) | 0x04C11DB7
    return v


def busy_chip():
    """A running line with taps and a counting thread, so pins and OEs change every few cycles."""
    ch = Chip()
    steps(ch, 3)
    blk(ch, "LINE", 0, INC=1, MOD=5, T0=0, T1=2, T2=0xFFFF)
    for o in range(14):
        kw = dict(BIND=0b100, SEL=(o % 4) | ((o + 1) % 4) << 2 | ((o + 2) % 4) << 4, LUT=0x9A5C3F61 ^ (o * 0x01110111))
        if o < 8:
            kw["OE"] = 0x3C5A0FF0 ^ (o * 0x00100101)
        blk(ch, "OUT", o, **kw)
    ch.load_program(0, [I(("IMM", "ACC.ADD"), ("ACC", "L.SYM"), imm=3, pause=1)])
    thread(ch, 0, trig="L0.BEAT")
    blk(ch, "CTRL", RUN=1)
    run_line(ch, 0)
    return ch


def check_digest():
    ch = busy_chip()
    blk(ch, "DBG", MCTL=1)
    exp = 0
    prev = ch.outputs()
    for t in range(400):
        _, uio, oe = prev
        d = sum(ch.out[o].OUT << o for o in range(14)) | (oe << 14)
        assert d & 0xFF == uio
        exp = misr_ref(exp, d)
        prev = ch.step(IDLE)
    assert rd(ch, "MISR", 4) == exp
    assert exp != 0
    # MEN = 0 holds; MCTL bit 1 clears
    blk(ch, "DBG", MCTL=0)
    steps(ch, 20)
    assert rd(ch, "MISR", 4) == exp
    blk(ch, "DBG", MCTL=2)
    assert rd(ch, "MISR", 4) == 0


def test_digest():
    check_digest()


def test_digest_reset_default_is_v2():
    ch = busy_chip()
    steps(ch, 100)
    assert rd(ch, "MISR", 4) == 0 and rd(ch, "MCTL") == 0


def test_mutant_digest_poly(monkeypatch):
    monkeypatch.setattr(m, "MISR_POLY", 0xEDB88320)
    with pytest.raises(AssertionError):
        check_digest()


def test_mutant_digest_bit_order(monkeypatch):
    def pins_word(self):
        return sum(o.OUT << o.o for o in self.out) | sum(o.OEN << (8 + o.o) for o in self.out[:8])
    monkeypatch.setattr(chip_mod.Chip, "_pins_word", pins_word)
    with pytest.raises(AssertionError):
        check_digest()


# ================================================================================================ 12.3 freeze
def snapshot(ch):
    ln = [(l.PH, l.RUN, l.FIRED, l.HELD, l.STAGED, l.COMMITTED, l.TAPMISS, l.SP, l.SC, l.W, l.SN, l.REM)
          for l in ch.lines]
    th = [(t.PC, t.EN, t.READY, t.RUNNING, t.ARMED, t.LATE, t.OVR) for t in ch.threads]
    co = [(c.XV, c.RV, c.IR, c.FPC, c.XT, c.XL, c.RR) for c in ch.cores]
    st = [(s.POS, s.BIDX, s.BA, s.CUR, s.CV, s.WV, s.RQ, s.LD, s.PEND, s.PV, s.STARVED) for s in ch.mem.streams]
    return (ln, th, co, st, ch.acc.A, ch.flags.F, ch.flags.FP, ch.MISR, ch.mem.ptr.PTR, ch.mem.ptr.RDY,
            ch.ctrl.CONFLICT, ch.ctrl.MEMHAZ)


def stream_chip():
    """busy_chip plus a transmit stream advanced from core 1 and a pointer read loop, to cover RAM landings."""
    ch = busy_chip()
    ch.mem.data[0:16] = bytes(range(0x30, 0x40))
    blk(ch, "STREAM", 0, MODE=0, START=0, LEN=16)
    blk(ch, "SRT", 0, CTL=1)
    blk(ch, "LINE", 1, INC=1, MOD=3, T0=1, T1=0xFFFF, T2=0xFFFF)
    blk(ch, "OUT", 9, BIND=0b101, LUT=lut(lambda i: i & 1))
    ch.load_program(1, [I(("S0.BIT", "L.DBIT"), ("ZERO", "S0.ADV"), ("IMM", "P0.R"), imm=0, pause=1)])
    thread(ch, 1, core=1, line=1, trig="L1.TAP0")
    run_line(ch, 1)
    blk(ch, "DBG", MCTL=1)
    return ch


def check_freeze_transparent(frozen_at=(17, 18, 19, 40, 41, 77, 120, 121, 122, 123)):
    a, b = stream_chip(), stream_chip()
    sa, sb = [], []
    for t in range(200):
        sa.append(a.step(IDLE))
        sb.append(b.step(IDLE))
        if t in frozen_at:                         # insert frozen cycles in b: outputs and state must hold
            b.FREEZE = b.FRZ = 1
            s0, o0 = snapshot(b), sb[-1]
            for _ in range(3):
                assert b.step(IDLE) == o0
            assert snapshot(b) == s0
            b.FREEZE = b.FRZ = 0
            b.FRZD = 1
    assert sa == sb
    assert snapshot(a) == snapshot(b)


def test_freeze_transparent():
    check_freeze_transparent()


def test_mutant_freeze_pins_not_held(monkeypatch):
    orig = Chip._step_frozen

    def leaky(self, raw):
        out_next = [o.compute(self) for o in self.out]
        r = orig(self, raw)
        for o, (v, oe) in zip(self.out, out_next):
            o.OUT, o.OEN = v ^ 1, oe
        return self.outputs()
    monkeypatch.setattr(Chip, "_step_frozen", leaky)
    with pytest.raises(AssertionError):
        check_freeze_transparent()


def check_step_over_spi():
    """FREEZE over SPI, then STEP: exactly one machine cycle per step (12.3); readback while frozen."""
    ch = busy_chip()
    ch.run(spi.write_frames(dbg_addr("DBG"), [1], 2))
    assert ch.FRZ == 1
    ph0 = ch.lines[0].PH
    for _ in range(7):
        ch.run(spi.write_frames(dbg_addr("DBG"), [3], 2))
        assert ch.FRZ == 1
    assert ch.lines[0].PH == (ph0 + 7) % 5
    cst = spi.spi_read(ch, dbg_addr("CST"), 4)
    assert cst[0] == (ch.cores[0].XT | ch.cores[0].XV << 3 | ch.cores[0].RV << 4)
    assert cst[2] == ch.cores[0].FPC
    assert spi.spi_read(ch, dbg_addr("ACC"), 1) == [ch.acc.A]
    ch.run(spi.write_frames(dbg_addr("DBG"), [0], 2))
    assert ch.FRZ == 0


def test_step_over_spi():
    check_step_over_spi()


def test_mutant_step_two_cycles(monkeypatch):
    def upd(self):
        self.FRZD = self.FRZ
        if self.dbg_write is not None and self.dbg_write[1]:
            self.FRZ, self.FREEZE = 0, 1
            self._mut_pending = True
        elif getattr(self, "_mut_pending", False):
            self._mut_pending = False
            self.FRZ = 0                              # mutant: the step runs two cycles
        else:
            self.FRZ = self.FREEZE
    monkeypatch.setattr(Chip, "_freeze_update", upd)
    with pytest.raises(AssertionError):
        check_step_over_spi()


def test_doorbell_held_through_freeze():
    ch = busy_chip()
    ch.load_program(1, [I(("IMM", "R2"), imm=0x5A, pause=1)])
    thread(ch, 2, core=1, trig="NONE")
    blk(ch, "DBG", DBG=1)
    blk(ch, "CTRL", DOORBELL=1 << 2)
    steps(ch, 30)
    assert ch.acc.R[2] == 0 and ch.DB == 1 << 2
    blk(ch, "DBG", DBG=0)
    steps(ch, 6)
    assert ch.acc.R[2] == 0x5A


# ================================================================================================ 12.4 edge capture
def check_edge_capture():
    ch = Chip()
    steps(ch, 3)
    blk(ch, "STREAM", 0, MODE=1, START=0x100, LEN=4 * 6)
    blk(ch, "SRT", 0, CTL=1)
    blk(ch, "DBG", EMASK=0b1001, ECTL=1)                   # P0 and P3
    # toggles of P0/P3 at raw cycles; P1 toggles too but is masked
    tog = {5: 0b1, 6: 0b1, 7: 0b1000, 30: 0b1001, 31: 0b10, 200: 0b1, 300: 0b1, 400: 0b1}
    v, lv_at = 0, {}
    for t in range(420):
        v ^= tog.get(t, 0)
        lv_at[t] = v
        ch.step(IDLE, v)
    # edge events in cycle t+2 for a raw change in cycle t; DC counts from the first CEN cycle (DC = 0 there)
    ev = [t for t in sorted(tog) if tog[t] & 0b1001][:6]
    recs = [int.from_bytes(ch.mem.data[0x100 + 4 * i:0x104 + 4 * i], "little") for i in range(6)]
    assert recs[0] & 0x1FFF == lv_at[ev[0]] & 0x1FFF
    for i in range(1, 6):
        assert recs[i] & 0x1FFF == lv_at[ev[i]] & 0x1FFF, i
        assert recs[i] >> 13 == ev[i] - ev[i - 1], (i, recs[i] >> 13)
    s = ch.mem.streams[0]
    assert s.POS == 24 and s.END and not s.STARVED          # back-to-back edges (5, 6, 7) never starve
    assert int.from_bytes(ch.mem.data[0x118:0x11C], "little") == 0     # the event after END is not written


def test_edge_capture():
    check_edge_capture()


def test_mutant_edge_capture_ignores_end(monkeypatch):
    orig = mem_mod.Stream._commit_capture

    def no_end(self, g, rec, ctl, end):
        return orig(self, g, rec, ctl, False)
    monkeypatch.setattr(mem_mod.Stream, "_commit_capture", no_end)
    with pytest.raises(AssertionError):
        check_edge_capture()


def test_edge_capture_starves_only_behind_a_frozen_or_lower_priority_port():
    # S0 has top priority: pushes every cycle never starve (12.4); here every cycle toggles for 40 cycles
    ch = Chip()
    steps(ch, 3)
    blk(ch, "STREAM", 0, MODE=1, START=0, LEN=2048)
    blk(ch, "SRT", 0, CTL=1)
    blk(ch, "DBG", EMASK=1, ECTL=1)
    for t in range(40):
        ch.step(IDLE, t & 1)
    steps(ch, 4)
    s = ch.mem.streams[0]
    assert s.POS == 4 * 40 and not s.STARVED and not s.PV
    for i in range(1, 39):
        assert int.from_bytes(ch.mem.data[4 * i:4 * i + 4], "little") >> 13 == 1


# ================================================================================================ 12.5 contract
def check_contract():
    ch = busy_chip()
    assert ch.contract_violations == []
    ch.run(spi.write_frames(m.HOST_MAP["LINE_BASE"] + 2, [7], 2))          # line 0 runs: violation
    assert len(ch.contract_violations) == 1 and "line 0" in ch.contract_violations[0][2]
    ch.run(spi.write_frames(m.HOST_MAP["LINE_BASE"] + 0x20 + 2, [7], 2))   # line 1 idle: fine
    ch.run(spi.write_frames(m.HOST_MAP["THREAD_BASE"] + 1, [0], 2))        # thread 0 enabled: violation
    ch.run(spi.write_frames(m.HOST_MAP["PROG_BASE"] + 8, [0], 2))          # program while RUN_global
    assert [v[2].split()[0] for v in ch.contract_violations] == ["line", "thread", "core"]


def test_contract():
    check_contract()


def test_mutant_contract_silent(monkeypatch):
    monkeypatch.setattr(Chip, "_contract", lambda self, hdec, hw: None)
    with pytest.raises(AssertionError):
        check_contract()


# ------------------------------------------------------------------------------------------------ 12.4 DC details
def check_dc_restart_in_freeze():
    """ECTL 0 then 1 inside one freeze, with a rewind: DC restarts at 0 (an ECTL write clears it)."""
    ch = Chip()
    steps(ch, 3)
    blk(ch, "STREAM", 0, MODE=1, START=0, LEN=64)
    blk(ch, "DBG", EMASK=1, ECTL=1)
    blk(ch, "SRT", 0, CTL=1)
    steps(ch, 50)
    assert ch.DC == 50
    ch.run(spi.write_frames(dbg_addr("DBG"), [1], 2))
    for v in (0, 1):
        ch.run(spi.write_frames(dbg_addr("ECTL"), [v], 2))
    ch.run(spi.write_frames(m.HOST_MAP["SRT_BASE"] + 2, [1], 2))
    assert ch.FRZ and ch.DC == 0 and ch.CEN == 1
    ch.run(spi.write_frames(dbg_addr("DBG"), [0], 2))
    assert 0 < ch.DC < 60


def test_dc_restart_in_freeze():
    check_dc_restart_in_freeze()


def test_mutant_dc_not_cleared_by_ectl(monkeypatch):
    orig = regs_mod.write_runtime

    def keep_dc(ch, addr, v):
        dc = ch.DC
        orig(ch, addr, v)
        ch.DC = dc
    monkeypatch.setattr(regs_mod, "write_runtime", keep_dc)
    with pytest.raises(AssertionError):
        check_dc_restart_in_freeze()


def check_dc_saturates():
    ch = Chip()
    steps(ch, 3)
    blk(ch, "STREAM", 0, MODE=1, START=0, LEN=64)
    blk(ch, "DBG", EMASK=1, ECTL=1)
    blk(ch, "SRT", 0, CTL=1)
    ch.DC = (1 << 19) - 4                                  # state set directly: 524k cycles are not simulated
    steps(ch, 10)
    assert ch.DC == 0x7FFFF
    for t in range(4):
        ch.step(IDLE, t & 1)                               # edges: record carries the saturated count, DC restarts
    steps(ch, 3)
    assert int.from_bytes(ch.mem.data[0:4], "little") >> 13 == 0x7FFFF
    assert 0 < ch.DC < 8


def test_dc_saturates():
    check_dc_saturates()


def test_mutant_dc_wraps(monkeypatch):
    monkeypatch.setattr(m, "ECAP_DC_BITS", 20)              # saturates at 2^20 - 1 instead
    with pytest.raises(AssertionError):
        check_dc_saturates()
