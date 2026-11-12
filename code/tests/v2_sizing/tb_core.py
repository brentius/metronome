"""cocotb bench for the Metronome v2 pipelined core sizing block (sim/numerics/v2_sizing/rtl/md2_core_top.v).

Cycle convention: cycle k is the interval after rising clock edge k (clock period 10 ns, so k = sim_time // 10).
Inputs driven just after rising edge k are seen in cycle k; the monitor samples combinational outputs at the
falling edge of cycle k. Pipeline contract under test: BOTS/PLANS/V2_DESIGN.md section 4.6.
"""
from __future__ import annotations

import sys
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, RisingEdge
from cocotb.utils import get_sim_time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "code" / "md2"))
import machine as M  # noqa: E402  (code/md2/machine.py: v2 field positions and port indices)

PERIOD = 10
NT = 6


# ---------------------------------------------------------------- tiny assembler ----------------------------------
def asm(moves=(), cond="TRUE", jmode="next", imm=0, jcond="TRUE", pause=False) -> int:
    """64-bit md2 word. moves: up to three (guard, src, dst) names; unused moves are guard 'never'."""
    w = 0

    def put(name, v):
        nonlocal w
        f = M.FIELD[name]
        assert 0 <= v < (1 << f.width), (name, v)
        w |= v << f.lsb

    put("pause", int(pause))
    put("jmode", M.JMODES[jmode])
    put("imm", imm)
    put("cond", M.GUARD_ID[cond])
    put("jcond", M.JGUARD_ID[jcond])
    for m in range(3):
        g, s, d = moves[m] if m < len(moves) else ("never", "ZERO", "NULL")
        put(f"m{m}_guard", M.GUARDS[g])
        put(f"m{m}_src", M.SRC_ID[s])
        put(f"m{m}_dst", M.DST_ID[d])
    return w


def mark(v, dst="R0", **kw) -> int:
    """An instruction whose only move writes imm=v to dst, so the move log identifies it."""
    return asm(moves=[("always", "IMM", dst)], imm=v, **kw)


# ---------------------------------------------------------------- bench ------------------------------------------
class Bench:
    def __init__(self, dut):
        self.dut = dut
        self.cfg = [dict(core=0, line=0, w0c=0, w1c=0, w0h=0, w1h=0) for _ in range(NT)]
        self.log = {}          # cycle -> [core0, core1] each (xv, thread, line, [(dst, data) of enabled moves])

    @staticmethod
    def cycle() -> int:
        return int(get_sim_time("ns") // PERIOD)

    async def start(self):
        d = self.dut
        for name in ["run_g", "trig", "h_pc_we", "h_pc_d", "h_en_we", "h_en_d", "t_core", "t_line", "t_w0c",
                     "t_w1c", "t_w0h", "t_w1h", "pw_en", "pw_core", "pw_addr", "pw_data", "guards", "g_line",
                     "srcs", "l_in", "l_cap"]:
            getattr(d, name).value = 0
        cocotb.start_soon(Clock(d.clk, PERIOD, unit="ns").start(start_high=True))
        cocotb.start_soon(self._monitor())
        await self.reset()

    async def reset(self):
        d = self.dut
        d.run_g.value = 0
        d.trig.value = 0
        d.rst_n.value = 0
        await self.tick(3)
        d.rst_n.value = 1
        self.cfg = [dict(core=0, line=0, w0c=0, w1c=0, w0h=0, w1h=0) for _ in range(NT)]
        self.log = {}
        await self.tick()

    async def tick(self, n=1):
        for _ in range(n):
            await RisingEdge(self.dut.clk)

    async def _monitor(self):
        d = self.dut
        while True:
            await FallingEdge(d.clk)
            en = int(d.mv_en.value)
            dst = int(d.mv_dst.value)
            data = int(d.mv_data.value)
            xv = int(d.x_valid.value)
            xt = int(d.x_thread.value)
            xl = int(d.x_line.value)
            row = []
            for c in range(2):
                mv = [((dst >> (18 * c + 6 * m)) & 63, (data >> (24 * c + 8 * m)) & 255)
                      for m in range(3) if (en >> (3 * c + m)) & 1]
                row.append(((xv >> c) & 1, (xt >> (3 * c)) & 7, (xl >> (2 * c)) & 3, mv))
            self.log[self.cycle()] = row

    def apply_cfg(self):
        d = self.dut
        core = line = w0c = w1c = w0h = w1h = 0
        for k, c in enumerate(self.cfg):
            core |= c["core"] << k
            line |= c["line"] << (2 * k)
            w0c |= c["w0c"] << (6 * k)
            w1c |= c["w1c"] << (6 * k)
            w0h |= c["w0h"] << (8 * k)
            w1h |= c["w1h"] << (8 * k)
        d.t_core.value, d.t_line.value = core, line
        d.t_w0c.value, d.t_w1c.value, d.t_w0h.value, d.t_w1h.value = w0c, w1c, w0h, w1h

    async def load(self, prog: dict[int, int], core=0):
        d = self.dut
        for a, w in sorted(prog.items()):
            d.pw_en.value, d.pw_core.value, d.pw_addr.value, d.pw_data.value = 1, core, a, w
            await self.tick()
        d.pw_en.value = 0

    async def set_pc(self, k, pc):
        d = self.dut
        d.h_pc_we.value, d.h_pc_d.value = 1 << k, pc
        await self.tick()
        d.h_pc_we.value = 0

    async def enable_all(self):
        d = self.dut
        d.h_en_we.value, d.h_en_d.value = (1 << NT) - 1, 1
        await self.tick()
        d.h_en_we.value = 0

    async def setup(self, progs, pcs, cfg=None):
        """Load programs ({core: {addr: word}}), set thread PCs and configuration, enable threads, RUN on."""
        for k, c in (cfg or {}).items():
            self.cfg[k].update(c)
        self.apply_cfg()
        for core, p in progs.items():
            await self.load(p, core)
        for k, pc in pcs.items():
            await self.set_pc(k, pc)
        await self.enable_all()
        self.dut.run_g.value = 1
        await self.tick()

    async def trigger(self, mask) -> int:
        """Pulse trig[mask] for one cycle; returns that cycle t."""
        t = self.cycle()
        self.dut.trig.value = mask
        await self.tick()
        self.dut.trig.value = 0
        return t

    # -------- log queries
    def execs(self, core=0, start=0, end=None, thread=None):
        """[(cycle, thread, moves)] of cycles with an executing instruction on core."""
        out = []
        for cyc in sorted(self.log):
            if cyc < start or (end is not None and cyc > end):
                continue
            xv, xt, _xl, mv = self.log[cyc][core]
            if xv and (thread is None or xt == thread):
                out.append((cyc, xt, mv))
        return out

    def moves(self, core=0, start=0, end=None):
        """[(cycle, dst, data)] of enabled moves."""
        return [(cyc, dst, data) for cyc in sorted(self.log) if cyc >= start and (end is None or cyc <= end)
                for dst, data in self.log[cyc][core][3]]


R0, R1, R2, ACC_LD = M.DST_ID["R0"], M.DST_ID["R1"], M.DST_ID["R2"], M.DST_ID["ACC.LD"]


# ---------------------------------------------------------------- tests ------------------------------------------
@cocotb.test()
async def test_first_insn_t3(dut):
    """Trigger in cycle t on an idle core: the first instruction executes in t+3."""
    b = Bench(dut)
    await b.start()
    await b.setup({0: {10: mark(0xA5, pause=True)}}, {0: 10})
    t = await b.trigger(1 << 0)
    await b.tick(8)
    mv = b.moves(0, start=t)
    assert mv == [(t + 3, R0, 0xA5)], mv
    assert b.execs(0, start=t) == [(t + 3, 0, [(R0, 0xA5)])]
    assert int(dut.t_pc.value) & 0xFF == 11, "pause writes the sequential PC"


@cocotb.test()
async def test_sequential_one_per_cycle(dut):
    """A burst of n sequential instructions occupies t+3 .. t+n+2 with no gaps; not-taken jumps cost nothing."""
    b = Bench(dut)
    await b.start()
    prog = {10: mark(1), 11: mark(2, jmode="if", jcond="F0"), 12: mark(3, jmode="ifnot", jcond="TRUE"), 13: mark(4, pause=True)}
    await b.setup({0: prog}, {0: 10})
    t = await b.trigger(1)
    await b.tick(10)
    assert b.moves(0, start=t) == [(t + 3 + i, R0, i + 1) for i in range(4)], b.moves(0, start=t)


@cocotb.test()
async def test_taken_jump_one_idle_wrong_path_silent(dut):
    """Taken jump: the fetched-ahead word writes nothing, the target executes two cycles after the jump."""
    b = Bench(dut)
    await b.start()
    wrong = asm(moves=[("always", "IMM", "ACC.LD"), ("always", "IMM", "T.STOP"), ("always", "IMM", "R3")],
                imm=0x77, pause=True, jmode="always")
    prog = {10: mark(0x20, jmode="always"), 11: wrong, 0x20: mark(0x5A, dst="R1", pause=True)}
    await b.setup({0: prog}, {0: 10})
    t = await b.trigger(1)
    await b.tick(10)
    assert b.moves(0, start=t) == [(t + 3, R0, 0x20), (t + 5, R1, 0x5A)], b.moves(0, start=t)
    assert [e[0] for e in b.execs(0, start=t)] == [t + 3, t + 5]
    assert int(dut.t_en.value) & 1 == 1, "wrong-path T.STOP must not take effect"
    assert int(dut.t_pc.value) & 0xFF == 0x21


@cocotb.test()
async def test_jump_on_line_relative_guard(dut):
    """jcond L.IN0 selects the executing thread's line (line 2 here); other lines' guards are ignored."""
    b = Bench(dut)
    await b.start()
    prog = {10: mark(30, jmode="if", jcond="L.IN0"), 11: mark(2, pause=True), 30: mark(3, pause=True)}
    await b.setup({0: prog}, {0: 10}, {0: dict(line=2)})
    dut.g_line.value = 1 << 10                       # IN0 set on line 2 only (bit 5*line + 0)
    t = await b.trigger(1)
    await b.tick(8)
    assert b.moves(0, start=t) == [(t + 3, R0, 30), (t + 5, R0, 3)], b.moves(0, start=t)
    assert b.log[t + 3][0][2] == 2, "executing line id"
    dut.g_line.value = (1 << 0) | (1 << 5) | (1 << 15)   # IN0 set on lines 0, 1, 3 only
    await b.set_pc(0, 10)
    t = await b.trigger(1)
    await b.tick(8)
    assert b.moves(0, start=t) == [(t + 3, R0, 30), (t + 4, R0, 2)], b.moves(0, start=t)


@cocotb.test()
async def test_pause_writes_pc_and_resumes(dut):
    """pause writes the sequential PC or the jump target; the next trigger resumes there."""
    b = Bench(dut)
    await b.start()
    prog = {10: mark(1, pause=True), 11: mark(40, pause=True, jmode="always"), 40: mark(3, pause=True)}
    await b.setup({0: prog}, {0: 10})
    seen = []
    for expect_pc in (11, 40, 41):
        t = await b.trigger(1)
        await b.tick(6)
        seen += [d for _c, _dst, d in b.moves(0, start=t)]
        assert int(dut.t_pc.value) & 0xFF == expect_pc
    assert seen == [1, 40, 3], seen


@cocotb.test()
async def test_dispatch_after_pause_one_idle(dut):
    """Two ready threads on core 0: the second burst's first instruction executes two cycles after the pause."""
    b = Bench(dut)
    await b.start()
    prog = {10: mark(1), 11: mark(2, pause=True), 20: mark(7, pause=True)}
    await b.setup({0: prog}, {0: 10, 1: 20})
    t = await b.trigger(0b11)
    await b.tick(10)
    ex = [(c, th) for c, th, _m in b.execs(0, start=t)]
    assert ex == [(t + 3, 0), (t + 4, 0), (t + 6, 1)], ex


@cocotb.test()
async def test_round_robin_three_threads(dut):
    """Three continuously ready threads on core 0 are served in circular order with equal shares."""
    b = Bench(dut)
    await b.start()
    prog = {10: mark(10, pause=True, jmode="always"), 20: mark(1), 21: mark(20, pause=True, jmode="always"),
            30: mark(30, pause=True, jmode="always")}
    await b.setup({0: prog}, {0: 10, 1: 20, 2: 30})
    t = b.cycle()
    dut.trig.value = 0b111            # retrigger continuously (OVR is set while busy; irrelevant here)
    await b.tick(60)
    dut.trig.value = 0
    bursts = []
    for c, th, _m in b.execs(0, start=t):
        if not bursts or bursts[-1][1] != th or bursts[-1][0] != c - 1:
            bursts.append([c, th])
        else:
            bursts[-1][0] = c
    order = [th for _c, th in bursts]
    assert order[:9] == [0, 1, 2] * 3, order
    n = [order.count(k) for k in range(3)]
    assert max(n) - min(n) <= 1, n


@cocotb.test()
async def test_watcher_redirects_dispatch(dut):
    """W0C on a global guard and W1C on a line-relative guard redirect dispatch to W0H / W1H."""
    b = Bench(dut)
    await b.start()
    prog = {10: mark(1, pause=True), 50: mark(0xEE, pause=True), 60: mark(0xDD, pause=True)}
    cfg = {0: dict(line=1, w0c=M.GUARD_ID["F3"], w0h=50, w1c=M.GUARD_ID["L.PINA"], w1h=60)}
    await b.setup({0: prog}, {0: 10}, cfg)
    res = []
    for guards, gline in [(0, 0), (1 << M.GUARD_ID["F3"], 0), (0, 1 << (5 * 1 + 3)), (0, 1 << (5 * 0 + 3)),
                          (1 << M.GUARD_ID["F3"], 1 << (5 * 1 + 3))]:
        await b.set_pc(0, 10)
        dut.guards.value, dut.g_line.value = guards, gline
        t = await b.trigger(1)
        await b.tick(6)
        mv = b.moves(0, start=t)
        assert len(mv) == 1 and mv[0][0] == t + 3, mv
        res.append(mv[0][2])
    # no watcher; W0 (F3); W1 (line 1 PINA); line 0 PINA does not count; W0 has priority over W1
    assert res == [1, 0xEE, 0xDD, 1, 0xEE], [hex(x) for x in res]


async def _bound_run(b, n, m, off, warm):
    """Thread 0 (burst n) and thread 1 (burst m) on core 0. Thread 0 triggered at t, thread 1 at t+off.
    Returns (last instruction cycle of thread 0) - t."""
    dut = b.dut
    await b.reset()
    prog = {10 + i: mark(i) for i in range(n - 1)}
    prog[10 + n - 1] = mark(10, pause=True, jmode="always")          # imm doubles as the loop target
    prog.update({40 + i: mark(0x40 + i, dst="R1") for i in range(m - 1)})
    prog[40 + m - 1] = mark(40, dst="R1", pause=True, jmode="always")
    await b.setup({0: prog}, {0: 10, 1: 40})
    if warm:                            # one thread-0 burst first, so RR prefers thread 1 next
        await b.trigger(1)
        await b.tick(n + 6)
    start = b.cycle()
    t = None
    for k in range(min(off, 0), max(off, 0) + 1):
        mask = (1 if k == 0 else 0) | (2 if k == off else 0)
        if k == 0:
            t = b.cycle()
        dut.trig.value = mask
        await b.tick()
    dut.trig.value = 0
    await b.tick(n + m + 12)
    ex0 = [c for c, _th, _m in b.execs(0, start=start, thread=0)]
    assert len(ex0) == n, (ex0, off, warm)
    return ex0[-1] - t


@cocotb.test()
async def test_response_bound_two_threads(dut):
    """Measured trigger-to-last-instruction for thread 0 over all trigger offsets of a peer and both RR states
    is at most n + 2 + (m + 1), with the worst case recorded."""
    n, m = 2, 3
    bound = n + 2 + (m + 1)
    worst = []
    b = Bench(dut)
    await b.start()
    for warm in (False, True):
        for off in range(-(m + 4), 3):
            r = await _bound_run(b, n, m, off, warm)
            assert r <= bound, (r, bound, off, warm)
            worst.append((r, off, warm))
    w = max(worst)
    dut._log.info("response bound n=%d m=%d: bound %d, measured worst %d at peer offset %d (warm=%s); all=%s",
                  n, m, bound, w[0], w[1], w[2], sorted(worst, reverse=True)[:6])
    assert w[0] == bound, "the bound should be tight for this pipeline"


@cocotb.test()
async def test_core1_threads_ignored_by_core0(dut):
    """A thread bound to core 1 is never executed by core 0; it runs from core 1's program memory."""
    b = Bench(dut)
    await b.start()
    p0 = {10: mark(0x11, pause=True), 20: mark(0x99, pause=True)}
    p1 = {20: mark(0x33, pause=True)}
    await b.setup({0: p0, 1: p1}, {0: 10, 3: 20}, {3: dict(core=1, line=3)})
    t = await b.trigger((1 << 0) | (1 << 3))
    await b.tick(8)
    assert [(c, th) for c, th, _m in b.execs(0, start=t)] == [(t + 3, 0)]
    assert b.moves(1, start=t) == [(t + 3, R0, 0x33)], b.moves(1, start=t)
    assert b.log[t + 3][1][1:3] == (3, 3)
