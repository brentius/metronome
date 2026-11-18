"""cocotb unit tests of the v2 RTL blocks (one test per toplevel; BLOCK selects which run).

md2_line and md2_stream run block-level lockstep against the metronome2 model's own Line and Stream classes under
seeded random configuration and stimulus, comparing every architectural register every cycle. md2_cfg_bank,
md2_mem and md2_host get directed checks of their timing contracts (SPEC_V2 1, 6.2, 9).
"""
from __future__ import annotations

import os
import random
import sys
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge, Timer

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "sim/reference"))
from metronome2 import m  # noqa: E402
from metronome2.line import Line  # noqa: E402
from metronome2.memory import Stream  # noqa: E402

BLOCK = os.environ.get("BLOCK", "")
SEEDS = int(os.environ.get("BLOCK_SEEDS", "6"))


def v(sig):
    x = sig.value
    assert x.is_resolvable, f"{sig._name} unresolved"
    return int(x)


async def clock(dut):
    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start())
    await FallingEdge(dut.clk)


# ================================================================================================== md2_line
def rand_line_cfg(rnd):
    mod = rnd.randint(3, 30)
    tap = lambda: rnd.choice([rnd.randrange(mod), rnd.randrange(mod), mod + rnd.randrange(3)])
    b = bytearray(32)
    vals = dict(INC=1 if rnd.random() < 0.7 else rnd.randint(1, mod - 1), MOD=mod, T0=tap(), T1=tap(), T2=tap(),
                PRE=rnd.randrange(mod), WLO=rnd.randrange(mod), WHI=rnd.randrange(mod))
    for off, (name, nb, _, _) in m.LINE_REGS.items():
        if name in vals:
            b[off:off + nb] = vals[name].to_bytes(nb, "little")
    for name in ("EDGE", "T0EDGE", "PINS", "SNAP", "HOLD"):
        off = next(o for o, r in m.LINE_REGS.items() if r[0] == name)
        b[off] = rnd.randrange(256)
    t0e = next(o for o, r in m.LINE_REGS.items() if r[0] == "T0EDGE")
    b[t0e] &= 0x7F
    if rnd.random() < 0.6:
        b[t0e] &= ~0x40
    for name in ("LUT0", "LUT1"):
        off = next(o for o, r in m.LINE_REGS.items() if r[0] == name)
        b[off:off + 4] = rnd.getrandbits(32).to_bytes(4, "little")
    return b


def line_state(ln):
    return dict(ph=ln.PH, run=ln.RUN, arm=ln.ARM, ren=ln.REN, fired=ln.FIRED, held=ln.HELD, staged=ln.STAGED,
                committed=ln.COMMITTED, tapmiss=ln.TAPMISS, sp=ln.SP, beat=ln.beat, tap=ln.tap[0] | ln.tap[1] << 1
                | ln.tap[2] << 2, in_sym=ln.IN, cap=ln.CAP)


async def line_run(dut, seed, cycles=3000):
    rnd = random.Random(seed)
    ln = Line(0)
    cfg = rand_line_cfg(rnd)
    ln.cfg[:] = cfg
    ln.decode()
    ln.run_t = 0
    dut.cfg.value = int.from_bytes(bytes(cfg), "little")
    pins_p = [rnd.choice([2, 3, 5, 9, 30]) for _ in range(13)]
    lv = sp = rnd.getrandbits(13)
    errors = 0
    for t in range(cycles):
        if rnd.random() < 0.01:                                  # live configuration change
            cfg = rand_line_cfg(rnd)
            ln.cfg[:] = cfg
            ln.decode()
            dut.cfg.value = int.from_bytes(bytes(cfg), "little")
        sp, lv = lv, lv ^ sum(1 << k for k in range(13) if rnd.randrange(pins_p[k]) == 0)
        rs, fl = lv & ~sp, ~lv & sp & 0x1FFF
        ctl = rnd.randrange(8) if rnd.random() < 0.03 else None
        sym = (rnd.randrange(3), rnd.randrange(16)) if rnd.random() < 0.2 else None
        hw = None
        if rnd.random() < 0.03:
            hw = (rnd.choice(["PH0", "PH1", "CTL", "STAT"]), rnd.choice([rnd.randrange(256), 1, 3, 5, 7]))
        dut.lvl.value, dut.rise.value, dut.fall.value = lv, rs, fl
        dut.ctl_we.value, dut.ctl_d.value = int(ctl is not None), ctl or 0
        dut.sym_we.value = int(sym is not None)
        dut.sym_op.value, dut.sym_d.value = (sym or (0, 0))
        dut.h_ph_we.value = 1 if hw and hw[0] == "PH0" else 2 if hw and hw[0] == "PH1" else 0
        dut.h_ctl_we.value = int(bool(hw) and hw[0] == "CTL")
        dut.h_stat_we.value = int(bool(hw) and hw[0] == "STAT")
        dut.h_d.value = hw[1] if hw else 0
        # model: combinational, then compare the combinational outputs in this cycle
        ln.comb(lv, rs, fl)
        await ReadOnly()
        got = dict(beat=v(dut.beat), tap=v(dut.tap), in_sym=v(dut.in_sym), cap=v(dut.cap))
        exp = {k: line_state(ln)[k] for k in got}
        if got != exp:
            errors += 1
            dut._log.error(f"seed {seed} cycle {t} comb: rtl {got} model {exp}")
        effective_ctl = hw[1] if hw and hw[0] == "CTL" else ctl
        ln.commit(effective_ctl, ln.sym_value(["SYM", "DBIT", "XOR"][sym[0]], sym[1]) if sym else None)
        if hw:   # host write last (SPEC 9), as metronome2.regs.write_runtime
            name, d = hw
            if name in ("PH0", "PH1"):
                k = 0 if name == "PH0" else 1
                ln.PH = (ln.PH & ~(0xFF << 8 * k)) | (d << 8 * k)
                ln.fix_fired()
            elif name == "CTL":
                ln.RUN, ln.ARM, ln.REN = d & 1, (d >> 1) & 1, (d >> 2) & 1
                ln.fix_fired()
            elif d & 1 and not ln.tapmiss_ev:
                ln.TAPMISS = 0
        await RisingEdge(dut.clk)
        await ReadOnly()
        st = line_state(ln)
        got = {k: v(getattr(dut, k)) for k in ("ph", "run", "arm", "ren", "fired", "held", "staged", "committed",
                                                "tapmiss", "sp")}
        exp = {k: st[k] for k in got}
        if got != exp:
            errors += 1
            dut._log.error(f"seed {seed} cycle {t}: rtl {got} model {exp}")
        assert errors < 5, f"seed {seed}: md2_line differs from the model"
        await FallingEdge(dut.clk)
    assert errors == 0
    return cycles


@cocotb.test(skip=BLOCK != "md2_line")
async def line_lockstep(dut):
    await clock(dut)
    dut.rst_n.value = 0
    for sig in (dut.cfg, dut.lvl, dut.rise, dut.fall, dut.ctl_we, dut.ctl_d, dut.sym_we, dut.sym_op, dut.sym_d,
                dut.h_ph_we, dut.h_ctl_we, dut.h_stat_we, dut.h_d, dut.frz):   # frz: v3 freeze off
        sig.value = 0
    await RisingEdge(dut.clk)
    await FallingEdge(dut.clk)
    cfg = bytearray(32)
    for off, value in ((0, 1), (2, 8), (4, 0), (6, 2), (8, 6), (10, 3)):
        cfg[off:off + 2] = value.to_bytes(2, "little")
    cfg[0x10] = 0x10                             # edge on P0 rise
    dut.cfg.value = int.from_bytes(cfg, "little")
    dut.rst_n.value = 1
    dut.ctl_we.value, dut.ctl_d.value = 1, 2      # arm while stopped
    dut.sym_we.value, dut.sym_d.value = 1, 11
    await RisingEdge(dut.clk)
    await FallingEdge(dut.clk)
    dut.ctl_we.value = dut.sym_we.value = 0
    dut.h_ctl_we.value, dut.h_d.value = 1, 0     # host stop wins over simultaneous start edge
    dut.lvl.value, dut.rise.value = 1, 1
    await RisingEdge(dut.clk)
    await ReadOnly()
    assert (v(dut.run), v(dut.fired), v(dut.first), v(dut.committed)) == (0, 0, 0, 0)
    await FallingEdge(dut.clk)
    n = 0
    for seed in range(1, SEEDS + 1):
        dut.rst_n.value = 0
        await RisingEdge(dut.clk)
        await FallingEdge(dut.clk)
        dut.rst_n.value = 1
        n += await line_run(dut, seed)
    dut._log.info(f"md2_line: {SEEDS} seeds, {n} cycles identical to metronome2.line.Line")


# ================================================================================================== md2_stream
async def stream_run(dut, seed, cycles=3000):
    rnd = random.Random(seed)
    ram = bytearray(rnd.getrandbits(8) for _ in range(m.DATA_BYTES))
    s = Stream(0)
    mode, msb = rnd.randrange(2), rnd.randrange(2)
    s.cfg[0] = mode | msb << 1
    start, length, mark = rnd.randrange(2048), rnd.choice([0, 1, 5, 40, 300]), rnd.randrange(8)
    s.cfg[1:3] = start.to_bytes(2, "little")
    s.cfg[3:5] = length.to_bytes(2, "little")
    s.cfg[5:7] = mark.to_bytes(2, "little")
    s.decode()
    dut.cfg_mode.value, dut.cfg_msb.value = mode, msb
    dut.cfg_start.value, dut.cfg_len.value, dut.cfg_mark.value = start, length, mark
    # rewind both (as a host CTL write), then random traffic
    rate = rnd.choice([1, 2, 6, 9])
    busy = rnd.choice([0.0, 0.3, 0.6])                             # arbiter serves someone else
    errors = 0
    rd_out = 0
    for t in range(cycles):
        rew = t == 0 or rnd.random() < 0.003
        adv = mode == 0 and rnd.randrange(rate) == 0
        rx = rnd.randrange(2) if (mode == 1 and rnd.randrange(rate) == 0) else None
        flush = mode == 1 and rnd.random() < 0.01
        clr = rnd.random() < 0.01
        await ReadOnly()
        req, req_we, addr = v(dut.req), v(dut.req_we), v(dut.req_addr)
        gnt = int(req and rnd.random() >= busy)
        exp_req = s.request()
        got_req = (("W", addr, v(dut.req_wdata)) if req_we else ("R", addr)) if req else None
        exp_c = (s.BIT, s.BYTE, s.END, s.G_MARK, s.G_BYTE, exp_req)
        got_c = (v(dut.bit_out), v(dut.byte_out), v(dut.g_end), v(dut.g_mark), v(dut.g_byte), got_req)
        if exp_c != got_c:
            errors += 1
            dut._log.error(f"seed {seed} cycle {t} comb: rtl {got_c} model {exp_c}")
        await Timer(1, unit="ns")                                    # leave ReadOnly before driving
        dut.adv.value, dut.rx_we.value, dut.rx_bit.value = int(adv), int(rx is not None), rx or 0
        dut.rewind.value, dut.flush.value, dut.clr_starved.value = int(rew), int(flush), int(clr)
        dut.gnt.value = gnt
        dut.rdata.value = rd_out
        word = 0
        if gnt:
            a = exp_req[1]
            if exp_req[0] == "W":
                ram[a] = exp_req[2]
            else:
                word = int.from_bytes(ram[a & ~3:(a & ~3) + 4], "little")
        ctl = (1 if rew else 0) | (2 if flush else 0) | (0x80 if clr else 0)
        s.commit(bool(gnt), word, adv, rx, ctl or None)
        await RisingEdge(dut.clk)
        rd_out = word if gnt and exp_req[0] == "R" else rd_out   # RAM output holds until the next read
        await ReadOnly()
        got = (v(dut.pos), v(dut.bidx), v(dut.starved))
        exp = (s.POS, s.BIDX, s.STARVED)
        if got != exp:
            errors += 1
            dut._log.error(f"seed {seed} cycle {t}: rtl pos/bidx/starved {got} model {exp}")
        assert errors < 5, f"seed {seed}: md2_stream differs from the model"
        await FallingEdge(dut.clk)
    assert errors == 0
    return cycles


@cocotb.test(skip=BLOCK != "md2_stream")
async def stream_lockstep(dut):
    await clock(dut)
    for sig in (dut.adv, dut.rx_we, dut.rx_bit, dut.rewind, dut.flush, dut.clr_starved, dut.gnt, dut.rdata,
                dut.cfg_mode, dut.cfg_msb, dut.cfg_start, dut.cfg_len, dut.cfg_mark,
                dut.frz, dut.frzd, dut.cap_en, dut.cap_push, dut.cap_rec):     # v3 inputs off
        sig.value = 0
    n = 0
    for seed in range(1, 2 * SEEDS + 1):
        dut.rst_n.value = 0
        await RisingEdge(dut.clk)
        await FallingEdge(dut.clk)
        dut.rst_n.value = 1
        n += await stream_run(dut, seed)
    dut._log.info(f"md2_stream: {2 * SEEDS} seeds, {n} cycles identical to metronome2.memory.Stream")


# ================================================================================================== md2_cfg_bank
@cocotb.test(skip=BLOCK != "md2_cfg_bank")
async def cfg_bank(dut):
    """BYTES 4, MASK 0x00_0F_00_FF: byte 0 all bits, byte 1 none, byte 2 low nibble, byte 3 none."""
    await clock(dut)
    dut.we.value, dut.waddr.value, dut.wdata.value = 0, 0, 0
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    await FallingEdge(dut.clk)
    dut.rst_n.value = 1
    for _ in range(3):
        await FallingEdge(dut.clk)
    assert v(dut.q) == 0
    seen = []
    for addr, data in ((0, 0xA5), (1, 0xFF), (2, 0xFF), (3, 0x77), (0, 0x3C)):
        dut.we.value, dut.waddr.value, dut.wdata.value = 1, addr, data      # write cycle W
        await FallingEdge(dut.clk)
        dut.we.value = 0
        w1 = v(dut.q)                                                       # W+1: old value
        await FallingEdge(dut.clk)
        w2 = v(dut.q)                                                       # W+2: new value
        seen.append((w1, w2))
        await FallingEdge(dut.clk)
    assert seen == [(0, 0xA5), (0xA5, 0xA5), (0xA5, 0x0F00A5), (0x0F00A5, 0x0F00A5), (0x0F00A5, 0x0F003C)], seen
    dut.rst_n.value = 0                                                     # async clear
    await FallingEdge(dut.clk)
    assert v(dut.q) == 0
    dut.rst_n.value = 1
    for _ in range(3):
        await FallingEdge(dut.clk)
    dut.we.value, dut.waddr.value, dut.wdata.value = 1, 0, 1                # two consecutive writes: flagged
    await FallingEdge(dut.clk)
    await FallingEdge(dut.clk)
    dut.we.value = 0
    await FallingEdge(dut.clk)
    assert v(dut.wr_spacing_err) == 1


# ================================================================================================== md2_mem
@cocotb.test(skip=BLOCK != "md2_mem")
async def mem_arbiter(dut):
    """Priority S0, S1, P0, host; pointer fetch RDY timing (served s, RDY from s+2), stale landing, MEMHAZ on an
    overwritten unserved request, host read landing."""
    await clock(dut)
    for sig in (dut.s_req, dut.s_we, dut.s_addr, dut.s_wd, dut.p_we, dut.p_sel, dut.p_d, dut.h_set, dut.h_wr,
                dut.h_addr, dut.h_d, dut.m_rd, dut.frz, dut.frzd, dut.s0_word, dut.s0_wword):   # v3 inputs off
        sig.value = 0
    dut.rst_n.value = 0
    await FallingEdge(dut.clk)
    dut.rst_n.value = 1

    async def cyc(**kw):
        for k, x in kw.items():
            getattr(dut, k).value = x
        await ReadOnly()
        st = dict(gnt=v(dut.s_gnt), ren=v(dut.m_ren), we=v(dut.m_we), addr=v(dut.m_addr), be=v(dut.m_be),
                  haz=v(dut.p_haz), rdy=v(dut.p_rdy), pd=v(dut.p_dat), hl=v(dut.h_land), hd=v(dut.h_land_d))
        await FallingEdge(dut.clk)
        for k in kw:
            getattr(dut, k).value = 0
        return st

    # pointer AL = 0x45 (request), served next cycle: word 0x11 lane 1
    dut.m_rd.value = 0x44332211
    a = await cyc(p_we=1, p_sel=0, p_d=0x45)
    assert a["ren"] == 0 and a["rdy"] == 0
    b = await cyc()
    assert (b["ren"], b["addr"]) == (1, 0x45 >> 2)
    c = await cyc()                     # landing cycle: RAM output word, byte lane 1
    assert c["rdy"] == 0
    d = await cyc()
    assert (d["rdy"], d["pd"]) == (1, 0x22)            # byte 0x45: lane 1
    # stream 1 and pointer and host requests together: S1 first, then P0, then host
    e = await cyc(s_req=0b10, s_addr=(0x123 << 11), p_we=1, p_sel=3, h_set=1, h_addr=0x7FF)
    assert e["gnt"] == 0b10 and e["haz"] == 0
    f = await cyc(s_req=0b11, s_addr=(0x123 << 11) | 0x10, s_we=0b01, s_wd=0xAB)
    assert f["gnt"] == 0b01 and (f["we"], f["addr"], f["be"]) == (1, 0x10 >> 2, 1)
    g = await cyc(p_we=1, p_sel=0, p_d=0x00)          # pointer request still pending: replaced, MEMHAZ
    assert g["haz"] == 0, "served this cycle is not pending"
    h = await cyc(s_req=0b01, p_we=1, p_sel=0, p_d=0x04)
    assert h["haz"] == 1 and h["gnt"] == 0b01
    i = await cyc()
    assert i["ren"] == 1 and i["addr"] == 1           # pointer fetch of byte 4
    j = await cyc()                                   # host read of 0x7FF (queued since e) served now
    assert (j["ren"], j["addr"]) == (1, 0x7FF >> 2)
    dut.m_rd.value = 0xDD000000
    k_ = await cyc()
    assert (k_["hl"], k_["hd"]) == (1, 0xDD)


# ================================================================================================== md2_host
@cocotb.test(skip=BLOCK != "md2_host")
async def host_link(dut):
    """SPI mode 0 framing on synchronised inputs: write strobes at c+1 with auto-increment, a register read
    answered on MISO, a data RAM read answered by hland, and an unknown command ignored."""
    await clock(dut)
    dut.rst_n.value = 0
    dut.sck.value, dut.sck_p.value, dut.cs_n.value, dut.mosi.value = 0, 0, 1, 0
    dut.rd_data.value, dut.rd_val.value, dut.hland.value, dut.hland_d.value = 0, 0, 0, 0
    await FallingEdge(dut.clk)
    dut.rst_n.value = 1
    events = []
    miso_bits = []
    sck_prev = 0

    async def tick(sck, cs_n, mosi):
        nonlocal sck_prev
        dut.sck.value, dut.sck_p.value, dut.cs_n.value, dut.mosi.value = sck, sck_prev, cs_n, mosi
        sck_prev = sck
        dut.rd_val.value = (v(dut.addr) * 7) & 0xFF          # register value at addr in this cycle
        await ReadOnly()
        if v(dut.wr):
            events.append(("wr", v(dut.addr), v(dut.wdata)))
        if v(dut.rd):
            events.append(("rd", v(dut.addr)))
        await FallingEdge(dut.clk)

    async def frame(bs):
        await tick(0, 0, 0)
        for b in bs:
            for i in range(7, -1, -1):
                bit = (b >> i) & 1
                for _ in range(4):
                    await tick(0, 0, bit)
                miso_bits.append(v(dut.miso))
                for _ in range(4):
                    await tick(1, 0, bit)
        for _ in range(4):
            await tick(0, 0, 0)
        for _ in range(4):
            await tick(0, 1, 0)

    await frame([0x02, 0x24, 0x10, 0x11, 0x22, 0x33])
    assert events == [("wr", 0x2410, 0x11), ("wr", 0x2411, 0x22), ("wr", 0x2412, 0x33)], events
    events.clear()
    miso_bits.clear()
    await frame([0x03, 0x12, 0x34, 0, 0])
    assert events == [("rd", 0x1234), ("rd", 0x1235), ("rd", 0x1236)], events   # prefetch one past (SPEC 9)
    data = [int("".join(map(str, miso_bits[24 + 8 * j:32 + 8 * j])), 2) for j in range(2)]
    assert data == [(0x1234 * 7) & 0xFF, (0x1235 * 7) & 0xFF], data
    events.clear()
    await frame([0x55, 0x00, 0x00, 0x99])
    assert events == []
