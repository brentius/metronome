"""cocotb side of the v2 lockstep harness: drive tt_um_brentius_metronome and the metronome2 model with identical
pin stimulus and compare uo_out, uio_out and uio_oe on every clock cycle (scenario from LOCKSTEP_SCENARIO)."""
from __future__ import annotations

import os
import sys
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE.parents[2] / "sim/reference"), str(HERE)]

import scenarios  # noqa: E402
from metronome2.chip import Chip  # noqa: E402


def _val(sig):
    v = sig.value
    return int(v) if v.is_resolvable else None


def zero_srams(dut) -> int:
    """The IHP SRAM models start as X; the model's memories start at 0. Silicon powers up random, so programs must
    not rely on either; zeroing keeps reads of unwritten words comparable."""
    n = 0
    for inst, words in (("u_pmem0", 256), ("u_pmem1", 256), ("u_dmem", 512)):
        h = getattr(dut, inst)
        try:
            mem = h.u_sram.i_SRAM_1P_behavioral_bm_bist.memory
        except AttributeError:
            mem = h.mem
        for i in range(words):
            mem[i].value = 0
        n += 1
    return n


def model_state(model):
    ln = [(l.PH, l.RUN, l.FIRED, l.HELD, l.STAGED, l.COMMITTED, l.TAPMISS) for l in model.lines]
    th = [(t.PC, t.EN, t.READY, t.RUNNING, t.ARMED, t.LATE, t.OVR) for t in model.threads]
    co = [(c.XV, c.RV, c.FPC, c.XT, c.RR) for c in model.cores]
    return f"lines {ln} threads {th} cores {co} acc {model.acc.A} flags {model.flags.F:#x}"


def rtl_state(dut):
    def g(h, n):
        try:
            return _val(getattr(h, n))
        except AttributeError:
            return "?"
    ln = [tuple(g(dut.g_ln[k].u, n) for n in ("ph", "run", "fired", "held", "staged", "committed", "tapmiss"))
          for k in range(4)]
    th = [tuple(g(dut.g_thr[k].u, n) for n in ("pc", "en", "ready", "running", "armed", "late", "ovr"))
          for k in range(6)]
    co = [tuple(g(dut.g_core[k].u_core, n) for n in ("xv", "rv", "fpc", "xt", "rr")) for k in range(2)]
    return f"lines {ln} threads {th} cores {co} acc {g(dut.u_acc, 'a')} flags {g(dut, 'fl')}"


@cocotb.test()
async def lockstep(dut):
    name = os.environ.get("LOCKSTEP_SCENARIO", "smoke")
    scen = scenarios.build(name)
    cocotb.start_soon(Clock(dut.clk, 16, unit="ns").start())
    model = Chip()
    dut.ena.value = 1
    dut.ui_in.value = scenarios.IDLE
    dut.uio_in.value = 0
    dut.rst_n.value = 1
    zero_srams(dut)
    outs = (0, 0, 0)
    mismatches = 0
    first = None
    for t, (ui, hi, uio, rst_n) in enumerate(scen.steps):
        await FallingEdge(dut.clk)
        uio = uio(t, outs) if callable(uio) else uio
        hi = hi(t, outs) if callable(hi) else hi
        ui = (ui & 0x07) | (hi & 0xF8)
        dut.ui_in.value = ui
        dut.uio_in.value = uio & 0xFF
        dut.rst_n.value = rst_n
        exp = tuple(model.step(ui, uio & 0xFF, rst_n))
        await RisingEdge(dut.clk)
        await ReadOnly()
        got = (_val(dut.uo_out), _val(dut.uio_out), _val(dut.uio_oe))
        outs = exp
        if t >= scen.compare_from and got != exp:
            mismatches += 1
            if first is None:
                first = t
                dut._log.error(f"model: {model_state(model)}")
                dut._log.error(f"rtl  : {rtl_state(dut)}")
            if mismatches <= 10:
                dut._log.error(f"cycle {t}: rtl uo/uio/oe={got} model={exp} (ui={ui:#04x} uio={uio & 0xFF:#04x})")
    assert mismatches == 0, f"{mismatches} mismatching cycles in {name} ({len(scen.steps)} cycles), first {first}"
    dut._log.info(f"scenario {name}: {len(scen.steps)} cycles, outputs identical")
