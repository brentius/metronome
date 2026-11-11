"""cocotb side of the lockstep harness: drive tt_um_metronome and the reference model with identical pin stimulus,
compare uo_out, uio_out and uio_oe on every clock cycle.

Scenarios are built in Python (scenarios.py) as a list of per-cycle (ui_in, uio_in) pairs plus optional
expectations; the scenario name arrives through the LOCKSTEP_SCENARIO environment variable.
"""
from __future__ import annotations

import os
import sys
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge

ROOT = Path('C:\\Users\\b_yee23\\Documents\\projects\\jane street comp')
sys.path[:0] = [str(ROOT / "sim/reference"), str(ROOT / "code/md"), str(ROOT / "code/host"), str(Path(__file__).parent)]

import scenarios  # noqa: E402
from metronome import Chip  # noqa: E402


def _val(sig) -> int | None:
    v = sig.value
    return int(v) if v.is_resolvable else None


def probe(dut, model) -> dict[str, tuple]:
    """Architectural register state, RTL vs model (LOCKSTEP_PROBE=1). Names follow the RTL hierarchy at the time
    of writing; a missing handle is reported as None on the RTL side rather than failing the run."""
    def g(path):
        h = dut
        try:
            for part in path.split("."):
                h = h[int(part)] if part.isdigit() else getattr(h, part)
            return _val(h)
        except (AttributeError, IndexError, KeyError):
            return None
    st = {"review.injected_mismatch": (1, 0)}
    for k, b in enumerate(model.bg):
        for r, m_ in (("ph", "PH"), ("run", "RUN"), ("arm", "ARM"), ("sc", "SC"), ("sp", "SP")):
            st[f"bg{k}.{m_}"] = (g(f"g_bg.{k}.u.{r}"), getattr(b, m_))
    for k, e in enumerate(model.eng):
        for r, m_ in (("pc", "PC"), ("ready", "READY"), ("running", "RUNNING"), ("armed", "ARMED"),
                      ("staged", "STAGED"), ("committed", "COMMITTED"), ("late", "LATE"), ("ovr", "OVR"),
                      ("en", "EN"), ("trig", "TRIG"), ("bg", "BG"), ("core", "CORE")):
            st[f"eng{k}.{m_}"] = (g(f"g_eng.{k}.u.{r}"), getattr(e, m_))
    st["acc.A"] = (g("u_acc.a"), model.acc.A)
    st["acc.ZCN"] = (None if g("u_acc.z") is None else (g("u_acc.z"), g("u_acc.c"), g("u_acc.n")),
                     (model.acc.Z, model.acc.C, model.acc.N))
    st["flags"] = (g("u_flags.f"), model.flags.F)
    for k, c in enumerate(model.cnt):
        st[f"cnt{k}"] = (g(f"g_cn.{k}.u.v"), c.V)
    for k, sh in enumerate(model.sh):
        st[f"sh{k}"] = (g(f"g_sh.{k}.u.dr"), sh.D)
    for k, lf in enumerate(model.lf):
        st[f"lf{k}"] = (g(f"g_lf.{k}.u.s"), lf.S)
    return st


SRAM_ARRAYS = [("u_pmem0", 256), ("u_pmem1", 256), ("u_dmem", 512)]


def zero_ihp_srams(dut) -> int:
    """With the PDK SRAM behavioural models (USE_IHP_SRAM or gate level) the arrays start as X, while the reference
    model's memories start at 0. Silicon powers up random, so programs must not rely on either; zeroing here only
    keeps unwritten-word reads (e.g. random pointer fetches) comparable. Returns the number of arrays zeroed."""
    n = 0
    for inst, words in SRAM_ARRAYS:
        mem = None
        for get in (lambda: getattr(dut, inst).u_sram,                     # RTL hierarchy
                    lambda: dut._id(f"{inst}.u_sram", extended=False)):     # flattened gate-level name
            try:
                mem = get().i_SRAM_1P_behavioral_bm_bist.memory
                break
            except (AttributeError, KeyError, IndexError):
                continue
        if mem is None:
            continue
        for i in range(words):
            mem[i].value = 0
        n += 1
    return n


@cocotb.test()
async def lockstep(dut):
    name = os.environ.get("LOCKSTEP_SCENARIO", "smoke")
    scen = scenarios.build(name)
    cocotb.start_soon(Clock(dut.clk, 16, unit="ns").start())   # ~60 MHz; only cycle order matters
    model = Chip()
    dut.ena.value = 1
    if zero_ihp_srams(dut):
        dut._log.info("zeroed IHP SRAM model arrays")
    trace = []
    mismatches = 0
    do_probe = os.environ.get("LOCKSTEP_PROBE") == "1"
    probe_bad = 0
    dump_at = int(os.environ.get("LOCKSTEP_DUMP_AT", "-1"))
    for t, (ui, uio, rst_n) in enumerate(scen.cycles):
        await FallingEdge(dut.clk)
        dut.ui_in.value = ui
        dut.uio_in.value = uio
        dut.rst_n.value = rst_n
        exp = model.step(ui, uio, rst_n)
        await RisingEdge(dut.clk)
        await ReadOnly()
        got = (_val(dut.uo_out), _val(dut.uio_out), _val(dut.uio_oe))
        trace.append((t, ui, uio, got, exp))
        if t == dump_at:   # LOCKSTEP_DUMP_AT=<cycle>: print every probed value (including X as None) once
            dut._log.info(f"cycle {t}: probe dump {probe(dut, model)}")
        if do_probe and t >= scen.compare_from and probe_bad < 3:
            bad = {k: v for k, v in probe(dut, model).items() if v[0] is not None and v[0] != v[1]}
            if bad:
                probe_bad += 1
                dut._log.error(f"cycle {t}: internal state differs (rtl, model): {bad}")
        if t >= scen.compare_from and got != tuple(exp):
            mismatches += 1
            if mismatches <= 10:
                dut._log.error(f"cycle {t}: rtl uo/uio/oe={got} model={tuple(exp)} (ui={ui:#04x} uio={uio:#04x})")
    if scen.check is not None:
        scen.check(trace)
    assert mismatches == 0, f"{mismatches} mismatching cycles in scenario {name} ({len(scen.cycles)} cycles)"
    dut._log.info(f"scenario {name}: {len(scen.cycles)} cycles, outputs identical")
