"""Smoke test of the latch-bank Tiny Tapeout top with behavioural cells.
    python -m pytest sim/numerics/v2_sizing/tt_latch_top/test_tt_latch_top.py -q
Build dir: code/tests/v2_sizing/sim_build_tt_latch_top (gitignored)."""
from __future__ import annotations

import os
import random
import shutil
from pathlib import Path

import cocotb
import pytest
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_tools.runner import get_results, get_runner

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
RTL = HERE.parent / "rtl"
BUILD = ROOT / "code" / "tests" / "v2_sizing" / "sim_build_tt_latch_top"
OSS = Path(os.environ.get("OSS_CAD_SUITE", r"C:\Users\b_yee23\tools\oss-cad-suite"))


async def cmd(dut, data, mode):
    dut.ui_in.value = data
    dut.uio_in.value = mode << 1
    await RisingEdge(dut.clk)
    dut.uio_in.value = (mode << 1) | 1
    for _ in range(4):
        await RisingEdge(dut.clk)
    dut.uio_in.value = mode << 1
    for _ in range(4):
        await RisingEdge(dut.clk)


def fold(vals):
    f = [0] * 6
    for k, v in enumerate(vals):
        for b in range(8):
            f[(8 * k + b) % 6] ^= (v >> b) & 1
    return sum(bit << j for j, bit in enumerate(f))


@cocotb.test()
async def test_smoke(dut):
    cocotb.start_soon(Clock(dut.clk, 16, unit="ns").start())
    dut.ena.value = 1
    dut.ui_in.value = 0
    dut.uio_in.value = 0
    dut.rst_n.value = 0
    for _ in range(4):
        await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    for _ in range(4):
        await RisingEdge(dut.clk)
    await Timer(1, unit="ns")
    assert int(dut.uo_out.value) == 0 and (int(dut.uio_out.value) >> 2) == 0 and int(dut.uio_oe.value) == 0xFC
    ref = [0] * 256
    await cmd(dut, 0, 0)                          # address 0
    rnd = random.Random(1)
    for k in range(256):                          # sequential auto-increment writes
        ref[k] = rnd.randrange(1, 256)
        await cmd(dut, ref[k], 1)
    await Timer(1, unit="ns")
    assert (int(dut.uio_out.value) >> 2) == fold(ref), "XOR fold mismatch"
    for a in (0, 1, 77, 255):                     # readback mux
        await cmd(dut, a, 0)
        await Timer(1, unit="ns")
        assert int(dut.uo_out.value) == ref[a], f"readback {a}"
    dut.rst_n.value = 0                           # reset clears the bank
    await Timer(1, unit="ns")
    assert int(dut.uo_out.value) == 0 and (int(dut.uio_out.value) >> 2) == 0


def test_cocotb():
    if shutil.which("iverilog") is None and (OSS / "bin").exists():
        os.environ["PATH"] = f"{OSS / 'bin'}{os.pathsep}{OSS / 'lib'}{os.pathsep}{os.environ['PATH']}"
    r = get_runner("icarus")
    r.build(sources=[RTL / "cells_behav.v", RTL / "cfg_latch_bank.v", HERE / "tt_um_brentius_metronome.v"],
            hdl_toplevel="tt_um_brentius_metronome", build_dir=BUILD, build_args=["-g2012"], always=True,
            timescale=("1ns", "1ps"))
    xml = r.test(test_module="test_tt_latch_top", hdl_toplevel="tt_um_brentius_metronome", build_dir=BUILD,
                 test_dir=HERE, results_xml=str(BUILD / "results.xml"), extra_env={"PYTHONPATH": str(HERE)})
    n, failed = get_results(xml)
    assert n == 1 and failed == 0
