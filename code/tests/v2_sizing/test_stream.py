"""pytest entry for md2_stream: python -m pytest code/tests/v2_sizing/test_stream.py -q"""
from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest
from cocotb_tools.runner import get_results, get_runner

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SRC = ROOT / "sim" / "numerics" / "v2_sizing" / "rtl" / "md2_stream.v"
OSS = Path(os.environ.get("OSS_CAD_SUITE", r"C:\Users\b_yee23\tools\oss-cad-suite"))
BUILD = HERE / "sim_build_stream"

TESTS = ["test_tx_unaligned", "test_tx_longer_all_alignments", "test_rx_flush", "test_rx_stops_at_end_and_flush_empty",
         "test_rx_overflow_starved", "test_tx_starved_when_grants_withheld", "test_tx_rewind_mid_frame"]

if shutil.which("iverilog") is None and (OSS / "bin").exists():
    os.environ["PATH"] = f"{OSS / 'bin'}{os.pathsep}{OSS / 'lib'}{os.pathsep}{os.environ['PATH']}"
if "VERILATOR_ROOT" not in os.environ and (OSS / "share" / "verilator").exists():
    os.environ["VERILATOR_ROOT"] = str(OSS / "share" / "verilator")


@pytest.fixture(scope="module")
def runner():
    r = get_runner("icarus")
    r.build(sources=[SRC], hdl_toplevel="md2_stream", build_dir=BUILD, build_args=["-g2005"], timescale=("1ns", "1ps"), always=True)
    return r


@pytest.mark.parametrize("name", TESTS)
def test_cocotb(runner, name):
    xml = runner.test(test_module="tb_stream", hdl_toplevel="md2_stream", build_dir=BUILD, test_dir=HERE,
                      testcase=name, results_xml=str(BUILD / f"results_{name}.xml"),
                      extra_env={"PYTHONPATH": str(HERE)})
    n, failed = get_results(xml)
    assert n == 1 and failed == 0, f"{name}: {failed} of {n} failed"


def test_verilator_lint():
    exe = shutil.which("verilator_bin") or shutil.which("verilator")
    if exe is None:
        pytest.skip("verilator not available")
    p = subprocess.run([exe, "--lint-only", "-Wall", "--top-module", "md2_stream", str(SRC)],
                       capture_output=True, text=True)
    assert p.returncode == 0, p.stdout + p.stderr
