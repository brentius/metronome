"""pytest entry: builds tt_um_metronome (behavioural memories) with Icarus and runs each cocotb test in
tb_metronome.py. Usage: python -m pytest code/tests/rtl -q"""
from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest
from cocotb_tools.runner import get_results, get_runner

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
RTL = ROOT / "code" / "rtl"
GEN = RTL / "gen"
OSS = Path(os.environ.get("OSS_CAD_SUITE", r"C:\Users\b_yee23\tools\oss-cad-suite"))
BUILD = HERE / "sim_build"

TESTS = ["test_host_registers", "test_program_load", "test_toggle_every_beat", "test_beatgen_rate_and_taps",
         "test_crc32_lfsr", "test_sticky_flags", "test_data_ram_pointers"]


def _tool_env():
    if shutil.which("iverilog") is None and (OSS / "bin").exists():
        os.environ["PATH"] = f"{OSS / 'bin'}{os.pathsep}{OSS / 'lib'}{os.pathsep}{os.environ['PATH']}"
    if "VERILATOR_ROOT" not in os.environ and (OSS / "share" / "verilator").exists():
        os.environ["VERILATOR_ROOT"] = str(OSS / "share" / "verilator")


_tool_env()


@pytest.fixture(scope="module")
def runner():
    r = get_runner("icarus")
    r.build(sources=sorted(RTL.glob("*.v")), includes=[GEN], hdl_toplevel="tt_um_metronome", build_dir=BUILD,
            build_args=["-g2005"], always=True)
    return r


@pytest.mark.parametrize("name", TESTS)
def test_cocotb(runner, name):
    xml = runner.test(test_module="tb_metronome", hdl_toplevel="tt_um_metronome", build_dir=BUILD,
                      test_dir=HERE, testcase=name, results_xml=str(BUILD / f"results_{name}.xml"),
                      extra_env={"PYTHONPATH": str(HERE)})
    n, failed = get_results(xml)
    assert n == 1 and failed == 0, f"{name}: {failed} of {n} failed"


def test_verilator_lint():
    exe = shutil.which("verilator_bin") or shutil.which("verilator")
    if exe is None:
        pytest.skip("verilator not available")
    p = subprocess.run([exe, "--lint-only", "-Wall", f"-I{GEN}", f"-I{RTL}", "--top-module", "tt_um_metronome",
                        *map(str, sorted(RTL.glob("*.v")))], capture_output=True, text=True)
    assert p.returncode == 0, p.stdout + p.stderr
