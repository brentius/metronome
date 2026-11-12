"""pytest entry for the Metronome v2 pipelined-core sizing block: builds md2_core_top (behavioural program memories)
with Icarus and runs each cocotb test in tb_core.py, then lints with Verilator -Wall.

    source code/tools/env.sh && python -m pytest code/tests/v2_sizing/test_core.py -q
"""
from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest
from cocotb_tools.runner import get_results, get_runner

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
RTL = ROOT / "sim" / "numerics" / "v2_sizing" / "rtl"
INC = ROOT / "code" / "md2"
OSS = Path(os.environ.get("OSS_CAD_SUITE", r"C:\Users\b_yee23\tools\oss-cad-suite"))
BUILD = HERE / "sim_build_core"
TOP = "md2_core_top"
SOURCES = [RTL / f for f in ("md2_core.v", "md2_core_thread.v", "md2_core_pmem.v", "md2_core_top.v")]

TESTS = ["test_first_insn_t3", "test_sequential_one_per_cycle", "test_taken_jump_one_idle_wrong_path_silent",
         "test_jump_on_line_relative_guard", "test_pause_writes_pc_and_resumes", "test_dispatch_after_pause_one_idle",
         "test_round_robin_three_threads", "test_watcher_redirects_dispatch", "test_response_bound_two_threads",
         "test_core1_threads_ignored_by_core0"]


def _tool_env():
    if shutil.which("iverilog") is None and (OSS / "bin").exists():
        os.environ["PATH"] = f"{OSS / 'bin'}{os.pathsep}{OSS / 'lib'}{os.pathsep}{os.environ['PATH']}"
    if "VERILATOR_ROOT" not in os.environ and (OSS / "share" / "verilator").exists():
        os.environ["VERILATOR_ROOT"] = str(OSS / "share" / "verilator")


_tool_env()


@pytest.fixture(scope="module")
def runner():
    r = get_runner("icarus")
    r.build(sources=SOURCES, includes=[INC], hdl_toplevel=TOP, build_dir=BUILD, build_args=["-g2005"], always=True)
    return r


@pytest.mark.parametrize("name", TESTS)
def test_cocotb(runner, name):
    xml = runner.test(test_module="tb_core", hdl_toplevel=TOP, build_dir=BUILD, test_dir=HERE, testcase=name,
                      results_xml=str(BUILD / f"results_{name}.xml"), extra_env={"PYTHONPATH": str(HERE)})
    n, failed = get_results(xml)
    assert n == 1 and failed == 0, f"{name}: {failed} of {n} failed"


def test_verilator_lint():
    exe = shutil.which("verilator_bin") or shutil.which("verilator")
    if exe is None:
        pytest.skip("verilator not available")
    p = subprocess.run([exe, "--lint-only", "-Wall", f"-I{INC}", "--top-module", TOP, *map(str, SOURCES)],
                       capture_output=True, text=True)
    assert p.returncode == 0, p.stdout + p.stderr
