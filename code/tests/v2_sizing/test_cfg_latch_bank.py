"""pytest entry: builds cfg_latch_bank (behavioural cells) and cfg_flop_bank with Icarus and runs tb_cfg_bank.py on each,
then lints the latch wrapper with Verilator -Wall.   python -m pytest code/tests/v2_sizing -q"""
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
OSS = Path(os.environ.get("OSS_CAD_SUITE", r"C:\Users\b_yee23\tools\oss-cad-suite"))
TESTS = ["test_reset_clears", "test_single_write_only_its_byte", "test_spaced_writes", "test_consecutive_write_flagged",
         "test_write_in_reset_release_cycle_ignored", "test_out_of_range_ignored", "test_latency"]
DUTS = {"cfg_latch_bank": ["cells_behav.v", "cfg_latch_bank.v"], "cfg_flop_bank": ["cfg_flop_bank.v"]}


def _tool_env():
    if shutil.which("iverilog") is None and (OSS / "bin").exists():
        os.environ["PATH"] = f"{OSS / 'bin'}{os.pathsep}{OSS / 'lib'}{os.pathsep}{os.environ['PATH']}"
    if "VERILATOR_ROOT" not in os.environ and (OSS / "share" / "verilator").exists():
        os.environ["VERILATOR_ROOT"] = str(OSS / "share" / "verilator")


_tool_env()


@pytest.fixture(scope="module", params=list(DUTS))
def built(request):
    top = request.param
    build = HERE / f"sim_build_{top}"
    r = get_runner("icarus")
    r.build(sources=[RTL / f for f in DUTS[top]], hdl_toplevel=top, build_dir=build, build_args=["-g2012"],
            parameters={"BYTES": 8}, defines={"COCOTB_SIM": 1}, always=True, timescale=("1ns", "1ps"))
    return r, top, build


@pytest.mark.parametrize("name", TESTS)
def test_cocotb(built, name):
    r, top, build = built
    xml = r.test(test_module="tb_cfg_bank", hdl_toplevel=top, build_dir=build, test_dir=HERE, testcase=name,
                 results_xml=str(build / f"results_{name}.xml"), extra_env={"PYTHONPATH": str(HERE)})
    n, failed = get_results(xml)
    assert n == 1 and failed == 0, f"{top}/{name}: {failed} of {n} failed"


@pytest.mark.parametrize("files", [["cells_behav.v", "cfg_latch_bank.v"], ["cfg_flop_bank.v"]])
def test_verilator_lint(files):
    exe = shutil.which("verilator_bin") or shutil.which("verilator")
    if exe is None:
        pytest.skip("verilator not available")
    top = "cfg_latch_bank" if "cfg_latch_bank.v" in files else "cfg_flop_bank"
    p = subprocess.run([exe, "--lint-only", "-Wall", "--top-module", top, *[str(RTL / f) for f in files]],
                       capture_output=True, text=True)
    assert p.returncode == 0 and "%Warning" not in p.stderr, p.stdout + p.stderr
