"""pytest entry for the v2 block unit tests (blocks_tb.py) and the Verilator lint of the whole v2 RTL.

    source code/tools/env.sh && python -m pytest code/tests/rtl_v2 -q
    BLOCK_SEEDS=20 python -m pytest code/tests/rtl_v2 -q        # more random seeds for md2_line / md2_stream
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE.parent / "lockstep_v2"))
from rtl_sources import SOURCES  # noqa: E402

SRC = Path(os.environ.get("RTL_V2_SRC", ROOT / "src"))   # override: mutation checks on a copy
BLOCKS = {
    "md2_line": (["md2_line.v"], {}),
    "md2_stream": (["md2_stream.v"], {}),
    "md2_cfg_bank": (["md2_cfg_bank.v", "cells_behav.v"], {"BYTES": 4, "MASK": 0x000F00FF, "AW": 2}),
    "md2_mem": (["md2_mem.v"], {}),
    "md2_host": (["md2_host.v"], {}),
}


@pytest.mark.skipif(shutil.which("iverilog") is None, reason="needs iverilog (source code/tools/env.sh)")
@pytest.mark.parametrize("block", list(BLOCKS))
def test_block(block):
    from cocotb_tools.runner import get_runner
    files, params = BLOCKS[block]
    build = HERE / "sim_build" / block
    r = get_runner("icarus")
    r.build(sources=[SRC / f for f in files], hdl_toplevel=block, build_dir=build, includes=[SRC],
            parameters=params, defines={"SIM": 1, "COCOTB_SIM": 1}, timescale=("1ns", "1ps"), always=True)
    xml = build / "results.xml"
    r.test(hdl_toplevel=block, test_module="blocks_tb", build_dir=build, test_dir=HERE, extra_env={"BLOCK": block},
           results_xml=str(xml))
    root = ET.parse(xml).getroot()
    fails = root.findall(".//failure") + root.findall(".//error")
    assert not fails, [f.get("message") for f in fails]
    ran = [tc for tc in root.iter("testcase") if tc.find("skipped") is None]
    assert len(ran) == 1, f"{block}: expected one test to run, ran {len(ran)}"


@pytest.mark.parametrize("defines", [["-DSIM"], [], ["-DSIM", "-DUSE_IHP_SRAM"]])
def test_verilator_lint(defines):
    exe = shutil.which("verilator_bin") or shutil.which("verilator")
    if exe is None:
        pytest.skip("verilator not available")
    if "-DUSE_IHP_SRAM" in defines:
        defines = ["-DUSE_IHP_SRAM"]          # black-box macros (md2_sram_bb.v), as synthesis sees them
    p = subprocess.run([exe, "--lint-only", "-Wall", f"-I{SRC}", *defines, "--top-module", "tt_um_brentius_metronome",
                        *[str(SRC / f) for f in SOURCES]], capture_output=True, text=True, cwd=ROOT)
    assert p.returncode == 0 and "%Warning" not in p.stderr, p.stderr[-3000:]


def test_generated_tables_current():
    p = subprocess.run([sys.executable, str(HERE / "gen_rtl_tables.py"), "--check"], capture_output=True, text=True)
    assert p.returncode == 0, p.stdout + p.stderr
