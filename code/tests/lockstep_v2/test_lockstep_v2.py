"""pytest entry: build the v2 RTL with Icarus and run each lockstep scenario against the metronome2 model.

    source code/tools/env.sh
    python -m pytest code/tests/lockstep_v2 -q                     # directed scenarios + LOCKSTEP_SEEDS random seeds
    LOCKSTEP_SEEDS=20 python -m pytest code/tests/lockstep_v2 -q
    LOCKSTEP_BEHAV_SRAM=1 ...                                      # md2_pmem/md2_dmem arrays instead of the IHP models
"""
from __future__ import annotations

import os
import shutil
import xml.etree.ElementTree as ET
from pathlib import Path

import pytest

from rtl_sources import SRC, rtl_files

HERE = Path(__file__).resolve().parent
SEEDS = int(os.environ.get("LOCKSTEP_SEEDS", "4"))
DIRECTED = ["smoke", "eth_loopback", "follower", "hold", "taps", "units", "reset_mid", "spi_target", "shifter_parallel"]

pytestmark = pytest.mark.skipif(shutil.which("iverilog") is None, reason="needs iverilog (source code/tools/env.sh)")


def _run(scenario: str):
    from cocotb_tools.runner import get_runner
    ihp = os.environ.get("LOCKSTEP_BEHAV_SRAM") != "1"
    files, defines = rtl_files(ihp_sram=ihp)
    build = HERE / ("sim_build" + ("" if ihp else "_behav") + os.environ.get("LOCKSTEP_TAG", ""))
    r = get_runner("icarus")
    r.build(sources=files, hdl_toplevel="tt_um_brentius_metronome", build_dir=build, includes=[SRC],
            defines=defines, timescale=("1ns", "1ps"), always=True)
    xml = build / f"results_{scenario}.xml"
    r.test(hdl_toplevel="tt_um_brentius_metronome", test_module="lockstep_tb", build_dir=build, test_dir=HERE,
           extra_env={"LOCKSTEP_SCENARIO": scenario}, results_xml=str(xml))
    root = ET.parse(xml).getroot()
    fails = root.findall(".//failure") + root.findall(".//error")
    assert not fails, f"{scenario}: {[f.get('message') for f in fails]}"


@pytest.mark.parametrize("scenario", DIRECTED + [f"random_{s}" for s in range(1, SEEDS + 1)])
def test_lockstep(scenario):
    _run(scenario)
