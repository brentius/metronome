"""pytest entry for v3_top_tb.py (DC saturation on the v3 top level, behavioural SRAM arrays)."""
import shutil
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "lockstep_v2"))
from rtl_sources import SRC, rtl_files  # noqa: E402


@pytest.mark.skipif(shutil.which("iverilog") is None, reason="needs iverilog")
def test_v3_top():
    from cocotb_tools.runner import get_runner
    files, defines = rtl_files(ihp_sram=False)
    build = HERE / "sim_build" / "v3_top"
    r = get_runner("icarus")
    r.build(sources=files, hdl_toplevel="tt_um_brentius_metronome", build_dir=build, includes=[SRC],
            defines=defines, timescale=("1ns", "1ps"), always=True)
    xml = build / "results.xml"
    r.test(hdl_toplevel="tt_um_brentius_metronome", test_module="v3_top_tb", build_dir=build, test_dir=HERE,
           results_xml=str(xml))
    root = ET.parse(xml).getroot()
    assert not (root.findall(".//failure") + root.findall(".//error"))
    assert len([tc for tc in root.iter("testcase") if tc.find("skipped") is None]) == 1
