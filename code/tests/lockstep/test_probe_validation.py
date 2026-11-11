"""A reported internal discrepancy must become a failing cocotb result, not a passing log."""
from pathlib import Path
import shutil
import xml.etree.ElementTree as ET

import pytest
from cocotb_tools.runner import get_results, get_runner

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


@pytest.fixture(scope="module")
def probe_runner():
    if shutil.which("iverilog") is None:
        pytest.skip("needs iverilog on PATH")
    build = HERE / "sim_build_probe_validation"
    runner = get_runner("icarus")
    runner.build(sources=sorted((ROOT / "code/rtl").glob("*.v")),
                 includes=[ROOT / "code/rtl/gen"], hdl_toplevel="tt_um_metronome",
                 build_dir=build, timescale=("1ns", "1ps"), always=True)
    return runner, build


@pytest.mark.parametrize("fault", ["mismatch", "unavailable", "missing_handle", "unresolved_value"])
def test_internal_probe_fault_fails(probe_runner, fault):
    runner, build = probe_runner
    xml = build / f"results_{fault}.xml"
    with pytest.raises(SystemExit) as failure:
        runner.test(hdl_toplevel="tt_um_metronome", test_module="probe_fault_tb", build_dir=build,
                    test_dir=HERE, results_xml=str(xml), extra_env={"LOCKSTEP_PROBE": "1",
                    "LOCKSTEP_SCENARIO": "smoke", "PROBE_FAULT": fault})
    assert failure.value.code == 1
    count, failed = get_results(xml)
    assert count == 1 and failed == 1, f"{fault}: internal probe fault silently passed"
    message = ET.parse(xml).find(".//failure").get("message", "")
    if fault in ("mismatch", "unavailable"):
        assert "internal state differs or unavailable" in message and "acc.A" in message, message
    else:
        diagnostic = "unavailable" if fault == "missing_handle" else "unresolved"
        assert f"internal probe {diagnostic}: u_acc.a" in message, message
