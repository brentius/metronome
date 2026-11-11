"""pytest entry: build tt_um_brentius_metronome with Icarus and run each lockstep scenario against the reference model.

    python -m pytest code/tests/lockstep -q                    # directed scenarios + a few random seeds
    LOCKSTEP_SEEDS=50 python -m pytest code/tests/lockstep -q  # more random seeds
"""
from __future__ import annotations

import os
import shutil
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
RTL = sorted(p for p in (ROOT / "src").glob("*.v"))
SEEDS = int(os.environ.get("LOCKSTEP_SEEDS", "3"))

pytestmark = pytest.mark.skipif(not RTL or shutil.which("iverilog") is None,
                                reason="needs src/*.v and iverilog on PATH (source code/tools/env.sh)")


def _paths(var: str) -> list[Path]:
    return [Path(p) for p in os.environ.get(var, "").split(os.pathsep) if p]


def _run(scenario: str):
    """Environment knobs (used on the pod, where the PDK lives):
    LOCKSTEP_NETLIST  gate-level netlist to simulate instead of src (e.g. final/nl/tt_um_brentius_metronome.nl.v)
    LOCKSTEP_EXTRA    extra sources, os.pathsep-separated (cell models, IHP SRAM behavioural models)
    LOCKSTEP_DEFINES  comma-separated defines (e.g. USE_IHP_SRAM,FUNCTIONAL,SIM)
    LOCKSTEP_TAG      build-directory suffix so that different configurations do not share a build"""
    from cocotb_tools.runner import get_runner
    tag = os.environ.get("LOCKSTEP_TAG", "")
    build = HERE / ("sim_build" + (f"_{tag}" if tag else ""))
    sources = _paths("LOCKSTEP_NETLIST") or RTL
    defines = {d: 1 for d in os.environ.get("LOCKSTEP_DEFINES", "").split(",") if d}
    r = get_runner("icarus")
    r.build(sources=sources + _paths("LOCKSTEP_EXTRA"), hdl_toplevel="tt_um_brentius_metronome", build_dir=build,
            includes=[ROOT / "src"], defines=defines, timescale=("1ns", "1ps"), always=False)
    r.test(hdl_toplevel="tt_um_brentius_metronome", test_module="lockstep_tb", build_dir=build, test_dir=HERE,
           extra_env={"LOCKSTEP_SCENARIO": scenario}, results_xml=str(build / f"results_{scenario}.xml"))
    import xml.etree.ElementTree as ET
    root = ET.parse(build / f"results_{scenario}.xml").getroot()
    failures = root.findall(".//failure") + root.findall(".//error")
    assert not failures, f"{scenario}: {[f.get('message') for f in failures]}"


@pytest.mark.parametrize("scenario", ["smoke", "regs", "blink", "proto_uart_tx", "proto_uart_rx", "proto_spi_controller", "proto_eth_tx"] + [f"random_{s}" for s in range(1, SEEDS + 1)])
def test_lockstep(scenario):
    _run(scenario)
