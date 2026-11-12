"""Run test.py locally without make (Windows), with the cocotb runner and Icarus, as the Makefile does.

    python run_local.py            # RTL: IHP SRAM models, behavioural latch and clock-gate cells
    python run_local.py --gl NETLIST --pdk-stdcell DIR
                                   # gate level: the post-route netlist, the PDK cell models in DIR
                                   # (sg13cmos5l_stdcell.v, and sg13cmos5l_udp.v if present) and the SRAM models

Build output: test/sim_build/{rtl,gl}; results in test/sim_build/<kind>/results.xml.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

from cocotb_tools.runner import get_results, get_runner

TEST = Path(__file__).resolve().parent
SRC = TEST.parent / "src"
SOURCES = ["project.v", "md2_host.v", "md2_commons_stub.v", "md2_core.v", "md2_core_thread.v", "md2_pmem.v",
           "md2_dmem.v", "md2_stream.v", "cfg_latch_bank.v", "cells_behav.v", "md2_sram_bb.v"]
SRAM_MODEL = [TEST / "sram_model" / f for f in ("RM_IHPSG13_1P_256x64_c2_bm_bist.v",
                                                "RM_IHPSG13_1P_512x32_c2_bm_bist.v",
                                                "RM_IHPSG13_1P_core_behavioral_bm_bist.v")]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--gl", type=Path, help="gate-level netlist")
    ap.add_argument("--pdk-stdcell", type=Path, help="directory with sg13cmos5l_stdcell.v (gate level)")
    a = ap.parse_args()

    defines = {"FUNCTIONAL": 1, "SIM": 1, "COCOTB_SIM": 1}   # COCOTB_SIM: as the cocotb Makefile flow defines it
    sources = list(SRAM_MODEL)
    if a.gl:
        kind = "gl"
        defines["GL_TEST"] = 1
        sources += sorted(a.pdk_stdcell.glob("*_udp.v")) + [a.pdk_stdcell / "sg13cmos5l_stdcell.v", a.gl]
    else:
        kind = "rtl"
        defines["USE_IHP_SRAM"] = 1
        sources += [SRC / f for f in SOURCES]
    sources.append(TEST / "tb.v")

    build = TEST / "sim_build" / kind
    runner = get_runner("icarus")
    runner.build(sources=sources, hdl_toplevel="tb", includes=[SRC], defines=defines, build_dir=build,
                 timescale=("1ns", "1ps"), always=True)
    xml = runner.test(hdl_toplevel="tb", test_module="test", test_dir=TEST, build_dir=build,
                      results_xml=str(build / "results.xml"))
    n, fail = get_results(xml)
    print(f"{kind}: {n} tests, {fail} failed")
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
