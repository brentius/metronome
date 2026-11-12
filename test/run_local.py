"""Run test.py locally without make (Windows), with the cocotb runner and Icarus, as test/Makefile does.

    python test/run_local.py                                   # RTL: IHP SRAM models, behavioural latch cells
    python test/run_local.py --gl NETLIST --pdk-stdcell DIR    # gate level: netlist, PDK cell models in DIR

Build output: test/sim_build/{rtl,gl}; results in test/sim_build/<kind>/results.xml.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from cocotb_tools.runner import get_results, get_runner

TEST = Path(__file__).resolve().parent
SRC = TEST.parent / "src"


def project_sources() -> list[str]:
    """PROJECT_SOURCES from the Makefile (one source list for both)."""
    mk = re.sub(r"\\\r?\n", " ", (TEST / "Makefile").read_text(encoding="utf-8"))
    return re.search(r"^PROJECT_SOURCES\s*=\s*(.*)$", mk, re.M).group(1).split()


SRAM_MODEL = [TEST / "sram_model" / f for f in ("RM_IHPSG13_1P_256x64_c2_bm_bist.v",
                                                "RM_IHPSG13_1P_512x32_c2_bm_bist.v",
                                                "RM_IHPSG13_1P_core_behavioral_bm_bist.v")]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--gl", type=Path, help="gate-level netlist")
    ap.add_argument("--pdk-stdcell", type=Path, help="directory with sg13cmos5l_stdcell.v (gate level)")
    a = ap.parse_args()
    defines = {"FUNCTIONAL": 1, "SIM": 1, "COCOTB_SIM": 1}
    sources = list(SRAM_MODEL)
    if a.gl:
        kind = "gl"
        defines["GL_TEST"] = 1
        sources += sorted(a.pdk_stdcell.glob("*_udp.v")) + [a.pdk_stdcell / "sg13cmos5l_stdcell.v", a.gl]
    else:
        kind = "rtl"
        defines["USE_IHP_SRAM"] = 1
        sources += [SRC / f for f in project_sources()]
    build = TEST / "sim_build" / kind
    r = get_runner("icarus")
    r.build(sources=sources + [TEST / "tb.v"], hdl_toplevel="tb", build_dir=build, includes=[SRC], defines=defines,
            timescale=("1ns", "1ps"), always=True)
    xml = build / "results.xml"
    r.test(hdl_toplevel="tb", test_module="test", build_dir=build, test_dir=TEST, results_xml=str(xml))
    total, failed = get_results(xml)
    print(f"{kind}: {total} test(s), {failed} failed")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
