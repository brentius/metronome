"""Run test.py locally without make (Windows), with the cocotb runner and Icarus, as the Makefile does.

    python run_local.py            # RTL: IHP SRAM models, behavioural latch and clock-gate cells
    python run_local.py --gl NETLIST --pdk-stdcell DIR
                                   # gate level: the post-route netlist, the PDK cell models in DIR
                                   # (sg13cmos5l_stdcell.v, and sg13cmos5l_udp.v if present) and the SRAM models
    python run_local.py --gl NETLIST --pdk-stdcell DIR --sdf CORNER.sdf --test test_cfg [--clk-ps N]
                                   # back-annotated gate level (V2_DESIGN 4.7): SDF rewritten for Icarus by
                                   # sdf_for_icarus.py, latch probe and monitors from gen_cfg_probe.py; on the pod
                                   # see code/flow/runpod/sdf_v2.sh

Build output: test/sim_build/{rtl,gl}; results in test/sim_build/<kind>/results.xml.
"""
from __future__ import annotations

import argparse
import subprocess
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
    ap.add_argument("--sdf", type=Path, help="gate level only: annotate this SDF (signoff delays of one corner) "
                                             "and add the configuration-latch probe and monitors (CFG_PROBE)")
    ap.add_argument("--test", default="test", help="cocotb test module (test, or test_cfg with --sdf)")
    ap.add_argument("--name", help="build subdirectory under sim_build (default rtl, gl or gl_sdf)")
    ap.add_argument("--clk-ps", type=int, help="clock period for test_cfg (default 16666)")
    a = ap.parse_args()

    defines = {"FUNCTIONAL": 1, "SIM": 1, "COCOTB_SIM": 1}   # COCOTB_SIM: as the cocotb Makefile flow defines it
    sources = list(SRAM_MODEL)
    build_args, includes, env = [], [SRC], {}
    if a.gl:
        kind = "gl"
        defines["GL_TEST"] = 1
        sources += sorted(a.pdk_stdcell.glob("*_udp.v")) + [a.pdk_stdcell / "sg13cmos5l_stdcell.v", a.gl]
    else:
        kind = "rtl"
        defines["USE_IHP_SRAM"] = 1
        sources += [SRC / f for f in SOURCES]
    if a.sdf:
        assert a.gl, "--sdf needs --gl"
        kind = "gl_sdf"
    build = TEST / "sim_build" / (a.name or kind)
    if a.sdf:
        # specify blocks carry the cell delays that $sdf_annotate overwrites; the probe is generated per netlist
        build_args += ["-gspecify", "-ginterconnect"]   # -ginterconnect: SDF INTERCONNECT (wire) delays
        # Icarus cannot resolve the flattened escaped instance names: annotate a renamed copy (sdf_for_icarus.py)
        build.mkdir(parents=True, exist_ok=True)
        sdf, nl = build / "icarus.sdf", build / "netlist_icarus.v"
        subprocess.run([sys.executable, str(TEST / "sdf_for_icarus.py"), str(a.sdf), str(sdf), str(a.gl), str(nl)],
                       check=True)
        sources[sources.index(a.gl)] = nl
        defines["SDF_FILE"] = f'"{sdf.resolve().as_posix()}"'
        defines["CFG_PROBE"] = 1
        subprocess.run([sys.executable, str(TEST / "gen_cfg_probe.py"), str(a.gl), str(build)], check=True)
        includes.append(build)
        sources.append(TEST / "cfg_latch_chk.v")
        env["CFG_PROBE_JSON"] = str(build / "cfg_probe.json")
    if a.clk_ps:
        env["CLK_PS"] = str(a.clk_ps)
    sources.append(TEST / "tb.v")

    runner = get_runner("icarus")
    runner.build(sources=sources, hdl_toplevel="tb", includes=includes, defines=defines, build_dir=build,
                 build_args=build_args, timescale=("1ns", "1ps"), always=True)
    xml = runner.test(hdl_toplevel="tb", test_module=a.test, test_dir=TEST, build_dir=build,
                      results_xml=str(build / "results.xml"), extra_env=env)
    n, fail = get_results(xml)
    print(f"{kind}: {n} tests, {fail} failed")
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
