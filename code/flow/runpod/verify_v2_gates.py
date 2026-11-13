#!/usr/bin/env python3
"""Run v2 pin/model lockstep against a routed netlist (zero delay or SDF).

Run separately for each extracted corner SDF, for example:
  python verify_v2_gates.py --repo /workspace/jsc --netlist .../final/nl/design.nl.v \
    --cells /root/pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog --out .../gl_zero
  python verify_v2_gates.py --repo /workspace/jsc --netlist .../design.nl.v --cells ... \
    --out .../gl_slow --sdf .../nom_slow_1p08V_125C/design.sdf

Icarus SDF limitations: project-local sdf_for_icarus.py renames escaped cell instances,
drops cell-to-cell INTERCONNECT delays (reports the largest dropped delay), and drops SRAM
macro timing blocks. Icarus does not support SDF TIMINGCHECKs. These runs check functional
pin/model agreement under the delays Icarus can annotate; they are not timing signoff.
"""
from __future__ import annotations

import argparse
import contextlib
import json
import os
import re
import subprocess
import shutil
import sys
import time
import traceback
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from cocotb_tools.runner import get_runner

SCENARIOS = ["smoke", "eth_loopback", "follower", "hold", "taps", "units", "reset_mid",
             "spi_target", "shifter_parallel"]
TOP = "tt_um_brentius_metronome"
WRAPPER = "v2_gate_tb"


def sha256(path: Path) -> str:
    import hashlib
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def atomic_json(path: Path, value: Any) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def xml_result(path: Path) -> tuple[int, list[str]]:
    import xml.etree.ElementTree as ET
    if not path.is_file():
        raise RuntimeError(f"cocotb did not produce results XML: {path}")
    root = ET.parse(path).getroot()
    skipped = root.findall(".//skipped")
    failed = root.findall(".//failure") + root.findall(".//error")
    details = [f"skip: {e.get('message', '')}" for e in skipped]
    details += [f"failure: {e.get('message', '')}" for e in failed]
    cases = [tc for tc in root.iter("testcase") if tc.find("skipped") is None]
    if len(cases) != 1:
        details.append(f"expected one executed testcase, found {len(cases)}")
    return len(cases), details


def sram_instances(netlist_text: str) -> dict[str, str]:
    """Find preserved macro instances and associate them with the three memories."""
    found: dict[str, str] = {}
    pattern = re.compile(
        r"\bRM_IHPSG13_1P_(?:256x64|512x32)_c2_bm_bist\s+"
        r"(?:\\([^\s]+)\s|([A-Za-z_$][\w$]*))"
    )
    for m in pattern.finditer(netlist_text):
        escaped, plain = m.groups()
        inst = (escaped or plain or "").replace("\\", "").rstrip()
        flat = inst.replace(".", "__").replace("[", "_").replace("]", "_")
        for memory in ("u_pmem0", "u_pmem1", "u_dmem"):
            if memory in flat:
                if memory in found:
                    raise RuntimeError(f"multiple preserved SRAM instances match {memory}: {found[memory]}, {flat}")
                found[memory] = inst
    if set(found) != {"u_pmem0", "u_pmem1", "u_dmem"}:
        raise RuntimeError(f"could not map all three SRAM instances in routed netlist: {found}")
    return found


def make_gate_harness(source: Path, destination: Path, memory_map: dict[str, str]) -> None:
    """Copy the scenario checker with gate-safe SRAM access and settled sampling."""
    text = source.read_text(encoding="utf-8")
    testdir = source.parent.resolve()
    root = testdir.parents[2]
    text = text.replace('sys.path[:0] = [str(HERE.parents[2] / "sim/reference"), str(HERE)]',
                        f'sys.path[:0] = {[str(root / "sim/reference"), str(testdir)]!r}')
    text = text.replace("from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge",
                        "from cocotb.triggers import FallingEdge, RisingEdge, Timer")
    text = text.replace('Clock(dut.clk, 16, unit="ns")', 'Clock(dut.clk, 16.666, unit="ns")')
    text = text.replace("await ReadOnly()", 'await Timer(8, unit="ns")')
    text = text.replace('dut._log.error(f"rtl  : {rtl_state(dut)}")',
                        'dut._log.error("rtl internal probes unavailable in routed netlist")')
    start = text.index("def zero_srams(dut) -> int:")
    end = text.index("\n\ndef model_state", start)
    fn = "\n".join([
        "def zero_srams(dut) -> int:",
        '    """Initialize SRAM models only; routed RTL internals are not probed."""',
        f"    names = {memory_map!r}",
        '    for key, words in (("u_pmem0", 256), ("u_pmem1", 256), ("u_dmem", 512)):',
        '        macro = getattr(dut.user_project, names[key])',
        '        try:',
        '            memory = macro.i_SRAM_1P_behavioral_bm_bist.memory',
        '        except AttributeError as e:',
        '            raise AssertionError(f"cannot access SRAM array for {key} via {names[key]}") from e',
        '        for i in range(words):',
        '            memory[i].value = 0',
        '    return 3',
    ])
    text = text[:start] + fn + text[end:]
    # Use separate stimulus/model and output-checker coroutines. The checker samples
    # 8 ns after each rising edge, before the next falling-edge stimulus update.
    test_start = text.index("@cocotb.test()")
    test = '''@cocotb.test()
async def lockstep(dut):
    name = os.environ.get("LOCKSTEP_SCENARIO", "smoke")
    scen = scenarios.build(name)
    cocotb.start_soon(Clock(dut.clk, 16.666, unit="ns").start())
    model = Chip()
    dut.ena.value = 1
    dut.ui_in.value = scenarios.IDLE
    dut.uio_in.value = 0
    dut.rst_n.value = 1
    zero_srams(dut)
    outs = (0, 0, 0)
    expected = []
    done = cocotb.triggers.Event()
    mismatches = []

    async def drive_and_model():
        nonlocal outs
        for t, (ui, hi, uio, rst_n) in enumerate(scen.steps):
            await FallingEdge(dut.clk)
            uio = uio(t, outs) if callable(uio) else uio
            hi = hi(t, outs) if callable(hi) else hi
            ui = (ui & 0x07) | (hi & 0xF8)
            dut.ui_in.value = ui
            dut.uio_in.value = uio & 0xFF
            dut.rst_n.value = rst_n
            exp = tuple(model.step(ui, uio & 0xFF, rst_n))
            expected.append((t, exp, ui, uio & 0xFF))
            outs = exp
        done.set()

    async def check_outputs():
        # Ignore the clock's initial rising edge; scenario step 0 is driven at
        # the first falling edge and is modeled for the following rising edge.
        await FallingEdge(dut.clk)
        for _ in range(len(scen.steps)):
            await RisingEdge(dut.clk)
            await Timer(8, unit="ns")
            if not expected:
                raise AssertionError("checker reached a clock edge without a modeled stimulus")
            t, exp, ui, uio = expected.pop(0)
            got = (_val(dut.uo_out), _val(dut.uio_out), _val(dut.uio_oe))
            if t >= scen.compare_from and got != exp:
                mismatches.append((t, got, exp, ui, uio))
                if len(mismatches) == 1:
                    dut._log.error(f"model: {model_state(model)}")
                    dut._log.error("rtl internal probes unavailable in routed netlist")
                if len(mismatches) <= 10:
                    dut._log.error(f"cycle {t}: rtl uo/uio/oe={got} model={exp} (ui={ui:#04x} uio={uio:#04x})")

    checker = cocotb.start_soon(check_outputs())
    await drive_and_model()
    await checker
    await done.wait()
    assert not mismatches, f"{len(mismatches)} mismatching cycles in {name}, first {mismatches[0][0]}"
    dut._log.info(f"scenario {name}: {len(scen.steps)} cycles, outputs identical")
'''
    destination.write_text(text[:test_start] + test, encoding="utf-8")


def make_sdf_wrapper(source: Path, destination: Path, sdf_path: Path | None) -> None:
    """Wrap the routed top like the proven skeleton bench so $sdf_annotate has a scope."""
    text = source.read_text(encoding="utf-8", errors="replace")
    if sdf_path is None:
        # Icarus exposes escaped dotted macro names as HierarchyArrayObject,
        # making their SRAM arrays inaccessible in cocotb. Rename instances in
        # this simulation-only copy, just as the SDF converter already does.
        pattern = re.compile(r"^(\s*)(sg13cmos5l_\w+|RM_IHPSG13_\w+)(\s+)\\(\S+)(\s)", re.M)
        def plain(match):
            name = match[4].replace(".", "__").replace("[", "_").replace("]", "_")
            return f"{match[1]}{match[2]}{match[3]}{name}{match[5]}"
        text = pattern.sub(plain, text)
    old = f"module {TOP} ("
    if text.count(old) != 1:
        raise RuntimeError(f"expected one module declaration for {TOP} in netlist")
    # Preserve the routed module's type: the SDF root CELLTYPE must match it.
    wrapper = f'''\n\nmodule {WRAPPER} (
    input wire [7:0] ui_in, output wire [7:0] uo_out,
    input wire [7:0] uio_in, output wire [7:0] uio_out, output wire [7:0] uio_oe,
    input wire ena, input wire clk, input wire rst_n
);
`ifdef SDF_FILE
    initial $sdf_annotate(`SDF_FILE, user_project);
`endif
    {TOP} user_project (.*);
endmodule
'''
    destination.write_text(text + wrapper, encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True, help="checkout containing code/tests/lockstep_v2 and test/sram_model")
    ap.add_argument("--netlist", type=Path, required=True, help="full routed netlist (final/nl/*.nl.v)")
    ap.add_argument("--cells", type=Path, required=True, help="IHP stdcell Verilog model directory")
    ap.add_argument("--out", type=Path, required=True, help="new, empty output directory; existing path is refused")
    ap.add_argument("--sdf", type=Path, help="one corner SDF; invoke separately for typ, slow and fast")
    ap.add_argument("--seeds", type=int, default=4, help="random scenarios, seeds 1..N (default: 4)")
    a = ap.parse_args()

    repo = a.repo.resolve(); netlist = a.netlist.resolve(); cells = a.cells.resolve()
    sdf = a.sdf.resolve() if a.sdf else None
    out = a.out.resolve()
    if a.seeds < 0:
        ap.error("--seeds must be nonnegative")
    for p, label in ((repo, "repo"), (netlist, "netlist"), (cells, "cells")):
        if not p.exists():
            ap.error(f"{label} path does not exist: {p}")
    if not (repo / "code/tests/lockstep_v2/lockstep_tb.py").is_file():
        ap.error(f"not a v2 checkout: {repo}")
    if not (repo / "test/sram_model/RM_IHPSG13_1P_256x64_c2_bm_bist.v").is_file():
        ap.error(f"missing IHP SRAM behavioral models under {repo / 'test/sram_model'}")
    if not (cells / "sg13cmos5l_stdcell.v").is_file():
        ap.error(f"missing sg13cmos5l_stdcell.v under {cells}")
    if sdf and not sdf.is_file():
        ap.error(f"SDF does not exist: {sdf}")
    if out.exists():
        ap.error(f"refusing existing output path: {out}")
    out.mkdir(parents=True)
    # vvp's buffered C stdout can interleave partial SDF warnings with cocotb
    # writes, defeating strict annotation diagnostics. Preserve complete lines.
    if os.name == "posix":
        if shutil.which("stdbuf") is None:
            ap.error("stdbuf is required for complete SDF diagnostic lines")
        os.environ["SIM_CMD_PREFIX"] = "stdbuf -oL -eL"

    testdir = repo / "code/tests/lockstep_v2"
    # Resolve the tested runner's documented converter; this preserves its tested SDF rewrite.
    converter = repo / "sim/numerics/v2_sizing/tt_v2_pnr/test/sdf_for_icarus.py"
    if sdf and not converter.is_file():
        ap.error(f"SDF conversion helper is missing: {converter}")
    scenarios = SCENARIOS + [f"random_{i}" for i in range(1, a.seeds + 1)]
    manifest: dict[str, Any] = {
        "started_utc": datetime.now(timezone.utc).isoformat(), "repo": str(repo),
        "netlist": str(netlist), "netlist_sha256": sha256(netlist), "cells": str(cells),
        "sdf": str(sdf) if sdf else None, "sdf_sha256": sha256(sdf) if sdf else None,
        "out": str(out), "seeds": a.seeds, "scenarios": scenarios,
        "clock_period_ns": 16.666, "runner_sha256": sha256(Path(__file__)),
        "sim_command_prefix": os.environ.get("SIM_CMD_PREFIX", ""),
        "known_sdf_limitations": [], "runs": [],
    }
    if sdf:
        manifest["known_sdf_limitations"] = [
            "Icarus does not support SDF TIMINGCHECKs; these are counted/reported, not enforced.",
            "sdf_for_icarus.py drops cell-to-cell INTERCONNECT delays and SRAM macro SDF blocks.",
            "Outputs are sampled 8 ns after rising edges; this functional test is not a path timing proof.",
        ]
    atomic_json(out / "manifest.json", manifest)
    sys.path[:0] = [str(testdir), str(repo / "sim/reference")]
    os.chdir(repo)

    # Netlist and PDK models are common across scenarios. Build once per delay mode, then
    # re-run cocotb with a distinct scenario and immutable XML/log path for each case.
    mode = "sdf" if sdf else "zero"
    build = out / "build"
    build.mkdir()
    sources: list[Path] = sorted((repo / "test/sram_model").glob("*.v"))
    sources += sorted(cells.glob("*_udp.v"))
    sources += [cells / "sg13cmos5l_stdcell.v"]
    net_for_sim = build / "netlist_wrapped.v"
    defines = {"FUNCTIONAL": 1, "SIM": 1, "GL_TEST": 1}
    build_args: list[str] = []
    try:
        mmap = sram_instances(netlist.read_text(encoding="utf-8", errors="replace"))
    except Exception as e:
        manifest["runs"].append({"status": "FAIL", "error": f"SRAM instance mapping failed: {e}"})
        atomic_json(out / "manifest.json", manifest)
        return 1
    if sdf:
        renamed_netlist = build / "netlist_icarus.v"
        sdf_for_sim = build / "icarus.sdf"
        converter_log = build / "sdf_conversion.log"
        p = subprocess.run([sys.executable, str(converter), str(sdf), str(sdf_for_sim),
                            str(netlist), str(renamed_netlist)], text=True, capture_output=True)
        converter_log.write_text(p.stdout + p.stderr, encoding="utf-8")
        if p.returncode:
            manifest["runs"].append({"status": "FAIL", "error": f"SDF conversion rc={p.returncode}"})
            atomic_json(out / "manifest.json", manifest)
            return 1
        defines["SDF_FILE"] = f'"{sdf_for_sim.as_posix()}"'
        build_args = ["-gspecify", "-ginterconnect"]
        manifest["sdf_conversion"] = p.stdout.strip()
        try:
            make_sdf_wrapper(renamed_netlist, net_for_sim, sdf_for_sim)
            mmap = sram_instances(renamed_netlist.read_text(encoding="utf-8"))
        except Exception as e:
            manifest["runs"].append({"status": "FAIL", "error": f"netlist wrapper generation failed: {e}"})
            atomic_json(out / "manifest.json", manifest)
            return 1
    else:
        try:
            make_sdf_wrapper(netlist, net_for_sim, None)
            mmap = sram_instances(net_for_sim.read_text(encoding="utf-8"))
        except Exception as e:
            manifest["runs"].append({"status": "FAIL", "error": f"netlist wrapper generation failed: {e}"})
            atomic_json(out / "manifest.json", manifest)
            return 1
    harness = out / "lockstep_gate_tb.py"
    make_gate_harness(testdir / "lockstep_tb.py", harness, mmap)
    manifest["harness_sha256"] = sha256(harness)
    manifest["sram_instances"] = mmap
    manifest["sampling"] = "8 ns after rising edge (before next falling-edge drive)"
    atomic_json(out / "manifest.json", manifest)
    sources.append(net_for_sim)
    runner = get_runner("icarus")
    build_log = out / "build.log"
    try:
        with build_log.open("w", encoding="utf-8") as log, contextlib.redirect_stdout(log), contextlib.redirect_stderr(log):
            runner.build(sources=sources, hdl_toplevel=WRAPPER, build_dir=build,
                         defines=defines, build_args=build_args, timescale=("1ns", "1ps"), always=True,
                         log_file=out / "compile.log")
    except Exception as e:
        manifest["runs"].append({"status": "FAIL", "error": f"compile/build failed: {e}"})
        manifest["finished_utc"] = datetime.now(timezone.utc).isoformat()
        atomic_json(out / "manifest.json", manifest)
        return 1

    all_ok = True
    for scenario in scenarios:
        name = re.sub(r"[^A-Za-z0-9_.-]", "_", scenario)
        xml = out / f"results_{name}.xml"
        logpath = out / f"run_{name}.log"
        start = time.time()
        row: dict[str, Any] = {"scenario": scenario, "xml": str(xml), "log": str(logpath)}
        try:
            with logpath.open("w", encoding="utf-8") as log, contextlib.redirect_stdout(log), contextlib.redirect_stderr(log):
                returned_xml = runner.test(hdl_toplevel=WRAPPER, test_module="lockstep_gate_tb", build_dir=build,
                                           test_dir=out, results_xml=str(xml),
                                           extra_env={"LOCKSTEP_SCENARIO": scenario}, log_file=out / f"sim_{name}.log")
            xmlpath = Path(returned_xml) if returned_xml else xml
            if xmlpath.resolve() != xml.resolve() and xmlpath.exists():
                shutil.copy2(xmlpath, xml)
            count, issues = xml_result(xml)
            logtext = logpath.read_text(encoding="utf-8", errors="replace") + (out / f"sim_{name}.log").read_text(encoding="utf-8", errors="replace")
            errors = re.findall(r"SDF ERROR[^\n]*", logtext, flags=re.IGNORECASE)
            warnings = [w for w in re.findall(r"SDF WARNING[^\n]*", logtext, flags=re.IGNORECASE)
                        if "TIMINGCHECK NOT SUPPORTED" not in w.upper()]
            unsupported = re.findall(r"[^\n]*TIMINGCHECK not supported[^\n]*", logtext, flags=re.IGNORECASE)
            row.update({"testcases_executed": count, "issues": issues, "sdf_errors": errors,
                        "sdf_unmatched_or_other_warnings": warnings,
                        "timingcheck_unsupported_count": len(unsupported),
                        "timingcheck_unsupported_examples": unsupported[:10],
                        "wall_seconds": round(time.time() - start, 3)})
            row["status"] = "PASS" if not issues and not errors and not warnings else "FAIL"
        except Exception as e:
            row.update({"status": "FAIL", "issues": [f"{type(e).__name__}: {e}"],
                        "traceback": traceback.format_exc(), "wall_seconds": round(time.time() - start, 3)})
        if row["status"] != "PASS":
            all_ok = False
        manifest["runs"].append(row)
        atomic_json(out / "manifest.json", manifest)

    manifest["finished_utc"] = datetime.now(timezone.utc).isoformat()
    manifest["status"] = "PASS" if all_ok else "FAIL"
    manifest["summary"] = {"passed": sum(r["status"] == "PASS" for r in manifest["runs"]),
                           "failed": sum(r["status"] != "PASS" for r in manifest["runs"]),
                           "total": len(manifest["runs"])}
    atomic_json(out / "manifest.json", manifest)
    atomic_json(out / "summary.json", {"status": manifest["status"], **manifest["summary"],
                                       "sdf": manifest["sdf"], "known_sdf_limitations": manifest["known_sdf_limitations"]})
    print(f"{manifest['status']}: {manifest['summary']['passed']}/{manifest['summary']['total']} scenarios; see {out}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
