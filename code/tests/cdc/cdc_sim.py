"""Build and run the CDC jitter bench (pytest side).

RTL mode (default): the lockstep source list, IHP SRAM models, behavioural latch cells - the same build as
code/tests/lockstep_v2.

Gate-level mode: set

    CDC_GL_NETLIST   routed/ synthesised netlist (Verilog), top tt_um_brentius_metronome or CDC_GL_TOP
    CDC_STDCELL_DIR  directory with the IHP cell models: sg13cmos5l_stdcell.v and *_udp.v
    CDC_GL_TOP       optional pin-compatible top module, default tt_um_brentius_metronome

Exactly as `test/run_local.py --gl` / `code/flow/runpod/gl_v2.sh`: the IHP SRAM behavioural models are always
compiled, the netlist replaces src/, and the bench itself is unchanged because it only looks at pins.  Jitter is
injected at the *stimulus* in both modes; in the netlist the s1 flip-flop is a standard cell, so a late resolution
is modelled by delaying the pin by one cycle and letting the real cell capture it, not by forcing the cell's state.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import xml.etree.ElementTree as ET
from datetime import datetime, timezone
from pathlib import Path

from cocotb_tools.runner import get_runner

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
if str(ROOT / "code/tests/lockstep_v2") not in sys.path:
    sys.path.insert(0, str(ROOT / "code/tests/lockstep_v2"))

from rtl_sources import SRAM_MODEL, SRC, rtl_files                       # noqa: E402

TOP = "tt_um_brentius_metronome"


def tool_version(command: list[str]) -> str:
    """First line of `command`'s version output, or a readable error (never raises)."""
    try:
        proc = subprocess.run(command, capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.SubprocessError) as exc:
        return f"unavailable ({exc.__class__.__name__})"
    text = (proc.stdout or proc.stderr).strip().splitlines()
    return text[0].strip() if text else f"no output (rc={proc.returncode})"


def environment(evidence: Path, argv: list[str]) -> dict:
    """Record date, tool versions and the command line next to the results."""
    try:
        import cocotb
        cocotb_version = cocotb.__version__
    except Exception:                                    # pragma: no cover - evidence only
        cocotb_version = "unknown"
    info = {
        "date_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "command": " ".join(argv),
        "python": sys.version.split()[0],
        "cocotb": cocotb_version,
        "iverilog": tool_version(["iverilog", "-V"]),
        "verilator": tool_version(["verilator", "--version"]),
        "yosys": tool_version(["yosys", "-V"]),
        "simulator": os.environ.get("CDC_SIM", "icarus"),
        "environment": {k: v for k, v in sorted(os.environ.items())
                        if k.startswith(("CDC_", "OSS_CAD_SUITE", "VERILATOR_ROOT"))},
    }
    Path(evidence).mkdir(parents=True, exist_ok=True)
    (Path(evidence) / "environment.json").write_text(json.dumps(info, indent=2), encoding="utf-8")
    return info


def gl_config() -> tuple[Path, Path] | None:
    netlist = os.environ.get("CDC_GL_NETLIST")
    if not netlist:
        return None
    stdcell = os.environ.get("CDC_STDCELL_DIR")
    if not stdcell:
        raise RuntimeError("CDC_GL_NETLIST is set but CDC_STDCELL_DIR is not")
    netlist, stdcell = Path(netlist).resolve(), Path(stdcell).resolve()
    if not netlist.is_file():
        raise RuntimeError(f"netlist not found: {netlist}")
    if not (stdcell / "sg13cmos5l_stdcell.v").is_file():
        raise RuntimeError(f"sg13cmos5l_stdcell.v not found in {stdcell}")
    if not sorted(stdcell.glob("*_udp.v")):
        raise RuntimeError(f"no *_udp.v UDP models in {stdcell}")
    return netlist, stdcell


class Built:
    def __init__(self, runner, build_dir: Path, top: str, kind: str):
        self.runner = runner
        self.build_dir = build_dir
        self.top = top
        self.kind = kind


def build(build_dir: Path, always: bool = False) -> Built:
    gl = gl_config()
    sim = os.environ.get("CDC_SIM", "icarus")
    files, defines = rtl_files(ihp_sram=True)
    top = TOP
    if gl is None:
        sources = list(files)
        kind = "rtl"
    else:
        netlist, stdcell = gl
        kind = "gl"
        top = os.environ.get("CDC_GL_TOP", TOP)
        defines = {"FUNCTIONAL": 1, "SIM": 1, "COCOTB_SIM": 1, "GL_TEST": 1}
        sources = list(SRAM_MODEL) + sorted(stdcell.glob("*_udp.v")) + [
            stdcell / "sg13cmos5l_stdcell.v", netlist]
    runner = get_runner(sim)
    kwargs = {} if sim == "verilator" else {"timescale": ("1ns", "1ps")}
    if sim == "verilator":
        kwargs["build_args"] = ["--timing", "-Wno-fatal"]
    runner.build(sources=sources, hdl_toplevel=top, build_dir=build_dir, includes=[SRC],
                 defines=defines, always=always, **kwargs)
    return Built(runner, build_dir, top, kind)


def run(scenario: str, built: Built, seeds: str | None = None, jitter: float = 0.5,
        out: Path | None = None, expect_divergence: bool = False,
        depth: int | None = None) -> tuple[list[str], dict | None]:
    """Run one scenario; returns (failure messages, summary JSON)."""
    seeds = seeds if seeds is not None else os.environ.get("CDC_SEEDS", "1,2,3")
    env = {"CDC_SCENARIO": scenario, "CDC_SEEDS": seeds, "CDC_JITTER": str(jitter)}
    if depth is not None:
        env["CDC_JITTER_DEPTH"] = str(depth)
    if expect_divergence:
        env["CDC_EXPECT_DIVERGENCE"] = "1"
    if built.kind == "gl":
        env["CDC_GL"] = "1"
    if out is not None:
        out = Path(out).resolve()
        out.parent.mkdir(parents=True, exist_ok=True)
        out.unlink(missing_ok=True)
        env["CDC_OUT"] = str(out)
    xml = built.build_dir / f"results_{scenario}.xml"
    if xml.exists():
        xml.unlink()
    try:
        built.runner.test(hdl_toplevel=built.top, test_module="cdc_jitter_tb",
                          build_dir=built.build_dir, test_dir=HERE, extra_env=env,
                          results_xml=str(xml))
    except SystemExit:                      # cocotb 2.x runner exits on a failing test; the XML is still written
        pass
    if not xml.exists():
        raise RuntimeError(f"{scenario}: the simulation wrote no results file ({xml})")
    root = ET.parse(xml).getroot()
    cases = root.findall(".//testcase")
    if len(cases) != 1 or cases[0].find("skipped") is not None:
        raise RuntimeError(f"{scenario}: expected one executed cocotb case ({xml})")
    fails = [f.get("error_msg") or f.get("message") or f.text or f.attrib
             for f in root.findall(".//failure") + root.findall(".//error")]
    summary = None
    if out is not None and Path(out).is_file():
        summary = json.loads(Path(out).read_text(encoding="utf-8"))
    return fails, summary
