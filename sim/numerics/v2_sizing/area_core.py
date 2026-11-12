"""Area and logic-depth estimate of the Metronome v2 pipelined core (sim/numerics/v2_sizing/rtl/).

    source code/tools/env.sh && python sim/numerics/v2_sizing/area_core.py [--log sim/numerics/v2_sizing/core_area.log]

1. Area: runs area_core.ys (yosys synth keeping hierarchy, program memory black-boxed, dfflibmap + abc to the IHP
   sg13cmos5l typical library, stat -liberty) and prints per-module area and flop counts.
2. Logic depth: for md2_core (C=0) flattened, keeps one group of endpoints at a time (all other outputs lose their
   port attribute and their exclusive logic is removed), maps with ABC to the slow-corner library
   (1.08 V, 125 C) and reads ABC's `stime -p` critical path. Combinational delay only: no wires (WireLoad none),
   no clock-to-Q at the start, no setup at the end, module inputs arrive at time 0. Evidence class: synthesized
   estimate, pre-placement.
Raw yosys output is appended to the log file.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
TYP = "build/pdk/sg13cmos5l_stdcell_typ_1p20V_25C.lib"
SLOW = "build/pdk/sg13cmos5l_stdcell_slow_1p08V_125C.lib"
PERIOD_PS = 16667
RTL = "sim/numerics/v2_sizing/rtl"

# endpoint groups of md2_core for the depth estimate (V2_DESIGN 4.6 names the first two)
CONES = {   # name: (endpoints kept, inputs tied to 0 or None)
    "IR -> jump/next address -> SRAM address (dispatch inputs tied 0)": ("w:fetch_addr w:fetch_en", "i:t_*"),
    "IR -> guard eval -> discard decision (load = xv' D, jmp)": ("w:load w:jmp", "i:t_*"),
    "IR -> move enables and source data (mv_en, mv_data)": ("w:mv_en w:mv_data", None),
    "thread state -> dispatch, watcher PC -> SRAM address": ("w:fetch_addr w:fetch_en", None),
    "whole md2_core (every output and flop input)": (None, None),
}


def yosys(script: str, tag: str, log: Path) -> str:
    tmp = HERE / f"_tmp_{tag}.ys"
    tmp.write_text(script)
    out = HERE / f"_tmp_{tag}.log"
    p = subprocess.run(["yosys", "-q", "-l", str(out), str(tmp)], cwd=ROOT, capture_output=True, text=True)
    text = out.read_text(errors="replace") if out.exists() else ""
    with log.open("a") as f:
        f.write(f"\n\n######## {tag}\n{script}\n{text}")
    tmp.unlink(missing_ok=True)
    out.unlink(missing_ok=True)
    if p.returncode:
        sys.exit(f"yosys failed ({tag}):\n{p.stdout[-2000:]}\n{p.stderr[-2000:]}")
    return text


def area(log: Path) -> dict[str, tuple[float, int, int]]:
    text = yosys((HERE / "area_core.ys").read_text().replace("@LIB@", TYP), "area", log)
    stat = text[text.rfind("Printing statistics"):]
    rows = {}
    for name, body in zip(*[iter(re.split(r"\n=== (.+?) ===\n", stat)[1:])] * 2):
        m = re.search(r"Chip area for module .*: ([\d.]+)\s*$", body, re.M)
        ffs = sum(int(n) for n in re.findall(r"^\s+(\d+)\s+[\d.E+]+\s+sg13\w*_(?:s?df|dl)\w*\s*$", body, re.M))
        rows[name.strip("\\")] = (float(m.group(1)) if m else 0.0, ffs, body)
    return rows


def depth(sel: str | None, tie: str | None, tag: str, log: Path) -> list[tuple[float, str, str, int]]:
    # flops become input/output pairs (<reg>.q / <reg>.d), so each run times one combinational cone
    cmds = [f"read_verilog -DSYNTHESIS -Icode/md2 {RTL}/md2_core.v", "hierarchy -top md2_core", "proc", "flatten",
            "opt", "dffunmap", "expose -evert-dff"]
    if sel:
        cmds += ["delete -port o:*", f"expose {sel}"]
    if tie:
        cmds += [f"delete -port {tie}", "setundef -zero -undriven"]
    cmds += ["opt_clean", "synth -top md2_core",
             f"abc -liberty {SLOW} -script +strash;&get,-n;&fraig,-x;&put;scorr;dc2;strash;&get,-n;&dch,-f;"
             f"&nf,-D,{PERIOD_PS};&put;buffer;upsize,-D,{PERIOD_PS};dnsize,-D,{PERIOD_PS};stime,-p"]
    script = "\n".join(cmds) + "\n"
    text = yosys(script, tag, log)
    res = []
    for blk in re.split(r"ABC: \+ stime -p", text)[1:]:
        d = re.search(r"Delay =\s+([\d.]+) ps", blk)
        se = re.search(r"Start-point = \S+ \((.+?)\)\.\s+End-point = \S+ \((.+?)\)\.", blk)
        levels = len(re.findall(r"ABC: Path\s+\d+ --.*sg13cmos5l_", blk[:blk.find("Start-point")]))
        if d and se:
            res.append((float(d.group(1)), se.group(1), se.group(2), levels))
    return sorted(res, reverse=True)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--log", default=str(HERE / "core_area.log"))
    a = ap.parse_args()
    log = Path(a.log)
    log.write_text("# raw yosys output of sim/numerics/v2_sizing/area_core.py\n")
    rows = area(log)
    print(f"Area, {TYP} (yosys synth + abc, hierarchical, program memory black-boxed)")
    print(f"{'module':40s} {'um2/inst':>9s} {'flops':>6s}")
    for n, (ar, ff, _b) in rows.items():
        k = re.search(r"C=s32'([01]+)", n)
        label = f"md2_core C={int(k.group(1), 2)}" if k else n
        print(f"{label[:40]:40s} {ar:9.0f} {ff:6d}")
    cores = [v for n, v in rows.items() if "md2_core" in n and "thread" not in n and "top" not in n]
    thr = next(v for n, v in rows.items() if "md2_core_thread" in n)
    top = next(v for n, v in rows.items() if n.endswith("md2_core_top"))
    tot = sum(c[0] for c in cores) + 6 * thr[0] + top[0]
    print(f"2 cores {sum(c[0] for c in cores):.0f} um2 ({sum(c[1] for c in cores)} flops); 6 thread slices "
          f"{6 * thr[0]:.0f} um2 ({6 * thr[1]} flops); glue {top[0]:.0f}; total {tot:.0f} um2")
    print(f"\nCombinational depth, {SLOW}, ABC stime (no wires, no clk-to-Q, no setup; flops cut into .q/.d ports)")
    for i, (name, (sel, tie)) in enumerate(CONES.items()):
        r = depth(sel, tie, f"depth{i}", log)
        dly, sp, ep, lv = r[0]
        print(f"{name:62s} {dly / 1000:6.2f} ns  {lv:2d} cells  {sp} -> {ep}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
