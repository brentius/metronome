"""Yosys area of a Metronome RTL tree (v2 baseline or v3) with the IHP sg13cmos5l typical library.

    . C:/Users/b_yee23/tools/oss-cad-suite/environment.ps1      (Yosys on PATH)
    python sim/numerics/v3_area/area_v3.py --src src --log data/raw/v3_rtl_20261116/area_v3.log
    python sim/numerics/v3_area/area_v3.py --src <baseline copy of src> --log .../area_v2_baseline.log

Same flow as code/tests/rtl_v2/area.py (the method behind the 274,908 um2 v2 figure): `synth`, `dfflibmap`, `abc`,
`opt_clean`, `stat -liberty`, hierarchical, defines SYNTHESIS USE_IHP_SRAM USE_IHP_CELLS (library latch and clock
gate counted, SRAM macros black boxes and not counted). Only the source directory is a parameter, so the baseline
tree (git show refs/v3-baseline/20261116:src/...) and the v3 tree are measured identically.
Evidence class: synthesized estimate, typical library (pre-placement, no clock tree, no buffering or resizing).
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "code/tests/lockstep_v2"))
from rtl_sources import SOURCES  # noqa: E402

LIB = (ROOT / "build/pdk/sg13cmos5l_stdcell_typ_1p20V_25C.lib").as_posix()
TOP = "tt_um_brentius_metronome"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--src", type=Path, default=ROOT / "src")
    ap.add_argument("--log", type=Path, required=True)
    a = ap.parse_args()
    src = a.src.resolve()
    srcs = " ".join(f'"{(src / f).as_posix()}"' for f in SOURCES)
    ys = f"""read_liberty -lib "{LIB}"
read_verilog -DSYNTHESIS -DUSE_IHP_SRAM -DUSE_IHP_CELLS -I{src.as_posix()} {srcs}
synth -top {TOP}
dfflibmap -liberty "{LIB}"
abc -liberty "{LIB}"
opt_clean
stat -liberty "{LIB}"
"""
    log = a.log.resolve()
    log.parent.mkdir(parents=True, exist_ok=True)
    ysf = log.with_suffix(".ys")
    ysf.write_text(ys)
    p = subprocess.run(["yosys", "-q", "-l", str(log), "-s", str(ysf)], capture_output=True, text=True)
    if p.returncode:
        print(p.stdout[-3000:], p.stderr[-3000:])
        return p.returncode
    txt = log.read_text(errors="replace")
    hier = txt[txt.rindex("=== design hierarchy ==="):]
    print(re.search(r"Yosys \S+ \([^)]*\)", txt).group(0) if re.search(r"Yosys \S+ \([^)]*\)", txt) else "yosys")
    for cnt, area, name in re.findall(r"^\s+(\d+)\s+([\d.E+]+)\s+(\S*(?:md2_|tt_um_)\S*)\s*$", hier, re.M):
        short = re.sub(r"^\$paramod\S*?\\", "", name.split("$")[-1]) if "$" in name else name
        print(f"  {int(cnt):7d} {float(area):12.1f}  {short}")
    print(re.search(r"Chip area for top module .*", txt).group(0))
    return 0


if __name__ == "__main__":
    sys.exit(main())
