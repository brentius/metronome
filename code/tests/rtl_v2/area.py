"""Yosys area of the v2 RTL (tt_um_brentius_metronome) with the IHP sg13cmos5l typical library.

    source code/tools/env.sh && python code/tests/rtl_v2/area.py

As sim/numerics/v2_sizing: `synth`, `dfflibmap` and `abc` against build/pdk/sg13cmos5l_stdcell_typ_1p20V_25C.lib,
hierarchical, then `stat -liberty`. USE_IHP_CELLS instantiates the library latch and clock gate in md2_cfg_bank
(read as -lib cells, so their library area is counted); USE_IHP_SRAM instantiates the SRAM macros, which are black
boxes and not counted. Raw log: code/tests/rtl_v2/area.log. Evidence class: synthesized estimate (pre-placement,
no clock tree, no buffering or resizing).
"""
from __future__ import annotations

import re
import argparse
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE.parents[0] / "lockstep_v2"))
from rtl_sources import SOURCES  # noqa: E402

LIB = "build/pdk/sg13cmos5l_stdcell_typ_1p20V_25C.lib"
TOP = "tt_um_brentius_metronome"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--log", type=Path, default=HERE / "area.log", help="Yosys log destination")
    args = ap.parse_args()
    srcs = " ".join(f"src/{f}" for f in SOURCES)
    ys = f"""read_liberty -lib {LIB}
read_verilog -DSYNTHESIS -DUSE_IHP_SRAM -DUSE_IHP_CELLS -Isrc {srcs}
synth -top {TOP}
dfflibmap -liberty {LIB}
abc -liberty {LIB}
opt_clean
stat -liberty {LIB}
"""
    tmp = HERE / "_area_run.ys"
    tmp.write_text(ys)
    log = args.log.resolve()
    log.parent.mkdir(parents=True, exist_ok=True)
    try:
        p = subprocess.run(["yosys", "-l", log.relative_to(ROOT).as_posix(), tmp.relative_to(ROOT).as_posix()],
                           cwd=ROOT, capture_output=True, text=True)
    finally:
        tmp.unlink(missing_ok=True)
    if p.returncode:
        print(p.stdout[-3000:], p.stderr[-3000:])
        return p.returncode
    txt = log.read_text(errors="replace")
    hier = txt[txt.rindex("=== design hierarchy ==="):]
    print(re.search(r"Yosys \S+ \([^)]*\)", txt).group(0))
    print("cells (incl. submodules), area um2 (incl. submodules), module:")
    for cnt, area, name in re.findall(r"^\s+(\d+)\s+([\d.E+]+)\s+(\S*(?:md2_|tt_um_)\S*)\s*$", hier, re.M):
        short = re.sub(r"^\$paramod\S*?\\", "", name.split("$")[-1]) if "$" in name else name
        print(f"  {int(cnt):7d} {float(area):12.1f}  {short}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
