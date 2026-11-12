"""Area of cfg_latch_bank vs cfg_flop_bank at BYTES=256 (2,048 bits), IHP sg13cmos5l typical library.

    source code/tools/env.sh && python sim/numerics/v2_sizing/area_latch.py

Runs area_latch.ys with yosys (cwd = repo root, relative paths: yosys does not accept quoted paths), writes the raw
log to latch_area.log and prints a summary. Evidence class: synthesized estimate (pre-placement, flat, no clock tree).
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LIB = "build/pdk/sg13cmos5l_stdcell_typ_1p20V_25C.lib"
REL = HERE.relative_to(ROOT).as_posix()


def cells(block: str) -> dict[str, int]:
    return {n: int(c) for c, n in re.findall(r"^\s+(\d+)\s+[\d.E+]+\s+(sg13\S+)\s*$", block, re.M)}


def main() -> int:
    script = (HERE / "area_latch.ys").read_text().replace("@LIB@", LIB).replace("@RTL@", f"{REL}/rtl").replace("@OUT@", REL)
    tmp = HERE / "_area_run.ys"
    tmp.write_text(script)
    try:
        p = subprocess.run(["yosys", "-l", f"{REL}/latch_area.log", str(tmp.relative_to(ROOT).as_posix())],
                           cwd=ROOT, capture_output=True, text=True)
    finally:
        tmp.unlink(missing_ok=True)
    if p.returncode:
        print(p.stdout[-3000:], p.stderr[-3000:])
        return p.returncode
    log = (HERE / "latch_area.log").read_text(errors="replace")
    blocks = [b for b in re.split(r"\n\d+\. Printing statistics\.", log)[1:] if "Chip area" in b]
    areas = [float(re.search(r"Chip area for module [^:]+: ([\d.]+)", b).group(1)) for b in blocks]
    cl, cf = cells(blocks[0]), cells(blocks[1])
    lib_area = {}
    for n in cl.keys() | cf.keys():
        m = re.search(rf"cell \({n}\) \{{\s*area : ([\d.]+)", (ROOT / LIB).read_text())
        lib_area[n] = float(m.group(1)) if m else 0.0
    bits = 2048

    def rows(name, c, total):
        print(f"\n{name}: total {total:.1f} um2 = {total / bits:.2f} um2/bit ({bits} bits)")
        for n, k in sorted(c.items(), key=lambda t: -t[1] * lib_area[t[0]]):
            print(f"  {k:6d} x {n:28s} {lib_area[n]:7.2f}  = {k * lib_area[n]:10.1f}")

    rows("cfg_latch_bank", cl, areas[0])
    rows("cfg_flop_bank", cf, areas[1])
    print(f"\nsaving: {areas[1] - areas[0]:.1f} um2 ({(areas[1] - areas[0]) / bits:.2f} um2/bit)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
