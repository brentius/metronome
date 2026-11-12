"""Standard-cell area of one md2_stream.   source code/tools/env.sh && python sim/numerics/v2_sizing/area_stream.py
Evidence class: synthesized estimate (yosys synth + abc, pre-placement)."""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LIB = "build/pdk/sg13cmos5l_stdcell_typ_1p20V_25C.lib"
LOG = HERE / "stream_area.log"


def main() -> int:
    tmp = HERE / "area_stream_run.ys"
    tmp.write_text((HERE / "area_stream.ys").read_text().replace("@LIB@", LIB))
    try:   # the repo path has spaces; yosys takes relative paths
        p = subprocess.run(["yosys", "-l", str(LOG), str(tmp.relative_to(ROOT))], cwd=ROOT, capture_output=True, text=True)
    finally:
        tmp.unlink(missing_ok=True)
    if p.returncode:
        print(p.stdout[-3000:], p.stderr[-3000:])
        return p.returncode
    text = LOG.read_text(errors="replace")
    area = float(re.findall(r"Chip area for module .*: ([\d.]+)", text)[-1])
    ffs = sum(int(n) for n in re.findall(r"^\s+(\d+)\s+[\d.E+]+\s+sg13\w*_(?:s?df|dl)\w*\s*$", text[text.rfind("Printing statistics"):], re.M))
    print(f"md2_stream area {area:.0f} um2, flops {ffs}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
