"""Hierarchical standard-cell area of tt_um_brentius_metronome with the IHP sg13cmos5l typical library.

    source code/tools/env.sh && python code/tests/rtl/area.py [--lib build/pdk/<lib>] [--log <file>]

Runs code/tests/rtl/area.ys (yosys synth, keeping hierarchy; memory wrappers black-boxed; dfflibmap + abc to the
liberty cells; stat -liberty) and prints a per-module table: area per instance, instance count, total, flops.
Evidence class: synthesized estimate (pre-placement; the flattened LibreLane number was about 19% higher).
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lib", default=str(ROOT / "build/pdk/sg13cmos5l_stdcell_typ_1p20V_25C.lib"))
    ap.add_argument("--log", default=str(HERE / "sim_build" / "area.log"))
    a = ap.parse_args()
    Path(a.log).parent.mkdir(parents=True, exist_ok=True)
    lib = Path(a.lib).resolve()
    try:                                 # yosys commands do not take quoted paths; the repo path has spaces
        lib = lib.relative_to(ROOT).as_posix()
    except ValueError:
        lib = lib.as_posix()
    script = (HERE / "area.ys").read_text().replace("@LIB@", lib)
    tmp = HERE / "sim_build" / "area_run.ys"
    tmp.write_text(script)
    p = subprocess.run(["yosys", "-q", "-l", a.log, str(tmp)], cwd=ROOT, capture_output=True, text=True)
    if p.returncode:
        print(p.stdout[-3000:], p.stderr[-3000:])
        return p.returncode
    text = Path(a.log).read_text(errors="replace")
    stat = text[text.rfind("Printing statistics"):]
    stat = stat[:stat.find("=== design hierarchy ===")]
    blocks = re.split(r"\n=== (.+?) ===\n", stat)
    rows = {}
    for name, body in zip(blocks[1::2], blocks[2::2]):
        m = re.search(r"Chip area for module .*: ([\d.]+)\s*$", body, re.M)
        area = float(m.group(1)) if m else 0.0
        ffs = sum(int(n) for n in re.findall(r"^\s+(\d+)\s+[\d.E+]+\s+sg13\w*_(?:s?df|dl)\w*\s*$", body, re.M))
        rows[name] = (area, ffs, body)
    # instance counts from the top's (and every module's) submodule lists
    counts = {n: 0 for n in rows}
    top = next(n for n in rows if n.endswith("tt_um_brentius_metronome"))
    counts[top] = 1

    def subs(body):
        return [(int(c), n) for c, n in re.findall(r"^\s+(\d+)\s+-\s+(\S+)\s*$", body, re.M) if n in rows]

    order = [top]
    i = 0
    while i < len(order):
        n = order[i]
        for c, s in subs(rows[n][2]):
            counts[s] += c * counts[n]
            if s not in order:
                order.append(s)
        i += 1

    def short(n):
        n = n.replace("$paramod", "").lstrip("\\$")
        mm = re.match(r"(?:[0-9a-f]{40}\\)?\\?(\w+)", n)
        base = mm.group(1) if mm else n
        k = re.search(r"\\(\w+)=s32'([01]+)", n)
        return base + (f"[{k.group(1)}={int(k.group(2), 2)}]" if k else "")

    agg = {}
    for n, (area, ffs, _b) in rows.items():
        if counts.get(n, 0) == 0:
            continue
        key = re.sub(r"\[K=\d+\]", "", short(n))
        if "md_outcell" in key:
            key = f"md_outcell({'OE' if area >= max(r[0] for x, r in rows.items() if 'md_outcell' in x) else 'no OE'})"
        e = agg.setdefault(key, [0.0, 0, 0.0, 0])
        e[0] = area
        e[1] += counts[n]
        e[2] += area * counts[n]
        e[3] += ffs * counts[n]
    total = sum(v[2] for v in agg.values())
    tff = sum(v[3] for v in agg.values())
    print(f"{'module':28s} {'mean/inst um2':>14s} {'n':>4s} {'total um2':>11s} {'%':>6s} {'flops':>6s}")
    for k, v in sorted(agg.items(), key=lambda kv: -kv[1][2]):
        print(f"{k:28s} {v[2] / v[1]:14.0f} {v[1]:4d} {v[2]:11.0f} {100 * v[2] / total:6.1f} {v[3]:6d}")
    print(f"{'TOTAL (std cells, hierarchical)':28s} {'':14s} {'':4s} {total:11.0f} {100.0:6.1f} {tff:6d}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
