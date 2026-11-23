#!/usr/bin/env bash
# Functional gate-level reset/power-up campaign against an unpowered routed netlist.
#
#   bash code/tests/xinit/run_gate.sh NETLIST.NL.V OUTDIR
#
# NETLIST.NL.V  routed, unpowered netlist (std-cell level, top tt_um_brentius_metronome)
# OUTDIR        directory for JUnit XML, per-case JSON, gl.log and summary.json
#
# Environment:
#   XINIT_STDCELL_DIR  directory holding sg13cmos5l_stdcell.v and the *_udp.v models
#                      (default /root/pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog)
#   XINIT_PYTHON       interpreter (default /root/ttvenv/bin/python)
#   XINIT_SEEDS / XINIT_LOCKSTEP_SEEDS  ignored in gate mode (RTL-only cases are deselected)
#
# Gate mode runs the pin-only variants: X-init (all storage X) and random-SRAM init (every
# SRAM word randomised, flops still X).  Flop deposits need RTL hierarchy and are RTL-only.
# Exits non-zero when any case fails; the same status is written to summary.json.
set -euo pipefail

usage() {
    echo "usage: $0 NETLIST.NL.V OUTDIR" >&2
    exit 2
}
die() {
    echo "run_gate: $*" >&2
    exit 2
}

[[ $# == 2 ]] || usage
[[ -f $1 ]] || die "no netlist at $1"
netlist=$(cd -- "$(dirname -- "$1")" && pwd)/$(basename -- "$1")
outdir=$2
mkdir -p -- "$outdir"
outdir=$(cd -- "$outdir" && pwd)

stdcell=${XINIT_STDCELL_DIR:-/root/pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog}
[[ -f $stdcell/sg13cmos5l_stdcell.v ]] || die "no sg13cmos5l_stdcell.v in $stdcell (set XINIT_STDCELL_DIR)"
python=${XINIT_PYTHON:-/root/ttvenv/bin/python}
[[ -x $python ]] || die "no interpreter at $python (set XINIT_PYTHON)"

repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd -- "$repo"

echo "netlist: $netlist"
echo "stdcell: $stdcell"
echo "outdir : $outdir"
start=$(date +%s)
rc=0
XINIT_NETLIST=$netlist XINIT_STDCELL_DIR=$stdcell XINIT_RESULTS_DIR=$outdir \
    "$python" -m pytest code/tests/xinit -q > "$outdir/gl.log" 2>&1 || rc=$?
wall=$(($(date +%s) - start))

"$python" - "$outdir/summary.json" "$rc" "$wall" "$netlist" "$stdcell" <<'PY'
import hashlib
import json
import platform
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

path, rc, wall, netlist, stdcell = sys.argv[1:6]
log = (Path(path).parent / "gl.log").read_text(encoding="utf-8", errors="replace")


def ver(cmd):
    exe = shutil.which(cmd[0])
    if not exe:
        return "missing"
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
        return (out.stdout or out.stderr).splitlines()[0].strip()
    except Exception as e:                  # pragma: no cover - diagnostics only
        return f"error: {e}"


counts = {}
for word in ("passed", "failed", "error", "skipped"):
    found = re.findall(rf"(\d+) {word}s?\b", log)
    if found:
        counts[word] = int(found[-1])
summary = {
    "kind": "xinit_gate",
    "date_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    "netlist": netlist,
    "netlist_sha256": hashlib.sha256(Path(netlist).read_bytes()).hexdigest(),
    "stdcell_dir": stdcell,
    "returncode": int(rc),
    "wall_s": int(wall),
    "pytest_counts": counts,
    "host": platform.platform(),
    "python": sys.version.split()[0],
    "icarus": ver(["iverilog", "-V"]),
    "yosys": ver(["yosys", "-V"]),
    "cases": sorted(p.name for p in Path(path).parent.glob("*.json")),
}
Path(path).write_text(json.dumps(summary, indent=1), encoding="utf-8")
print(json.dumps({k: summary[k] for k in ("returncode", "wall_s", "pytest_counts")}))
PY

echo "$(date -u +%Y%m%dT%H%M%SZ) xinit_gl rc=$rc wall_s=$wall netlist=$netlist" | tee -a "$outdir/runs.log"
exit "$rc"
