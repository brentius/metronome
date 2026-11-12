#!/bin/bash
# Gate-level run of the v2 skeleton's cocotb test on a completed harden result (pod).
#   gl_v2.sh TAG
# Uses /root/work/TAG/test/run_local.py --gl with the unpowered final netlist and the PDK cell models.
# Writes /workspace/results/TAG/gl/ and appends a line to /workspace/results/runs.log.
set -uo pipefail
TAG=$1
source "$(dirname "$0")/podenv.sh"
RES=/workspace/results/$TAG; W=/root/work/$TAG
NL=$(ls "$RES"/final/nl/*.nl.v 2>/dev/null | head -1)
[ -f "$NL" ] || { echo "no netlist for $TAG"; exit 2; }
OUT=$RES/gl
[ -e "$OUT" ] && { echo "refusing to overwrite $OUT"; exit 2; }
mkdir -p "$OUT"
cd "$W/test"
t0=$(date +%s)
/root/ttvenv/bin/python run_local.py --gl "$NL" --pdk-stdcell "$PDK_ROOT/$PDK/libs.ref/sg13cmos5l_stdcell/verilog" > "$OUT/gl.log" 2>&1
rc=$?
t1=$(date +%s)
cp sim_build/gl/results.xml "$OUT/" 2>/dev/null || true
echo "$(date -u +%Y%m%dT%H%M%SZ) $TAG gl rc=$rc wall_s=$((t1-t0))" | tee -a /workspace/results/runs.log
echo "GL_END rc=$rc"
exit $rc
