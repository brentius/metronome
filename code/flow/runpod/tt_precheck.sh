#!/bin/bash
# Run the Tiny Tapeout precheck (tt-support-tools/precheck) on a completed harden result.
#   tt_precheck.sh TAG
# Reads /workspace/results/TAG/tt_submission/*.gds*, writes /workspace/results/TAG/precheck/.
set -uo pipefail
TAG=$1
source "$(dirname "$0")/podenv.sh"
RES=/workspace/results/$TAG
GDS=$(ls "$RES"/tt_submission/*.gds* 2>/dev/null | head -1)
[ -n "$GDS" ] || { echo "no GDS under $RES/tt_submission"; exit 2; }
# precheck.py looks for info.yaml in the GDS directory and its parents
[ -e "$RES/info.yaml" ] || cp "/root/work/$TAG/info.yaml" "$RES/info.yaml" 2>/dev/null     || { echo "no info.yaml for $TAG"; exit 2; }
OUT=$RES/precheck
[ -e "$OUT" ] && { echo "refusing to overwrite $OUT"; exit 2; }
mkdir -p "$OUT"
cd /root/tt/precheck
rm -rf reports && mkdir -p reports
t0=$(date +%s)
/root/ttvenv/bin/python precheck.py --gds "$GDS" --tech "$PDK" > "$OUT/precheck.log" 2>&1
rc=$?
t1=$(date +%s)
cp -r reports "$OUT/" 2>/dev/null || true
echo "$(date -u +%Y%m%dT%H%M%SZ) $TAG precheck rc=$rc wall_s=$((t1-t0))" | tee -a /workspace/results/runs.log
echo "PRECHECK_END rc=$rc"
exit $rc
