#!/bin/bash
# Harden a Tiny Tapeout project directory with the official tt-support-tools flow (no Docker).
#   tt_harden.sh PROJECT_TGZ TAG
# PROJECT_TGZ: path (on the pod) of a tarball whose root holds info.yaml, src/, test/, docs/.
# Work happens on container disk; results are copied to /workspace/results/TAG and logged in runs.log.
set -uo pipefail
TGZ=$1; TAG=$2
export PDK_ROOT=${PDK_ROOT:-/root/pdk}
export PDK=ihp-sg13cmos5l
source "$(dirname "$0")/podenv.sh"
WORK=/root/work/$TAG; RES=/workspace/results/$TAG
if [ -e "$WORK" ] || [ -e "$RES" ]; then echo "refusing to overwrite $WORK or $RES"; exit 2; fi
mkdir -p "$WORK" "$RES"
tar -xzf "$TGZ" -C "$WORK"
cd "$WORK"
git init -q . 2>/dev/null; git add -A >/dev/null 2>&1; git -c user.email=flow@local -c user.name=flow commit -qm snapshot >/dev/null 2>&1 || true
ln -sfn /root/tt tt
PY=/root/ttvenv/bin/python
t0=$(date +%s)
{
  $PY ./tt/tt_tool.py --create-user-config --pdk $PDK && \
  $PY ./tt/tt_tool.py --harden --no-docker --pdk $PDK
} > "$RES/harden.log" 2>&1
rc=$?
t1=$(date +%s)
$PY ./tt/tt_tool.py --print-stats --pdk $PDK > "$RES/stats.md" 2>&1 || true
$PY ./tt/tt_tool.py --print-cell-category --pdk $PDK > "$RES/cells.md" 2>&1 || true
$PY ./tt/tt_tool.py --print-warnings --pdk $PDK > "$RES/warnings.md" 2>&1 || true
[ $rc -eq 0 ] && { $PY ./tt/tt_tool.py --create-tt-submission --pdk $PDK > "$RES/submission.log" 2>&1 || true; }
# copy reports, logs, metrics and final views (not the whole run tree)
if [ -d runs/wokwi ]; then
  ( cd runs/wokwi && find . \( -name '*.log' -o -name '*.rpt' -o -name 'metrics.*' -o -name '*.json' -o -name '*.sdc' \) -size -20M -print0 | tar --null -czf "$RES/run_text.tgz" -T - ) || true
  cp -r runs/wokwi/final "$RES/final" 2>/dev/null || true
fi
[ -d tt_submission ] && cp -r tt_submission "$RES/" 2>/dev/null
cp src/config_merged.json "$RES/" 2>/dev/null || true
cp info.yaml "$RES/" 2>/dev/null || true
cp /root/flow_versions.txt "$RES/versions.txt" 2>/dev/null || true
echo "$(date -u +%Y%m%dT%H%M%SZ) $TAG rc=$rc wall_s=$((t1-t0))" | tee -a /workspace/results/runs.log
echo "HARDEN_END rc=$rc"
exit $rc
