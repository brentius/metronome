#!/bin/bash
set -uo pipefail
source /workspace/jsc/flow/podenv.sh
export _OPENLANE_MAX_CORES=8
TAG=metronome_r3_d17
WORK=/root/work/$TAG
[ ! -e "$WORK" ] || { echo "refusing to reuse $WORK"; exit 2; }
mkdir -p "$WORK"
tar -xzf /workspace/jsc/upload/metronome_r3_d17.tgz -C "$WORK"
cd "$WORK"
git init -q .
git add -A
git -c user.email=flow@local -c user.name=flow commit -qm snapshot
ln -s /root/tt tt
/root/ttvenv/bin/python tt/tt_tool.py --create-user-config --pdk ihp-sg13cmos5l || exit $?
python3 /workspace/jsc/flow/ll_variant.py "$TAG" map_delay4 --to OpenROAD.STAPrePNR --set 'SYNTH_STRATEGY="DELAY 4"' --set GRT_ADJUSTMENT=0.15 --set GRT_ALLOW_CONGESTION=false --set OPENROAD_THREADS=8 --set STA_THREADS=4
rc=$?; echo "MAPPING_RESULT delay4 rc=$rc"
python3 /workspace/jsc/flow/ll_variant.py "$TAG" map_area0 --to OpenROAD.STAPrePNR --set 'SYNTH_STRATEGY="AREA 0"' --set GRT_ADJUSTMENT=0.15 --set GRT_ALLOW_CONGESTION=false --set OPENROAD_THREADS=8 --set STA_THREADS=4
rc=$?; echo "MAPPING_RESULT area0 rc=$rc"
