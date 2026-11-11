#!/bin/bash
set -uo pipefail
source /workspace/jsc/flow/podenv.sh
export _OPENLANE_MAX_CORES=8
BASE=metronome_r3_d17
cd /root/work/$BASE
RES=/workspace/results/${BASE}__map_area0
[ ! -e "$RES/final" ] || { echo "refusing to overwrite mapped views"; exit 2; }
cp -r runs/map_area0/final "$RES/"
cp source_manifest.json info.yaml "$RES/"
cp /root/flow_versions.txt "$RES/versions.txt"
LOCKSTEP_PROBE=0 bash /workspace/jsc/flow/lockstep_pod.sh /workspace/jsc/upload/d17_lockstep_inputs.tgz gl ${BASE}__map_area0 -k 'test_lockstep and (smoke or random_1)'
rc=$?; echo "MAPPED_GL_CHECK rc=$rc"
[ "$rc" -eq 0 ] || exit "$rc"
python3 /workspace/jsc/flow/ll_variant.py "$BASE" pnr_area0 --from OpenROAD.Floorplan --state map_area0/12-openroad-staprepnr --to OpenROAD.GlobalRouting --set 'SYNTH_STRATEGY="AREA 0"' --set GRT_ADJUSTMENT=0.15 --set GRT_ALLOW_CONGESTION=false --set OPENROAD_THREADS=8 --set STA_THREADS=4
