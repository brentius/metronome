#!/bin/bash
set -uo pipefail
source /workspace/jsc/flow/podenv.sh
export _OPENLANE_MAX_CORES=8
python3 /workspace/jsc/flow/ll_variant.py metronome_r3_d17 route_area0 --from OpenROAD.CheckAntennas --state pnr_area0/28-openroad-globalrouting --set 'SYNTH_STRATEGY="AREA 0"' --set GRT_ADJUSTMENT=0.15 --set GRT_ALLOW_CONGESTION=false --set OPENROAD_THREADS=8 --set STA_THREADS=4
