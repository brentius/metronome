#!/bin/bash
set -uo pipefail
source /workspace/jsc/flow/podenv.sh
export _OPENLANE_MAX_CORES=4
python3 - <<'PY'
import pathlib,sys
sys.path.insert(0,'/workspace/jsc/flow');import ll_variant
states=sorted(pathlib.Path('/root/work/metronome_r3_d17/runs/route_area0').glob('*stamidpnr*/state_out.json'))
assert len(states)==1,states
state='route_area0/'+states[0].parent.name
sys.argv=['ll_variant.py','metronome_r3_d17','repair_grt_area0','--from','OpenROAD.ResizerTimingPostGRT','--to','OpenROAD.ResizerTimingPostGRT','--state',state,
'--set','SYNTH_STRATEGY="AREA 0"','--set','RUN_POST_GRT_RESIZER_TIMING=true','--set','GRT_ADJUSTMENT=0.15','--set','GRT_ALLOW_CONGESTION=false',
'--set','GRT_RESIZER_SETUP_SLACK_MARGIN=0.1','--set','GRT_RESIZER_HOLD_SLACK_MARGIN=0.1','--set','OPENROAD_THREADS=4','--set','STA_THREADS=4']
raise SystemExit(ll_variant.main())
PY
