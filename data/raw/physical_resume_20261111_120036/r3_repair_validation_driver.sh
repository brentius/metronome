#!/bin/bash
set -uo pipefail
source /workspace/jsc/flow/podenv.sh
export _OPENLANE_MAX_CORES=4
python3 - <<'PY'
import pathlib,sys,subprocess,json
sys.path.insert(0,'/workspace/jsc/flow');import ll_variant
base=['python3','/workspace/jsc/flow/ll_variant.py','metronome_r3_d17']
common=['--set','SYNTH_STRATEGY="AREA 0"','--set','GRT_ADJUSTMENT=0.15','--set','GRT_ALLOW_CONGESTION=false','--set','OPENROAD_THREADS=4','--set','STA_THREADS=4']
cmd=base+['repaired_grt','--from','OpenROAD.GlobalRouting','--to','OpenROAD.GlobalRouting','--state','repair_grt_area0/01-openroad-resizertimingpostgrt']+common
subprocess.run(cmd,check=True)
run=pathlib.Path('/root/work/metronome_r3_d17/runs/repaired_grt');gate=ll_variant.gate_summary(run)['global_route_gate'];print('REPAIRED_GRT_GATE',json.dumps(gate),flush=True)
if gate['status']!='pass':raise SystemExit(3)
state='repaired_grt/'+next(run.glob('*globalrouting')).name
for name,corner in [('slow','nom_slow_1p08V_125C'),('fast','nom_fast_1p32V_m40C')]:
 cmd=base+['repaired_sta_'+name,'--from','OpenROAD.STAMidPNR','--to','OpenROAD.STAMidPNR','--state',state]+common+['--set','PNR_CORNERS='+json.dumps([corner]),'--set','DEFAULT_CORNER='+json.dumps(corner)]
 subprocess.run(cmd,check=True)
PY
