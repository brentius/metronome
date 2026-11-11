#!/bin/bash
set -uo pipefail
source /workspace/jsc/flow/podenv.sh
export _OPENLANE_MAX_CORES=8
python3 - <<'PY'
import pathlib,json,tarfile,datetime,os,signal,subprocess
res=pathlib.Path('/workspace/results');base='metronome_r3_d17'
gate=json.loads((res/(base+'__repaired_grt')/'summary.json').read_text())['global_route_gate'];assert gate['status']=='pass',gate
for suffix,corner in [('slow','nom_slow_1p08V_125C'),('fast','nom_fast_1p32V_m40C')]:
 d=json.loads((res/(base+'__repaired_sta_'+suffix)/'summary.json').read_text())
 assert d['timing__setup__ws__corner:'+corner]>=0 and d['timing__hold__ws__corner:'+corner]>=0,d
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ');archive=res/('r3_superseded_route_'+stamp);archive.mkdir()
p=pathlib.Path('/root/work')/base/'runs/route_area0'
with tarfile.open(archive/'route_area0_text.tgz','w:gz') as t:
 for f in sorted(p.rglob('*')):
  if f.is_file() and f.suffix in ['.log','.json','.rpt','.sdc','.tcl'] and f.stat().st_size<20000000:t.add(f,arcname=str(f.relative_to(p)))
print('ARCHIVED_SUPERSEDED_ROUTE',archive,flush=True)
for f in pathlib.Path('/proc').glob('[0-9]*/cmdline'):
 try:
  raw=f.read_bytes();parts=raw.split(bytes([0]));cmd=raw.replace(bytes([0]),b' ').decode(errors='replace')
  if parts and parts[0].decode(errors='replace').endswith('/openroad') and '/root/work/metronome_r3_d17/runs/route_area0/' in cmd:
   os.kill(int(f.parent.name),signal.SIGTERM);print('STOPPED_SUPERSEDED_BASELINE',f.parent.name,flush=True)
 except (FileNotFoundError,ProcessLookupError):pass
cmd=['python3','/workspace/jsc/flow/ll_variant.py',base,'route_repaired12','--from','OpenROAD.STAMidPNR-3','--state','repaired_grt/01-openroad-globalrouting',
'--set','SYNTH_STRATEGY="AREA 0"','--set','GRT_ADJUSTMENT=0.15','--set','GRT_ALLOW_CONGESTION=false','--set','GRT_RESIZER_SETUP_SLACK_MARGIN=0.1','--set','GRT_RESIZER_HOLD_SLACK_MARGIN=0.1','--set','DRT_OPT_ITERS=12','--set','DRT_SAVE_DRC_REPORT_ITERS=1','--set','OPENROAD_THREADS=8','--set','STA_THREADS=4']
raise SystemExit(subprocess.call(cmd))
PY
