import pathlib,json,datetime,glob
print('UTC',datetime.datetime.now(datetime.timezone.utc).isoformat())
for v in ['e1_grtadj015','e2_dens45']:
 p=pathlib.Path('/root/work/metronome_r2/runs')/v
 print('RUN',v)
 for f in sorted(p.glob('*globalrouting*/*.log')):
  t=f.read_text(errors='replace');i=t.rfind('Final congestion report:');print(t[i:i+1800]);print('extra_iterations',t.count('Start extra iteration'),'ndr_disabled',t.count('GRT-0273'))
 for f in sorted(p.glob('*stamidpnr*/or_metrics_out.json'))[-1:]:
  d=json.loads(f.read_text());print('TIMING',{k:v for k,v in d.items() if any(s in k for s in ['setup__ws','hold__ws','slew_violation','cap_violation'])})
for n in ['/sys/fs/cgroup/cpu.max','/sys/fs/cgroup/memory.max','/sys/fs/cgroup/memory.current']:
 p=pathlib.Path(n);print(n,p.read_text().strip() if p.exists() else 'missing')
base=pathlib.Path(glob.glob('/nix/store/*python3-3.13.13-env/lib/python3.13/site-packages/librelane')[0])
for rel in ['scripts/yosys/synth.tcl','config/flow.py','steps/yosys.py','steps/openroad.py','scripts/openroad/common/grt.tcl']:
 p=base/rel
 if p.exists():
  lines=p.read_text().splitlines();print('SOURCE',str(p))
  keys=['SYNTH_HIERARCHY_MODE','SYNTH_STRATEGY','MAX_CORES','AREA 0','GRT_ALLOW_CONGESTION','RT_MAX_LAYER','GRT_OVERFLOW_ITERS','SYNTH_KEEP_HIERARCHY']
  hits=[i for i,l in enumerate(lines) if any(k in l for k in keys)]
  for i in hits[:18]:print('\n'.join(f'{j+1}: {lines[j]}' for j in range(max(0,i-2),min(len(lines),i+5))))
print('VERSIONS',pathlib.Path('/root/flow_versions.txt').read_text())
