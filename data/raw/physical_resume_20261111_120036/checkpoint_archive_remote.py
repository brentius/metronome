import pathlib,json,tarfile,hashlib,datetime,io
base=pathlib.Path('/root/work/metronome_r3_d17').resolve();selected=['repaired_grt/01-openroad-globalrouting','repair_grt_area0/01-openroad-resizertimingpostgrt','pnr_area0/28-openroad-globalrouting','map_area0/12-openroad-staprepnr']
files=set()
def include(f):
 f=pathlib.Path(f)
 if f.is_file() and f.resolve().is_relative_to(base):files.add(f.resolve())
def refs(x):
 if isinstance(x,dict):
  for k,v in x.items():
   if k!='metrics':refs(v)
 elif isinstance(x,list):
  for v in x:refs(v)
 elif isinstance(x,str) and x.startswith(str(base)):include(x)
for tag in selected:
 step=base/'runs'/tag
 for name in ['state_out.json','state_in.json','config.json','or_metrics_out.json','COMMANDS']:
  f=step/name;include(f)
  if name=='state_out.json':refs(json.loads(f.read_text()))
for f in (base/'src').rglob('*'):include(f)
for name in ['info.yaml','source_manifest.json','librelane_plugin_sram_pdn.py','odb_stripes.py']:include(base/name)
manifest={'restore_under':str(base),'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'selected_states':selected,'files':[]}
for f in sorted(files):manifest['files'].append({'path':str(f.relative_to(base)),'bytes':f.stat().st_size,'sha256':hashlib.sha256(f.read_bytes()).hexdigest()})
out=pathlib.Path('/workspace/results/metronome_r3_d17_checkpoint_grt_repaired.tgz');assert not out.exists(),out
with tarfile.open(out,'w:gz') as tar:
 for f in sorted(files):tar.add(f,arcname=str(f.relative_to(base)))
 b=(json.dumps(manifest,indent=2)+'\n').encode();t=tarfile.TarInfo('checkpoint_manifest.json');t.size=len(b);tar.addfile(t,io.BytesIO(b))
print('CHECKPOINT_ARCHIVE',out,'bytes',out.stat().st_size,'files',len(files))
print('ROUTE_TAIL',pathlib.Path('/workspace/jobs/r3_route_repaired12.log').read_text(errors='replace')[-1100:])
