import pathlib,json,datetime,tarfile,os,signal,glob
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
evidence=pathlib.Path('/workspace/results/r2_gate3_diagnosis_'+stamp);evidence.mkdir()
for v in ['e1_grtadj015','e2_dens45']:
 p=pathlib.Path('/root/work/metronome_r2/runs')/v
 with tarfile.open(evidence/(v+'_text.tgz'),'w:gz') as t:
  for f in sorted(p.rglob('*')):
   if f.is_file() and f.suffix in ['.log','.json','.rpt','.sdc','.tcl'] and f.stat().st_size<20000000:t.add(f,arcname=str(f.relative_to(p)))
 print('ARCHIVED',v,(evidence/(v+'_text.tgz')).stat().st_size)
for f in pathlib.Path('/proc').glob('[0-9]*/cmdline'):
 try:
  raw=f.read_bytes();parts=raw.split(bytes([0]));cmd=raw.replace(bytes([0]),b' ').decode(errors='replace')
  if parts and parts[0].decode(errors='replace').endswith('/openroad') and any('/root/work/metronome_r2/runs/'+v+'/' in cmd for v in ['e1_grtadj015','e2_dens45']):
   pid=int(f.parent.name);(evidence/('stopped_'+str(pid)+'.txt')).write_text(cmd);os.kill(pid,signal.SIGTERM);print('STOPPED_SUPERSEDED_ROUTER',pid)
 except (FileNotFoundError,ProcessLookupError):pass
base=pathlib.Path(glob.glob('/nix/store/*python3-3.13.13-env/lib/python3.13/site-packages/librelane')[0])
for key in ['MAX_CORES','SYNTH_STRATEGY','SYNTH_HIERARCHY_MODE']:
 print('CONFIG_KEY',key);count=0
 for p in base.rglob('*'):
  if p.suffix not in ['.py','.tcl']:continue
  try:lines=p.read_text().splitlines()
  except Exception:continue
  for i,l in enumerate(lines):
   if key in l:
    print(str(p.relative_to(base)),i+1,'\n'.join(lines[max(0,i-2):i+5]));count+=1
    if count>=8:break
  if count>=8:break
for n in ['/sys/fs/cgroup/cpu/cpu.cfs_quota_us','/sys/fs/cgroup/cpu/cpu.cfs_period_us','/sys/fs/cgroup/memory/memory.limit_in_bytes']:
 p=pathlib.Path(n);print(n,p.read_text().strip() if p.exists() else 'missing')
print('REMOTE_EVIDENCE',evidence)
