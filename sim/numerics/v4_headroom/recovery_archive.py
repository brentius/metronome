import pathlib,time,subprocess,json,hashlib,tarfile,os
P=pathlib.Path
out=P('/workspace/archives/v4_phase1_recovery_20261117');out.mkdir(exist_ok=False)
tags=sorted(p.name for p in P('/workspace/results').glob('v4p1_b*'))
while True:
 text=P('/workspace/results/runs.log').read_text()
 pending=[t for t in tags if not any(t+' rc=' in l for l in text.splitlines())]
 print(time.strftime('%FT%TZ',time.gmtime()),'pending',pending,flush=True)
 if not pending:break
 time.sleep(45)
for t in tags:subprocess.run(['python3','/workspace/jsc/collect_recovery.py',t],stdout=open(out/(t+'.collect.log'),'w'),stderr=subprocess.STDOUT)
roots=list(P('/root/work').glob('v4*'))+list(P('/workspace/results').glob('v4p1*'))+list(P('/workspace/jsc/upload').glob('v4p1*'))+list(P('/workspace/jobs').glob('v4p1*'))+list(P('/workspace/jsc').glob('*v4*'))
roots += [P('/workspace/results/runs.log')]
files={str(f):f for r in roots for f in ([r] if r.is_file() else r.rglob('*')) if f.is_file()}
manifest={k.lstrip('/'): {'size':f.stat().st_size,'sha256':hashlib.file_digest(open(f,'rb'),'sha256').hexdigest()} for k,f in sorted(files.items())}
(out/'manifest.json').write_text(json.dumps(manifest,indent=1))
a=out/'all_native.tgz'
with tarfile.open(a,'w:gz',compresslevel=3) as tar:
 for k,f in sorted(files.items()):tar.add(f,arcname=k.lstrip('/'),recursive=False)
with tarfile.open(a) as tar:
 for m in tar:
  if m.isfile():assert hashlib.file_digest(tar.extractfile(m),'sha256').hexdigest()==manifest[m.name]['sha256']
record={'archive':str(a),'bytes':a.stat().st_size,'sha256':hashlib.file_digest(open(a,'rb'),'sha256').hexdigest(),'verified_members':len(manifest),'roots':[str(r) for r in roots]}
(out/'verification.json').write_text(json.dumps(record,indent=1));print(record,flush=True)
with tarfile.open(out/'results.tgz','w:gz') as tar:
 for r in P('/workspace/results').glob('v4p1*'):tar.add(r,arcname=r.name)
print('DONE',flush=True)
