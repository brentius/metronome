import pathlib,json,glob,sys
sys.path.insert(0,'/workspace/jsc/flow');import ll_variant
p=pathlib.Path('/root/work/metronome_r3_d17/runs/pnr_area0');d=ll_variant.gate_summary(p)
print('GRT_SUMMARY',json.dumps(d))
base=pathlib.Path(glob.glob('/nix/store/*python3-3.13.13-env/lib/python3.13/site-packages/librelane')[0])
for key in ['PNR_CORNERS','STA_CORNERS','DEFAULT_CORNER']:
 print('CONFIG_KEY',key);count=0
 for f in base.rglob('*.py'):
  lines=f.read_text(errors='replace').splitlines()
  for i,l in enumerate(lines):
   if key in l:
    print(str(f.relative_to(base)),i+1,'\n'.join(lines[max(0,i-2):i+5]));count+=1
    if count>=5:break
  if count>=5:break
print('ROUTE_TAIL',pathlib.Path('/workspace/jobs/r3_route_area0.log').read_text(errors='replace')[-1100:])
