import pathlib,json
for v in ['map_delay4','map_area0']:
 p=pathlib.Path('/root/work/metronome_r3_d17/runs')/v
 print('RUN',v)
 for f in sorted(p.glob('*synthesis/state_out.json')):
  d=json.loads(f.read_text());print('SYNTH_STATE',str(f));print('VIEWS',{k:v for k,v in d.items() if k!='metrics'});print('METRICS',d.get('metrics'))
 for f in sorted(p.glob('*synthesis/*stat*')):print('STAT',str(f),f.read_text(errors='replace')[-2800:])
 for f in sorted(p.glob('*staprepnr/*')):
  if f.is_file() and f.suffix in ['.rpt','.log']:print('STA_FILE',f.name)
 print('FINAL',[(str(f.relative_to(p)),f.stat().st_size) for f in p.glob('final/nl/*')])
print('MAPPING_LOG',pathlib.Path('/workspace/jobs/r3_mapping.log').read_text(errors='replace')[-900:])
