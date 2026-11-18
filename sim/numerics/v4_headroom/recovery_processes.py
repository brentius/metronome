from pathlib import Path
import json,time
rows=[]
for p in Path('/proc').glob('[0-9]*'):
 try:
  cmd=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
  if 'openroad' in cmd or 'tt_tool.py' in cmd:
   s=(p/'stat').read_text().split();rows.append({'pid':p.name,'cmd':cmd[:250],'ticks':int(s[13])+int(s[14]),'state':s[2]})
 except:pass
print(json.dumps(rows,indent=1))
