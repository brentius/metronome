"""Preflight the SPI-loaded scenarios on the cycle model before RTL runs."""
import argparse
import json
import os
from pathlib import Path
import time
import traceback

ROOT=Path(__file__).resolve().parents[3]
os.environ['SCORE_RTL_REPO']=str(ROOT)
import scenarios_score as scenarios
from score_tb import read_bytes
from metronome2 import Chip


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--case',action='append')
    a=p.parse_args()
    a.out.mkdir(parents=True,exist_ok=False)
    results=[]
    for name in a.case or scenarios.BUILDERS:
        row={'case':name,'status':'FAIL'};start=time.monotonic()
        try:
            s=scenarios.build(name);chip=Chip();trace=[];inputs=[];frames=[];previous=(0,0,0)
            for t,(ui,hi,uio,rst) in enumerate(s.steps):
                uio=uio(t,previous) if callable(uio) else uio
                hi=hi(t,previous) if callable(hi) else hi
                ui=(ui&7)|(hi&248)
                previous=tuple(chip.step(ui,uio&255,rst))
                trace.append(previous);inputs.append(uio&255);frames.append(ui)
            for read in s.read_expectations:
                b,e=read['start'],read['end']
                actual=read_bytes(frames[b:e],trace[b:e],len(read['data']))
                assert actual==bytes(read['data']),(hex(read['addr']),actual,read['data'])
            row.update(status='PASS',cycles=len(s.steps),checks=scenarios.validate(s,trace,inputs,chip))
            (a.out/(name+'.image.json')).write_text(json.dumps(s.compiled.image,indent=2)+'\n')
        except Exception:
            row['error']=traceback.format_exc()
        row['wall_seconds']=time.monotonic()-start
        results.append(row)
        (a.out/(name+'.json')).write_text(json.dumps(row,indent=2,default=str)+'\n')
        print(name,row['status'],round(row['wall_seconds'],2),flush=True)
    (a.out/'summary.json').write_text(json.dumps(results,indent=2,default=str)+'\n')
    return int(any(r['status']!='PASS' for r in results))


if __name__=='__main__':raise SystemExit(main())
