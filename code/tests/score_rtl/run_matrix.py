"""Run independent compiled-Score simulator modes concurrently on a prepared host."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse,json,subprocess,sys

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--rtl-src',type=Path,required=True)
    p.add_argument('--physical',type=Path,required=True,help='qualified final directory with nl/ and sdf/')
    p.add_argument('--cells',type=Path,required=True)
    p.add_argument('--case',action='append')
    p.add_argument('--modes',nargs='+',default=['rtl','gates','typ','slow','fast'])
    a=p.parse_args();a.out.mkdir(parents=True,exist_ok=False)
    assert len(set(a.modes))==len(a.modes) and set(a.modes)<=set(['rtl','gates','typ','slow','fast'])
    netlist=next((a.physical/'nl').glob('*.nl.v'))
    def run(mode):
        command=[sys.executable,str(a.repo/'code/tests/score_rtl/run_score.py'),'--repo',str(a.repo),
                 '--out',str(a.out/mode),'--rtl-src',str(a.rtl_src)]
        for name in a.case or []:command+=['--case',name]
        if mode!='rtl':command+=['--netlist',str(netlist),'--cells',str(a.cells)]
        if mode in ('typ','slow','fast'):
            command+=['--sdf',str(next((a.physical/'sdf').glob('*'+mode+'*/*.sdf')))]
        with (a.out/(mode+'.controller.log')).open('x') as f:
            try:rc=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,timeout=5400).returncode
            except subprocess.TimeoutExpired:rc=124
        result={'mode':mode,'rc':rc,'command':command}
        (a.out/(mode+'.launch.json')).write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result),flush=True)
        return result
    with ThreadPoolExecutor(max_workers=min(5,len(a.modes))) as pool:results=list(pool.map(run,a.modes))
    (a.out/'launches.json').write_text(json.dumps(results,indent=2)+'\n')
    return int(any(r['rc'] for r in results))

if __name__=='__main__':raise SystemExit(main())
