"""Run compiled Score images on RTL, optionally the qualified routed netlist/SDF."""
from __future__ import annotations
import argparse
import contextlib
from datetime import datetime,timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import xml.etree.ElementTree as ET


def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def save(path,data):
    tmp=path.with_suffix('.tmp');tmp.write_text(json.dumps(data,indent=2)+'\n');tmp.replace(path)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[3])
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--case',action='append')
    p.add_argument('--rtl-src',type=Path,help='explicit frozen RTL directory; default repo/src')
    p.add_argument('--netlist',type=Path);p.add_argument('--cells',type=Path);p.add_argument('--sdf',type=Path)
    a=p.parse_args();repo=a.repo.resolve();out=a.out.resolve()
    if out.exists():p.error('refusing existing output directory')
    if bool(a.netlist)!=bool(a.cells) or a.sdf and not a.netlist:p.error('gate mode requires --netlist --cells; SDF needs gates')
    os.environ['SCORE_RTL_REPO']=str(repo)
    if a.rtl_src:os.environ['RTL_V2_SRC']=str(a.rtl_src.resolve())
    sys.path[:0]=[str(repo/'code/tests/score_rtl'),str(repo/'code/tests/lockstep_v2'),str(repo/'code/flow/runpod')]
    import scenarios_score
    from rtl_sources import rtl_files,SRC
    from cocotb_tools.runner import get_runner
    cases=a.case or list(scenarios_score.BUILDERS)
    assert cases and len(set(cases))==len(cases) and all(c in scenarios_score.BUILDERS for c in cases)
    out.mkdir(parents=True);build=out/'build';build.mkdir()
    mode='sdf' if a.sdf else 'gates' if a.netlist else 'rtl'
    inputs={}
    for prefix in ('code/tests/score_rtl','code/score','code/scorec','code/host2/metronome2_tools','code/md2',
                   'sim/reference','code/tests/scorec','code/tests/checkers'):
        for f in (repo/prefix).rglob('*'):
            if f.is_file() and f.suffix in ('.py','.json','.score') and '__pycache__' not in f.parts:
                inputs[str(f.relative_to(repo))]=sha(f)
    metadata={'started':datetime.now(timezone.utc).isoformat(),'mode':mode,'cases':cases,'runs':[],
              'input_hashes':inputs,'clock_period_ps':16667,'source_clock_hz_nominal':60000000,
              'limitations':[],'command':sys.argv}
    manifest=out/'manifest.json';save(manifest,metadata)
    sources,defines=rtl_files(ihp_sram=True);top='tt_um_brentius_metronome';mmap={};args=[]
    try:
        if a.netlist:
            from verify_v2_gates import make_sdf_wrapper,sram_instances,WRAPPER
            cells=a.cells.resolve();net=a.netlist.resolve();for_sim=net
            defines={'FUNCTIONAL':1,'SIM':1,'GL_TEST':1}
            metadata['netlist_sha256']=sha(net)
            if a.sdf:
                sdf=a.sdf.resolve();conv=repo/'sim/numerics/v2_sizing/tt_v2_pnr/test/sdf_for_icarus.py'
                converted=build/'icarus.sdf';for_sim=build/'netlist_icarus.v'
                r=subprocess.run([sys.executable,str(conv),str(sdf),str(converted),str(net),str(for_sim)],capture_output=True,text=True)
                (build/'sdf_conversion.log').write_text(r.stdout+r.stderr)
                if r.returncode:raise RuntimeError('SDF conversion failed')
                defines['SDF_FILE']='"'+converted.as_posix()+'"';args=['-gspecify','-ginterconnect']
                metadata['sdf_sha256']=sha(sdf)
                metadata['limitations']=['SRAM macro/interconnect SDF omitted; TIMINGCHECK unsupported; pins sampled8ns afteredge, nottimingsignoff']
            wrapper=build/'wrapped.v';make_sdf_wrapper(for_sim,wrapper,a.sdf)
            mmap=sram_instances(wrapper.read_text())
            sources=sorted((repo/'test/sram_model').glob('*.v'))+sorted(cells.glob('*_udp.v'))+[cells/'sg13cmos5l_stdcell.v',wrapper]
            top=WRAPPER
            if os.name=='posix':os.environ['SIM_CMD_PREFIX']='stdbuf -oL -eL'
        metadata['hdl_hashes']={str(f):sha(f) for f in sources};save(manifest,metadata)
        runner=get_runner('icarus');local=Path(tempfile.mkdtemp(prefix='score_sim_'))
        with (out/'build.log').open('x') as log,contextlib.redirect_stdout(log),contextlib.redirect_stderr(log):
            runner.build(sources=sources,hdl_toplevel=top,build_dir=build,includes=[SRC],defines=defines,
                         build_args=args,timescale=('1ns','1ps'),always=True,log_file=out/'compile.log')
        for name in cases:
            start=time.monotonic();row={'case':name,'status':'FAIL'};xml=out/(name+'.xml');sim=local/(name+'.log')
            print('START',mode,name,flush=True)
            try:
                with (out/(name+'.runner.log')).open('x') as log,contextlib.redirect_stdout(log),contextlib.redirect_stderr(log):
                    runner.test(hdl_toplevel=top,test_module='score_tb',build_dir=build,test_dir=out,results_xml=str(xml),
                                log_file=sim,extra_env={'SCORE_RTL_REPO':str(repo),'SCORE_OUTPUT':str(out),'SCORE_CASE':name,
                                  'SCORE_SRAM_MAP':json.dumps(mmap),'PYTHONPATH':os.pathsep.join([str(repo/'code/tests/score_rtl'),os.environ.get('PYTHONPATH','')])})
                cases_xml=list(ET.parse(xml).getroot().iter('testcase'))
                assert len(cases_xml)==1 and not any(c.tag in ('failure','error','skipped') for t in cases_xml for c in t),'failing/missing/skipped XML'
                logtext=sim.read_text(errors='replace')
                errors=re.findall(r'SDF ERROR[^\n]*',logtext,re.I)
                warnings=[w for w in re.findall(r'SDF WARNING[^\n]*',logtext,re.I) if 'TIMINGCHECK NOT SUPPORTED' not in w.upper()]
                assert not errors and not warnings,(errors,warnings)
                assert (out/(name+'.checked.json')).is_file(),'missing independent check artifact'
                row.update(status='PASS',testcases=1,unsupported_timingchecks=len(re.findall('TIMINGCHECK not supported',logtext,re.I)))
            except Exception as exc:row['error']=repr(exc)
            finally:
                if sim.exists():shutil.copy2(sim,out/(name+'.sim.log'))
            row['wall_seconds']=time.monotonic()-start;metadata['runs'].append(row);save(manifest,metadata)
            print(row['status'],name,round(row['wall_seconds'],2),flush=True)
        metadata['status']='PASS' if all(r['status']=='PASS' for r in metadata['runs']) else 'FAIL'
    except Exception as exc:metadata.update(status='FAIL',error=repr(exc))
    current={str(repo/name):sha(repo/name) for name in inputs}
    changed=[name for name,wanted in inputs.items() if current[str(repo/name)]!=wanted]
    metadata['changed_inputs_during_run']=changed
    if changed:metadata['status']='FAIL'
    metadata['finished']=datetime.now(timezone.utc).isoformat();save(manifest,metadata)
    save(out/'summary.json',{'status':metadata['status'],'passed':sum(r['status']=='PASS' for r in metadata['runs']),
                             'total':len(cases),'mode':mode,'changed_inputs':changed})
    print(metadata['status'],out,flush=True)
    return int(metadata['status']!='PASS')


if __name__=='__main__':raise SystemExit(main())
