#!/usr/bin/env python3
"""Run bounded programmable protocol wire demonstrations on v2 RTL or routed gates.

python run_campaign.py --repo . --out NEW_DIRECTORY [--case uart]
Gate mode adds --netlist FILE --cells PDK_STDCELL_DIRECTORY; SDF adds --sdf FILE.
"""
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
import traceback
import xml.etree.ElementTree as ET


def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1<<20),b''): h.update(b)
    return h.hexdigest()


def save(path,data):
    temporary=path.with_suffix('.tmp')
    temporary.write_text(json.dumps(data,indent=2)+'\n')
    temporary.replace(path)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--case',action='append',help='repeat to select cases; default all')
    ap.add_argument('--netlist',type=Path)
    ap.add_argument('--cells',type=Path)
    ap.add_argument('--sdf',type=Path)
    ap.add_argument('--base-revision',help='source baseline; exact uncommitted test inputs are hashed separately')
    a=ap.parse_args()
    repo=a.repo.resolve(); out=a.out.resolve()
    if out.exists(): ap.error(f'refusing existing output directory: {out}')
    if bool(a.netlist)!=bool(a.cells): ap.error('--netlist and --cells must be used together')
    if a.sdf and not a.netlist: ap.error('--sdf requires --netlist and --cells')
    sys.path[:0]=[str(repo/'code/tests/protocol_campaign'),str(repo/'code/tests/lockstep_v2'),
                  str(repo/'code/flow/runpod'),str(repo/'sim/reference')]
    import campaign
    from cocotb_tools.runner import get_runner
    from rtl_sources import SRC,rtl_files
    names=list(campaign.ALL_CASES)
    cases=a.case or names
    unknown=set(cases)-set(names)
    if unknown: ap.error(f'unknown cases {sorted(unknown)}; choose {names}')
    if not cases or len(cases)!=len(set(cases)): ap.error('cases must be nonempty and unique')
    out.mkdir(parents=True); build=out/'build'; build.mkdir()
    metadata={'started_utc':datetime.now(timezone.utc).isoformat(),'mode':'sdf' if a.sdf else 'gates' if a.netlist else 'rtl',
              'clock_period_ps':16667,'sampling_after_rise_ps':8000,'cases':cases,'runs':[],
              'base_revision':a.base_revision,'command_line':sys.argv,
              'input_hashes':{str(p.relative_to(repo)):sha(p) for p in (repo/'code/tests/protocol_campaign').glob('*.py')},
              'sdf_limitations':[]}
    manifest=out/'manifest.json'
    save(manifest,metadata)
    sources,defines=rtl_files(ihp_sram=True)
    top='tt_um_brentius_metronome'; mmap={}; build_args=[]
    try:
        if a.netlist:
            from verify_v2_gates import make_sdf_wrapper,sram_instances,WRAPPER
            netlist=a.netlist.resolve(); cells=a.cells.resolve()
            if not netlist.is_file() or not (cells/'sg13cmos5l_stdcell.v').is_file():
                raise RuntimeError('missing routed netlist or PDK standard cell models')
            metadata.update(netlist=str(netlist),netlist_sha256=sha(netlist),cells=str(cells))
            if os.name=='posix':
                if not shutil.which('stdbuf'): raise RuntimeError('stdbuf required for unbroken SDF diagnostics')
                os.environ['SIM_CMD_PREFIX']='stdbuf -oL -eL'
            for_sim=netlist
            if a.sdf:
                sdf=a.sdf.resolve()
                metadata.update(sdf=str(sdf),sdf_sha256=sha(sdf))
                converter=repo/'sim/numerics/v2_sizing/tt_v2_pnr/test/sdf_for_icarus.py'
                for_sim=build/'netlist_icarus.v'; converted=build/'icarus.sdf'
                proc=subprocess.run([sys.executable,str(converter),str(sdf),str(converted),str(netlist),str(for_sim)],
                                    capture_output=True,text=True)
                (build/'sdf_conversion.log').write_text(proc.stdout+proc.stderr)
                if proc.returncode: raise RuntimeError(f'SDF converter failed rc={proc.returncode}')
                metadata['sdf_limitations']=[
                    'SRAM macro SDF and cell-to-cell INTERCONNECT delays are omitted by the Icarus converter.',
                    'Icarus TIMINGCHECKs are unsupported; annotation diagnostics are counted, not enforced.',
                    'Pins sampled 8 ns after rising edge; this is supplemental functional evidence, not timing signoff.']
                metadata['sdf_conversion']=proc.stdout
            wrapper=build/'netlist_wrapped.v'
            make_sdf_wrapper(for_sim,wrapper,a.sdf)
            mmap=sram_instances(wrapper.read_text())
            sources=sorted((repo/'test/sram_model').glob('*.v'))+sorted(cells.glob('*_udp.v'))+[cells/'sg13cmos5l_stdcell.v',wrapper]
            defines={'FUNCTIONAL':1,'SIM':1,'GL_TEST':1}
            if a.sdf:
                defines['SDF_FILE']='"'+converted.as_posix()+'"'
                build_args=['-gspecify','-ginterconnect']
            top=WRAPPER
        metadata['simulated_source_hashes']={str(p):sha(p) for p in sources}
        metadata['sram_instance_map']=mmap
        save(manifest,metadata)
        runner=get_runner('icarus')
        # Icarus emits thousands of TIMINGCHECK diagnostics at SDF load. Keep
        # line-buffered simulator logging off the network filesystem, then copy
        # the complete original log back after each case, including failures.
        local_logs=Path(tempfile.mkdtemp(prefix='metronome_campaign_logs_'))
        with (out/'build.log').open('x') as log,contextlib.redirect_stdout(log),contextlib.redirect_stderr(log):
            runner.build(sources=sources,hdl_toplevel=top,build_dir=build,includes=[SRC],defines=defines,
                         build_args=build_args,timescale=('1ns','1ps'),always=True,log_file=out/'compile.log')
        for name in cases:
            print(f'START {metadata["mode"]} {name}',flush=True)
            start=time.monotonic(); row={'name':name,'status':'FAIL'}
            xml=out/f'{name}.xml'; simlog=out/f'{name}.sim.log'; runlog=out/f'{name}.runner.log'
            staged_log=local_logs/f'{name}.sim.log'
            try:
                with runlog.open('x') as log,contextlib.redirect_stdout(log),contextlib.redirect_stderr(log):
                    returned=runner.test(hdl_toplevel=top,test_module='campaign_tb',build_dir=build,test_dir=out,
                        results_xml=str(xml),log_file=staged_log,extra_env={
                            'PYTHONPATH':os.pathsep.join([str(repo/'code/tests/protocol_campaign'),str(repo/'sim/reference'),
                                                       str(repo/'code/tests/lockstep_v2'),os.environ.get('PYTHONPATH','')]),
                            'CAMPAIGN_REPO':str(repo),'CAMPAIGN_CASE':name,'CAMPAIGN_OUTPUT':str(out),
                            'CAMPAIGN_SRAM_MAP':json.dumps(mmap)})
                if staged_log.exists(): shutil.copy2(staged_log,simlog)
                if returned and Path(returned).resolve()!=xml.resolve(): shutil.copy2(returned,xml)
                tests=list(ET.parse(xml).getroot().iter('testcase'))
                bad=[e.tag for t in tests for e in t if e.tag in ('failure','error','skipped')]
                output=runlog.read_text(errors='replace')+simlog.read_text(errors='replace')
                errors=re.findall(r'SDF ERROR[^\n]*',output,flags=re.I)
                warnings=[v for v in re.findall(r'SDF WARNING[^\n]*',output,flags=re.I)
                          if 'TIMINGCHECK NOT SUPPORTED' not in v.upper()]
                checks=out/f'{name}.checked.json'
                row.update(testcases=len(tests),bad_test_elements=bad,sdf_errors=errors,sdf_other_warnings=warnings,
                           timingcheck_unsupported_count=len(re.findall('TIMINGCHECK not supported',output,re.I)))
                if len(tests)!=1 or bad or errors or warnings or not checks.is_file():
                    raise AssertionError(f'non-passing XML, annotation diagnostics or missing checker artifact: {row}')
                row['status']='PASS'
            except Exception as exc:
                if staged_log.exists() and not simlog.exists(): shutil.copy2(staged_log,simlog)
                row.update(error=repr(exc),traceback=traceback.format_exc())
            row['wall_seconds']=round(time.monotonic()-start,3)
            metadata['runs'].append(row); save(manifest,metadata)
            print(f'{row["status"]} {name} {row["wall_seconds"]}s',flush=True)
        metadata['status']='PASS' if len(metadata['runs'])==len(cases) and all(r['status']=='PASS' for r in metadata['runs']) else 'FAIL'
    except Exception as exc:
        metadata.update(status='FAIL',error=repr(exc),traceback=traceback.format_exc())
    metadata['finished_utc']=datetime.now(timezone.utc).isoformat()
    save(manifest,metadata)
    summary={'status':metadata['status'],'mode':metadata['mode'],'passed':sum(r['status']=='PASS' for r in metadata['runs']),
             'total':len(cases),'executed':len(metadata['runs']),'sdf_limitations':metadata['sdf_limitations']}
    save(out/'summary.json',summary)
    print(json.dumps(summary),flush=True)
    return 0 if metadata['status']=='PASS' else 1


if __name__=='__main__':
    raise SystemExit(main())
