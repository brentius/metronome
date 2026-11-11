"""Inject a known internal mismatch into a COPY of the lockstep test."""
import os
from pathlib import Path
import sys
import xml.etree.ElementTree as ET

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
os.environ['PATH'] = os.pathsep.join([
    'C:/Users/b_yee23/tools/oss-cad-suite/bin',
    'C:/Users/b_yee23/tools/oss-cad-suite/lib', os.environ['PATH']])
source = (ROOT / 'code/tests/lockstep/lockstep_tb.py').read_text()
source = source.replace('ROOT = Path(__file__).resolve().parents[3]', f'ROOT = Path({str(ROOT)!r})')
source = source.replace('st = {}', 'st = {"review.injected_mismatch": (1, 0)}')
(HERE / 'probe_gap_tb.py').write_text(source)
from cocotb_tools.runner import get_runner
runner = get_runner('icarus')
build = HERE / 'probe_build'
runner.build(sources=sorted((ROOT / 'code/rtl').glob('*.v')),
             includes=[ROOT / 'code/rtl/gen'], hdl_toplevel='tt_um_metronome',
             build_dir=build, timescale=('1ns', '1ps'), always=True)
paths = [HERE, ROOT / 'code/tests/lockstep', ROOT / 'sim/reference', ROOT / 'code/md']
sys.path[:0] = list(map(str, paths))
runner.test(hdl_toplevel='tt_um_metronome', test_module='probe_gap_tb',
            build_dir=build, test_dir=HERE, results_xml=str(HERE / 'probe_gap.xml'),
            extra_env={'LOCKSTEP_SCENARIO': 'smoke', 'LOCKSTEP_PROBE': '1',
                       'PYTHONPATH': os.pathsep.join(map(str, paths))})
xml = ET.parse(HERE / 'probe_gap.xml').getroot()
failures = xml.findall('.//failure') + xml.findall('.//error')
print(f'Injected mismatch (1,0) every cycle; XML failures/errors: {len(failures)}')
assert not failures, 'Expected current harness to ignore internal probe mismatches'
