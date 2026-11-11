"""Separate scratch harness: log simulation progress, with expensive probes disabled."""
import os
from pathlib import Path
import sys
from cocotb_tools.runner import get_runner, get_results

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
os.environ['PATH'] = os.pathsep.join([
    'C:/Users/b_yee23/tools/oss-cad-suite/bin',
    'C:/Users/b_yee23/tools/oss-cad-suite/lib', os.environ['PATH']])
source = (ROOT / 'code/tests/lockstep/lockstep_tb.py').read_text()
source = source.replace('ROOT = Path(__file__).resolve().parents[3]', f'ROOT = Path({str(ROOT)!r})')
needle = '    for t, (ui, uio, rst_n) in enumerate(scen.cycles):\n'
source = source.replace(needle, needle + f'        if t % 10000 == 0:\n            with open({str(HERE / "random_progress.txt")!r}, "a") as f:\n                print(t, flush=True, file=f)\n')
(HERE / 'random_progress_tb.py').write_text(source)
sys.path[:0] = [str(HERE), str(ROOT / 'code/tests/lockstep'), str(ROOT / 'sim/reference'), str(ROOT / 'code/md')]
r = get_runner('icarus')
b = HERE / 'random_progress_build'
r.build(sources=sorted((ROOT / 'code/rtl').glob('*.v')), includes=[ROOT / 'code/rtl/gen'],
        hdl_toplevel='tt_um_metronome', build_dir=b, timescale=('1ns', '1ps'), always=True)
xml = HERE / 'random_progress.xml'
r.test(hdl_toplevel='tt_um_metronome', test_module='random_progress_tb',
       build_dir=b, test_dir=HERE, results_xml=str(xml),
       extra_env={'LOCKSTEP_SCENARIO': 'random_1', 'LOCKSTEP_PROBE': '0'})
n, failed = get_results(xml)
assert n == 1 and failed == 0
