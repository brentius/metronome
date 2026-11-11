import os
from pathlib import Path
import sys
from cocotb_tools.runner import get_runner, get_results

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
os.environ['PATH'] = os.pathsep.join([
    'C:/Users/b_yee23/tools/oss-cad-suite/bin',
    'C:/Users/b_yee23/tools/oss-cad-suite/lib', os.environ['PATH']])
sys.path.insert(0, str(HERE))
r = get_runner('icarus')
b = HERE / 'starvation_pins_build'
r.build(sources=sorted((ROOT / 'code/rtl').glob('*.v')), includes=[ROOT / 'code/rtl/gen'],
        hdl_toplevel='tt_um_metronome', build_dir=b, always=True)
xml = HERE / 'starvation_pins.xml'
r.test(hdl_toplevel='tt_um_metronome', test_module='starvation_pins_tb',
       build_dir=b, test_dir=HERE, results_xml=str(xml))
n, failed = get_results(xml)
assert n == 1 and failed == 0
