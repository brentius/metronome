"""Check the template testbench against saved v1 gates, not the new CI layout.

Pinned IHP-Open-PDK 89d42ee6 standard-cell models must be downloaded into
code/.build/template_gl_models/. SRAM models come from test/sram_model/.
Only the old netlist's top-module name is changed, in an ignored build copy.
"""
from pathlib import Path
import hashlib
import json

from cocotb_tools.runner import get_results, get_runner

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BUILD = ROOT / "code/.build/template_saved_v1_gl"
MODELS = ROOT / "code/.build/template_gl_models"
BUILD.mkdir(parents=True, exist_ok=True)
original = ROOT / "data/raw/metronome_v1.0/gds/tt_um_metronome.nl.v"
netlist = BUILD / "tt_um_brentius_metronome.nl.v"
netlist.write_text(original.read_text().replace("module tt_um_metronome (", "module tt_um_brentius_metronome ("))
sources = [MODELS / n for n in ("sg13cmos5l_udp.v", "sg13cmos5l_stdcell.v")]
sources += sorted((ROOT / "test/sram_model").glob("*.v"))
sources += [netlist, ROOT / "test/tb.v"]
manifest = {
    "kind": "zero-delay saved-v1 gate simulation; template testbench validation only",
    "pdk_revision": "89d42ee6d2fd9b50b86a1aada6fee6673c3e6008",
    "model_repository": "https://github.com/IHP-GmbH/IHP-Open-PDK",
    "original_netlist": str(original.relative_to(ROOT)),
    "original_netlist_sha256": hashlib.sha256(original.read_bytes()).hexdigest(),
    "inputs": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
}
(HERE / "saved_v1_gl_inputs.json").write_text(json.dumps(manifest, indent=2) + "\n")
runner = get_runner("icarus")
runner.build(sources=sources, hdl_toplevel="tb", build_dir=BUILD,
             defines={"FUNCTIONAL": 1, "SIM": 1, "GL_TEST": 1},
             timescale=("1ns", "1ps"), always=True)
result = runner.test(hdl_toplevel="tb", test_module="test", test_dir=ROOT / "test",
                     build_dir=BUILD, results_xml=str(HERE / "saved_v1_gl_smoke.xml"))
assert get_results(result) == (1, 0), "saved v1 GL smoke failed"
