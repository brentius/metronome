"""Equivalent of the template's test/Makefile RTL run (SIM=icarus, TOPLEVEL=tb, module test) for a machine without
make: PROJECT_SOURCES and SRAM_MODEL from test/Makefile, defines FUNCTIONAL SIM USE_IHP_SRAM, include src."""
import re, sys
from pathlib import Path
from cocotb_tools.runner import get_runner
root = Path(sys.argv[1]).resolve()
mk = (root / "test/Makefile").read_text()
srcs = re.search(r"^PROJECT_SOURCES = (.*)$", mk, re.M).group(1).split()
model = [root / "test" / p.replace("$(PWD)/", "") for p in re.search(r"^SRAM_MODEL = (.*)$", mk, re.M).group(1).split()]
r = get_runner("icarus")
r.build(sources=model + [root / "src" / s for s in srcs] + [root / "test/tb.v"], hdl_toplevel="tb",
        includes=[root / "src"], defines={"FUNCTIONAL": 1, "SIM": 1, "USE_IHP_SRAM": 1},
        build_dir=root / "test/sim_build/rtl", timescale=("1ns", "1ps"), always=True)
r.test(hdl_toplevel="tb", test_module="test", test_dir=root / "test", build_dir=root / "test/sim_build/rtl",
       results_xml=str(root / "test/results.xml"))
