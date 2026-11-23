"""Icarus entry points for the reset and power-up campaign.

    python -m pytest code/tests/xinit -q                       # RTL, default campaign
    XINIT_SEEDS=8 XINIT_LOCKSTEP_SEEDS=8 python -m pytest code/tests/xinit -q   # heavier
    XINIT_NETLIST=/path/netlist.v XINIT_STDCELL_DIR=/path/verilog python -m pytest code/tests/xinit -q

Gate mode replaces every RTL case with the pin-only variants: flop deposits need RTL hierarchy, so a routed netlist
runs X-init (all storage X) plus random SRAM contents (the only non-reset storage the bench can still reach).
"""
import json
import os
import sys
from pathlib import Path

import pytest
from cocotb_tools.runner import get_results, get_runner

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path[:0] = [str(HERE), str(ROOT / "code/tests/lockstep_v2")]

from inventory_flops import classify, storage_paths, yosys_json
from rtl_sources import SRC, SRAM_MODEL, rtl_files

TOP = "tt_um_brentius_metronome"
NETLIST = os.environ.get("XINIT_NETLIST")
STDCELL = os.environ.get("XINIT_STDCELL_DIR")
GATE = bool(NETLIST or STDCELL)
SEEDS = int(os.environ.get("XINIT_SEEDS", "3"))
LOCKSTEP_SEEDS = int(os.environ.get("XINIT_LOCKSTEP_SEEDS", "2"))
assert SEEDS >= 1 and LOCKSTEP_SEEDS >= 1 and not (bool(NETLIST) != bool(STDCELL)), \
    "set both XINIT_NETLIST and XINIT_STDCELL_DIR"

# Pulse widths in ps at a fixed phase of 1 ns (wholly between rising edges), plus a pulse that straddles a rising edge
# and one that starts after it.  Phase is measured from the falling edge; the next rising edge is at 8 ns.
PULSES = [(16000, 1000), (4000, 1000), (1000, 1000), (100, 1000), (10, 1000), (1, 1000),
          (1000, 7500), (1, 10000)]

RTL_CASES = [
    ("random_flops", "smoke", 1),
    ("random_flops", "spi_target", 2),
    ("random_flops", "v4_config_write", 3),
    *[("random_flops", f"random_{seed}", seed) for seed in range(1, LOCKSTEP_SEEDS + 1)],
    *[("random_all", "xinit_load_run", seed) for seed in range(1, SEEDS + 1)],
    ("random_sram", "xinit_load_run", 1),
    ("random_all", "xinit_load_read", 1),
    ("random_all", "xinit_reset_only", 1),
    ("random_all", "xinit_mid_reset", 7),
    *[("random_all", f"xinit_pulse_{width}_{phase}", 7) for width, phase in PULSES],
]
X_CASES = [("x_check", name, 0) for name in
           ("xinit_reset_only", "xinit_load_run", "xinit_load_read")]
GATE_CASES = X_CASES + [("random_sram", "xinit_load_run", 1), ("random_sram", "xinit_load_read", 1)]
CASES = GATE_CASES if GATE else RTL_CASES + X_CASES + [("x_probe", "xinit_read_probe", 0)]
# Diagnostics: XINIT_CASES="mode:scenario:seed,mode:scenario:seed" adds cases (e.g. a single seed or a
# bisection run with XINIT_PATHS).  Not used by the default campaign.
for _case in filter(None, os.environ.get("XINIT_CASES", "").split(",")):
    _mode, _scenario, _seed = _case.split(":")
    CASES.append((_mode, _scenario, int(_seed)))


@pytest.fixture(scope="session")
def inventory(tmp_path_factory):
    # Yosys is launched at the repo root with relative source paths.
    raw = tmp_path_factory.mktemp("inventory") / "design.json"
    design = yosys_json(raw)
    result = classify(design)
    paths, fallbacks = storage_paths(design)
    assert not fallbacks, fallbacks[:10]
    return result, paths


@pytest.mark.skipif(GATE, reason="RTL inventory is checked in the RTL suite")
def test_inventory(inventory):
    inv, paths = inventory
    snapshot = json.loads((HERE / "inventory.json").read_text(encoding="utf-8"))
    assert {key: inv[key] for key in inv if key != "no_reset"} == {
        key: snapshot[key] for key in inv if key != "no_reset"
    }
    # Yosys can assign different generated cell IDs to otherwise identical slices.
    def sites(report):
        return sorted(json.dumps({k: v for k, v in site.items() if k != "cell"}, sort_keys=True)
                      for site in report["no_reset"])

    assert sites(inv) == sites(snapshot)
    assert paths == snapshot["storage_paths"]
    assert paths == json.loads((HERE / "storage_paths.json").read_text(encoding="utf-8"))


CORE_MODEL = SRAM_MODEL[2]
# A flattened netlist's SRAM array is not reachable through Icarus VPI (the escaped instance name is discoverable,
# its internals are not).  Gate mode therefore compiles a copy of the core model that can fill itself at time 0; the
# fill is selected per run with a plusarg so the same binary serves the X-init and random-SRAM cases.
RANDOM_INIT = """
// ---- xinit: optional power-up randomisation of this macro's words (gate-level random-SRAM variant)
integer xinit_i;
integer xinit_seed;
initial begin
    xinit_seed = 32'h5eed_0000 ^ (P_DATA_WIDTH * 31 + P_ADDR_WIDTH);
    if ($test$plusargs("xinit_random_sram")) begin
        for (xinit_i = 0; xinit_i < (1 << P_ADDR_WIDTH); xinit_i = xinit_i + 1)
            memory[xinit_i] = $random(xinit_seed);
        $display("xinit: randomised %0d SRAM words at power-up", (1 << P_ADDR_WIDTH));
    end
end
"""


@pytest.fixture(scope="session")
def simulator(tmp_path_factory):
    if GATE:
        pdk = Path(STDCELL).resolve()
        build = tmp_path_factory.mktemp("xinit_gl")
        text = CORE_MODEL.read_text(encoding="utf-8").rstrip()
        assert text.endswith("endmodule"), CORE_MODEL
        random_core = build / "RM_IHPSG13_1P_core_behavioral_bm_bist_random.v"
        random_core.write_text(text[:-len("endmodule")] + RANDOM_INIT + "endmodule\n", encoding="utf-8")
        files = [SRAM_MODEL[0], SRAM_MODEL[1], random_core, *sorted(pdk.glob("*_udp.v")),
                 pdk / "sg13cmos5l_stdcell.v", Path(NETLIST).resolve()]
        defines = {"FUNCTIONAL": 1, "SIM": 1, "GL_TEST": 1}
        includes = [pdk]
    else:
        build = tmp_path_factory.mktemp("xinit_rtl")
        files, defines = rtl_files(ihp_sram=True)
        includes = [SRC]
    missing = [str(path) for path in files if not path.is_file()]
    assert not missing, f"missing Verilog sources: {missing}"
    runner = get_runner("icarus")
    runner.build(sources=files, hdl_toplevel=TOP, build_dir=build, includes=includes,
                 defines=defines, timescale=("1ns", "1ps"), always=True)
    return runner, build


@pytest.mark.parametrize("mode,scenario,seed", CASES)
def test_powerup(simulator, mode, scenario, seed):
    runner, build = simulator
    stem = f"{mode}-{scenario}-{seed}"
    result_dir = Path(os.environ.get("XINIT_RESULTS_DIR", build)).resolve()
    result_dir.mkdir(parents=True, exist_ok=True)
    xml = result_dir / f"{stem}.xml"
    result = result_dir / f"{stem}.json"
    result.unlink(missing_ok=True)
    paths = os.environ.get("XINIT_PATHS", str(HERE / "storage_paths.json"))
    env = {"XINIT_MODE": mode, "XINIT_SCENARIO": scenario, "XINIT_SEED": str(seed),
           "XINIT_RESULT": str(result), "XINIT_PATHS": paths,
           "XINIT_GATE": str(int(GATE))}
    # The runner chooses its import path from sys.path, and names its XML from
    # PYTEST_CURRENT_TEST when called inside pytest.
    plusargs = ["+xinit_random_sram"] if mode == "random_sram" else []
    xml = runner.test(hdl_toplevel=TOP, test_module="xinit_tb", build_dir=build,
                      test_dir=build, extra_env=env, plusargs=plusargs, results_xml=str(xml))
    assert get_results(xml) == (1, 0), f"simulation failed, see {result}"
    assert result.is_file(), f"missing simulation evidence: {result}"
