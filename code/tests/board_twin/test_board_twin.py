"""pytest entry for the board twin: build the full-chip RTL with Icarus and run the loader core against it.

    source code/tools/env.sh
    python -m pytest code/tests/board_twin -q                    # core tests + smoke + sweep + negative + uart_tx
    TWIN_GRID=16:0.05,16:0.95,8:0.5 python -m pytest code/tests/board_twin -q -k sweep   # custom sweep
    TWIN_REBUILD=1 ...                                           # force an Icarus rebuild

The RTL source list and IHP SRAM models come from `code/tests/lockstep_v2/rtl_sources.py` (imported, not copied).
"""
from __future__ import annotations

import json
import os
import shutil
import xml.etree.ElementTree as ET
from pathlib import Path

import pytest

import sweep_table
from rtl_sources import SRC, rtl_files

HERE = Path(__file__).resolve().parent
BUILD = HERE / "sim_build_twin"
GRID = os.environ.get("TWIN_GRID")
RESULTS = Path(os.environ.get("TWIN_RESULTS", str(BUILD / "sweep_results.json")))

#: The four simulator tests need iverilog; `test_sweep_table_in_sw_results` is pure Python and must run anywhere (it is
#: the guard that keeps the documented sweep numbers equal to the last run's JSON).
NEEDS_IVERILOG = pytest.mark.skipif(shutil.which("iverilog") is None,
                                    reason="needs iverilog (source code/tools/env.sh)")


def _build():
    from cocotb_tools.runner import get_runner
    files, defines = rtl_files(ihp_sram=True)
    runner = get_runner("icarus")
    runner.build(sources=files, hdl_toplevel="tt_um_brentius_metronome", build_dir=BUILD, includes=[SRC],
                 defines=defines, timescale=("1ns", "1ps"), always=os.environ.get("TWIN_REBUILD") == "1")
    return runner


def _run_test(testcase, extra_env=None):
    runner = _build()
    xml = BUILD / f"results_{testcase}.xml"
    env = {}
    if extra_env:
        env.update({k: str(v) for k, v in extra_env.items()})
    try:
        runner.test(hdl_toplevel="tt_um_brentius_metronome", test_module="board_twin_tb", build_dir=BUILD,
                    test_dir=HERE, testcase=testcase, extra_env=env, results_xml=str(xml))
    except SystemExit as exc:            # cocotb exits non-zero when a test fails; report it as an assertion
        assert exc.code in (0, None), f"cocotb reported a failure in {testcase} (see {xml})"
    root = ET.parse(xml).getroot()
    fails = root.findall(".//failure") + root.findall(".//error")
    assert not fails, f"{testcase}: {[f.get('message') for f in fails]}"


@NEEDS_IVERILOG
def test_twin_smoke():
    """SPEC-limit SCK (clk/16, worst phase), ID/data-RAM/runtime-register round trips, full status read-back."""
    _run_test("twin_smoke")


@NEEDS_IVERILOG
def test_twin_sweep():
    """SCK period x phase x jitter sweep; every point at or below clk/16 must work, and the report is written."""
    if RESULTS.exists():
        RESULTS.unlink()
    _run_test("twin_sweep", {"TWIN_RESULTS": RESULTS})
    data = json.loads(RESULTS.read_text(encoding="utf-8"))
    rows = data["grid"]
    if GRID is None:
        assert len(rows) >= 16, rows
        assert any(r["period"] >= 16.0 for r in rows) and any(r["period"] < 16.0 for r in rows)
    failing_spec = [(r["period"], r["phase"], r["jitter"], r["problems"]) for r in rows
                    if r["spec_ok"] and not r["pass"]]
    assert not failing_spec, failing_spec
    fastest_ok = min((r["period"] for r in rows if r["pass"]), default=None)
    all_phase_ok = sorted({r["period"] for r in rows
                           if all(x["pass"] for x in rows if x["period"] == r["period"])})
    print("\nsweep: %d points, fastest passing SCK = clk/%s, periods passing at every tested phase = %s"
          % (len(rows), fastest_ok, all_phase_ok))
    for row in rows:
        print("  clk/%-5s phase %.2f jitter %.2f: id=%d read(data,reg)=%d%d write(data,reg)=%d%d mismatch=%d  %s"
              % (row["period"], row["phase"], row["jitter"], row["id_ok"], row["read_data_ok"], row["read_reg_ok"],
                 row["write_data_ok"], row["write_reg_ok"], row["mismatches"], "PASS" if row["pass"] else "FAIL"))


@NEEDS_IVERILOG
def test_twin_negative():
    """Negative controls: a corrupted byte and an over-fast SCK must both be rejected by the same verdict."""
    _run_test("twin_negative")


@NEEDS_IVERILOG
def test_twin_uart_tx():
    """examples/uart_tx.mas loaded by the real loader: O8 must carry the bytes written to HOSTIN."""
    _run_test("twin_uart_tx")


@pytest.mark.skipif(GRID is not None or RESULTS != BUILD / "sweep_results.json",
                    reason="only checks the documented, default-grid sweep")
def test_sweep_table_in_sw_results():
    """SWEEP_RESULTS.md must contain the table rendered from the sweep JSON this run produced.

    The documented numbers are only allowed to be the ones an actual run wrote: if the grid, a verdict or a phase
    changes, this fails until the table in SWEEP_RESULTS.md is regenerated with sweep_table.py.
    """
    if not RESULTS.exists():
        pytest.skip("run test_twin_sweep first (or TWIN_RESULTS points elsewhere)")
    data = json.loads(RESULTS.read_text(encoding="utf-8"))
    document = (HERE / "SWEEP_RESULTS.md").read_text(encoding="utf-8")
    missing = [line for line in sweep_table.table(data["grid"]).splitlines()
               if line.startswith("| clk/") and line not in document]
    assert not missing, "SWEEP_RESULTS.md is stale, regenerate it:\n" + "\n".join(missing[:6])
    summary = sweep_table.summary(data["grid"]).splitlines()
    absent = [line for line in summary if line not in document]
    assert not absent, "SWEEP_RESULTS.md summary is stale:\n" + "\n".join(absent)
