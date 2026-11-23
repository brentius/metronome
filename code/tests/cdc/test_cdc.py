"""CDC verification for Metronome: structural audit (Yosys) + metastability-injection simulation (cocotb).

    source code/tools/env.sh
    python -m pytest code/tests/cdc -q

Tests
    test_structural_audit          every raw input -> one first-stage flop only; s1 -> s2 -> sp; rst_n only to the
                                   reset synchroniser; no combinational raw-input path to any output (audit_cdc.py)
    test_audit_fail_closed         an unclassified cell type raises instead of being skipped
    test_mutation[...]             planted raw-input / s1 / rst_n uses on a *copy* of src/ must be caught
    test_negative_control          a two-cycle late resolution on the host link must change the decoded result
    test_cdc_jitter[...]           each protocol scenario on the RTL, one clean pass + CDC_SEEDS jittered passes

Environment
    CDC_SEEDS=1,2                  jitter seeds (one pass each, plus the clean pass)
    CDC_JITTER=0.5                 probability that an input edge is resolved one cycle late
    CDC_JITTER_DEPTH=1             cycles added by a late resolution; the negative control uses 2
    CDC_SCENARIOS=spi_host,...     subset of scenarios_cdc.BUILDERS
    CDC_EXTENDED=1                 add the v4 UART training/retransmission/reply scenarios
    CDC_GL_NETLIST / CDC_STDCELL_DIR / CDC_GL_TOP   run the same bench on a routed netlist (see cdc_sim.py)
"""
from __future__ import annotations

import os
import shutil
import sys
from pathlib import Path

import pytest

import _tools

_tools.ensure_tools()

import audit_cdc  # noqa: E402
import cdc_sim  # noqa: E402
from cdc_jitter_tb import Jitter  # noqa: E402
from scenarios_cdc import DEFAULT_SCENARIOS, EXTENDED_SCENARIOS, NEGATIVE_CONTROL  # noqa: E402

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SRC = ROOT / "src"
SEEDS = os.environ.get("CDC_SEEDS", "1,2")
scenario_default = DEFAULT_SCENARIOS + (EXTENDED_SCENARIOS if os.environ.get("CDC_EXTENDED") == "1" else ())
SCENARIOS = [s.strip() for s in os.environ.get("CDC_SCENARIOS", ",".join(scenario_default)).split(",") if s.strip()]

@pytest.fixture(scope="session")
def evidence(tmp_path_factory):
    configured = os.environ.get("CDC_OUTDIR")
    path = Path(configured).resolve() if configured else tmp_path_factory.mktemp("cdc")
    path.mkdir(parents=True, exist_ok=True)
    cdc_sim.environment(path, sys.argv)
    return path


# ==================================================================================================== structural
def test_structural_audit(evidence):
    report = audit_cdc.run_audit(SRC, json_out=evidence / "audit.json")
    (evidence / "structural_audit.txt").write_text(report.text() + "\n", encoding="utf-8")
    assert report.passed, report.text()
    sec = report.sections
    assert any("all 16 raw input bits" in line for line in sec["RAW_FANOUT"]), report.text()
    assert any("rst_n reaches exactly 2 pins" in line for line in sec["RSTN_FANOUT"]), report.text()
    assert any("s1 -> s2" in line for line in sec["SYNC_CHAIN"]), report.text()
    # the async clears of the configuration latches are fed by the synchronised reset, not by rst_n
    assert any("md2_cfg_cells.rst_s: 2112x async_clear cfg_dlhrq_beh" in line for line in sec["RESET_NETS"]), \
        report.text()
    assert any("no combinational path" in line for line in sec["NO_RAW_COMB_PATH"]), report.text()


def test_audit_fail_closed():
    """An unclassified cell type must stop the audit, never be silently ignored."""
    module = audit_cdc.Module("m", {"ports": {}, "cells": {}, "netnames": {}})
    module.known = set()
    with pytest.raises(audit_cdc.AuditError):
        audit_cdc.cell_class(module, "$frobnicate")
    with pytest.raises(audit_cdc.AuditError):
        audit_cdc.cell_class(module, "sg13cmos5l_mystery_1")


def test_gl_config_fail_closed(monkeypatch, tmp_path):
    """A half-configured gate-level run must refuse to start instead of silently simulating the RTL."""
    netlist = tmp_path / "nl.v"
    netlist.write_text("module tt_um_brentius_metronome; endmodule\n", encoding="ascii")
    monkeypatch.setenv("CDC_GL_NETLIST", str(netlist))
    monkeypatch.delenv("CDC_STDCELL_DIR", raising=False)
    with pytest.raises(RuntimeError, match="CDC_STDCELL_DIR"):
        cdc_sim.gl_config()
    cells = tmp_path / "cells"
    monkeypatch.setenv("CDC_STDCELL_DIR", str(cells))
    with pytest.raises(RuntimeError, match="sg13cmos5l_stdcell"):
        cdc_sim.gl_config()
    cells.mkdir()
    (cells / "sg13cmos5l_stdcell.v").write_text("", encoding="ascii")
    with pytest.raises(RuntimeError, match="_udp"):
        cdc_sim.gl_config()
    (cells / "sg13cmos5l_udp.v").write_text("", encoding="ascii")
    assert cdc_sim.gl_config() == (netlist.resolve(), cells.resolve())
    monkeypatch.delenv("CDC_GL_NETLIST", raising=False)
    assert cdc_sim.gl_config() is None


# (file, original text, replacement, check that must fire)
MUTANTS = {
    "raw_input_into_output": (
        "project.v",
        "    assign uio_out = o_out[7:0];",
        "    assign uio_out = o_out[7:0] | {7'd0, ui_in[0]};",
        "RAW_FANOUT"),
    "s1_used_as_synchronised": (
        "project.v",
        "wire [12:0] pins_level = ({s2[15:11], s2[7:0]} & ~replay_mask) | (rlv & replay_mask);",
        "wire [12:0] pins_level = ({s1[15:11], s1[7:0]} & ~replay_mask) | (rlv & replay_mask);",
        "SYNC_CHAIN"),
    "raw_rst_n_into_output": (
        "project.v",
        "    assign uio_oe  = o_oe;",
        "    assign uio_oe  = o_oe | {7'd0, ~rst_n};",
        "RSTN_FANOUT"),
}


@pytest.mark.parametrize("name", sorted(MUTANTS))
def test_mutation(tmp_path, evidence, name):
    """Plant an unsynchronised use on a *copy* of src/ and require the audit to fail with the expected check."""
    work = tmp_path / "src"
    shutil.copytree(SRC, work)
    filename, old, new, check = MUTANTS[name]
    path = work / filename
    text = path.read_text(encoding="utf-8")
    assert text.count(old) == 1, f"mutation {name}: anchor not unique in {filename}"
    path.write_text(text.replace(old, new, 1), encoding="utf-8")
    report = audit_cdc.run_audit(work, json_out=evidence / f"mutation_{name}.json")
    assert not report.passed, f"mutation {name} was not detected:\n{report.text()}"
    assert any(f.check == check for f in report.findings), \
        f"mutation {name}: expected a {check} finding, got {[f.check for f in report.findings]}\n{report.text()}"
    if name == "raw_input_into_output":
        assert any(f.check == "NO_RAW_COMB_PATH" for f in report.findings), report.text()


# ==================================================================================================== simulation
def test_jitter_preserves_consecutive_late_edges():
    jitter = Jitter(seed=1, prob=1, mask=1, rst=False)
    observed = [jitter.step(t, 0, uio, 1)[1] for t, uio in enumerate([0, 1, 0, 0])]
    assert observed == [0, 0, 1, 0]
    assert jitter.edges[0] == jitter.delayed[0] == 2


@pytest.fixture(scope="session")
def built(evidence):
    sim = os.environ.get("CDC_SIM", "icarus")
    tool = "iverilog" if sim == "icarus" else sim
    if not _tools.have(tool):
        pytest.fail(f"needs {tool} (source code/tools/env.sh)")
    return cdc_sim.build(evidence / "sim", always=True)


def test_negative_control(built, evidence):
    """A difference must be detectable: the negative-control scenario must decode *differently* when perturbed.

    `spi_host_fast` writes a sentinel at clk/16, reads it back, overwrites at clk/2 and reads again.  The clean pass
    must produce both values.  With every MOSI edge resolved two cycles late - twice the campaign's one-cycle model,
    chosen so the effect is unambiguous - the clk/2 overwrite is lost (the clk/16 sentinel write survives), so the
    second readback must differ from the control.  Without this, `protocol_results_equal` could pass vacuously.
    """
    out = evidence / f"{NEGATIVE_CONTROL}-negative-control.json"
    fails, summary = cdc_sim.run(NEGATIVE_CONTROL, built, seeds="7", jitter=1.0, out=out,
                                 expect_divergence=True, depth=2)
    assert not fails, f"negative control: {fails}"
    assert summary is not None, f"negative control: no summary written to {out}"
    assert summary["expect_divergence"] is True, summary
    assert summary["jitter_depth_cycles"] == 2, summary
    assert summary["passes"][0]["error"] is None, summary["passes"][0]["error"]
    assert summary["protocol_results_equal"] is False, summary
    assert any(p["error"] or p["result"] != summary["passes"][0]["result"] for p in summary["passes"][1:]), summary


@pytest.mark.parametrize("scenario", SCENARIOS)
def test_cdc_jitter(built, evidence, scenario):
    out = evidence / f"{scenario}.json"
    fails, summary = cdc_sim.run(scenario, built, seeds=SEEDS,
                                 jitter=float(os.environ.get("CDC_JITTER", "0.5")), out=out)
    assert not fails, f"{scenario}: {fails}"
    assert summary is not None, f"{scenario}: no summary written to {out}"
    assert summary["protocol_results_equal"], summary
    assert len(summary["passes"]) == 1 + len([s for s in SEEDS.split(",") if s.strip()])
    for jitter_pass in summary["passes"][1:]:
        assert jitter_pass["edges_delayed"] > 0, f"{scenario}: jitter inactive in {jitter_pass['label']}"
