"""Safety properties for unattended verification evidence."""
import importlib.util
import sys
import subprocess
import pytest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[2] / "flow/runpod/verify_v2_pipeline.py"


def load():
    assert SCRIPT.is_file(), "overnight pipeline runner is missing"
    spec = importlib.util.spec_from_file_location("verify_v2_pipeline", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_skipped_or_empty_xml_cannot_pass(tmp_path):
    mod = load()
    xml = tmp_path / "results.xml"
    for body in ('<testsuite/>', '<testsuite><testcase><skipped/></testcase></testsuite>',
                 '<testsuite><testcase><failure/></testcase></testsuite>'):
        xml.write_text(body)
        assert not mod.xml_result(xml)["ok"]
    xml.write_text('<testsuite><testcase name="ran"/></testsuite>')
    assert mod.xml_result(xml)["ok"]
    assert not mod.xml_result(tmp_path / "absent.xml")["ok"]


def test_stage_failure_and_timeout_are_recorded(tmp_path):
    mod = load()
    summary = {"stages": []}
    run = mod.Pipeline(tmp_path, tmp_path, summary, 60)
    result = run.step("bad", [sys.executable, "-c", "raise SystemExit(7)"])
    assert result["returncode"] == 7 and result["status"] == "failed"
    result = run.step("timeout", [sys.executable, "-c", "import time; time.sleep(30)"], timeout=0.1)
    assert result["status"] == "timeout"
    assert (tmp_path / "summary.json").exists()


def test_missing_prerequisite_is_not_a_pass(tmp_path):
    mod = load()
    summary = {"stages": []}
    run = mod.Pipeline(tmp_path, tmp_path, summary, 60)
    run.unavailable("sdf_slow", "no SDF")
    assert summary["stages"][0]["status"] == "unavailable"


def test_pre_route_timing_cannot_qualify_final_physical(tmp_path):
    mod = load()
    early = tmp_path / "05-openroad-stamidpnr/nom_slow_1p08V_125C"
    early.mkdir(parents=True)
    (early / "sta.log").write_text("%OL_METRIC_F timing__setup__ws__corner:nom_slow_1p08V_125C 1.0\n")
    assert not mod.physical_result(tmp_path)["ok"]
    for corner in ("typ", "slow", "fast"):
        stage = tmp_path / f"58-openroad-stapostpnr/nom_{corner}_conditions"
        stage.mkdir(parents=True)
        (stage / "sta.log").write_text("".join(
            f"%OL_METRIC_F timing__{kind}__ws__corner:nom_{corner}_conditions 0.1\n" for kind in ("setup", "hold")))
    assert mod.physical_result(tmp_path)["ok"]


def test_gate_sram_mapping_preserves_actual_escaped_names():
    script = SCRIPT.with_name("verify_v2_gates.py")
    spec = importlib.util.spec_from_file_location("verify_v2_gates", script)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    names = mod.sram_instances("\n".join(
        f"RM_IHPSG13_1P_{size}_c2_bm_bist \\{name}.u_sram ( .A_CLK(clk) );"
        for name, size in (("u_pmem0", "256x64"), ("u_pmem1", "256x64"), ("u_dmem", "512x32"))))
    assert names["u_pmem0"] == "u_pmem0.u_sram"


def test_interruption_terminates_active_subprocess(tmp_path, monkeypatch):
    mod = load()
    real_popen = subprocess.Popen
    children = []
    def popen(*args, **kwargs):
        child = real_popen(*args, **kwargs)
        children.append(child)
        real_wait = child.wait
        def wait_once(timeout=None):
            child.wait = real_wait
            raise KeyboardInterrupt()
        child.wait = wait_once
        return child
    monkeypatch.setattr(mod.subprocess, "Popen", popen)
    run = mod.Pipeline(tmp_path, tmp_path, {"stages": []}, 60)
    try:
        with pytest.raises(KeyboardInterrupt):
            run.step("cancel", [sys.executable, "-c", "import time; time.sleep(30)"])
        assert children[0].poll() is not None, "interruption orphaned the active subprocess"
    finally:
        for child in children:
            if child.poll() is None:
                child.kill()
                child.wait()
