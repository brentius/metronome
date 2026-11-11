"""Keep partial or mixed-stage physical-flow evidence distinguishable from signoff."""
import importlib.util
import json
from pathlib import Path


SPEC = importlib.util.spec_from_file_location(
    "ll_variant", Path(__file__).resolve().parents[2] / "flow/runpod/ll_variant.py"
)
FLOW = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(FLOW)


def test_metrics_identify_their_source_stage(tmp_path):
    early = tmp_path / "05-openroad-stamidpnr"
    late = tmp_path / "06-openroad-detailedrouting"
    early.mkdir()
    late.mkdir()
    setup = "timing__setup__ws__corner:nom_typ_1p20V_25C"
    (early / "or_metrics_out.json").write_text(json.dumps({setup: 6.5}))
    (late / "or_metrics_out.json").write_text(json.dumps({"route__drc_errors": 72}))
    result = FLOW.gate_summary(tmp_path)
    assert result["metric_sources"][setup] == "05-openroad-stamidpnr/or_metrics_out.json"
    assert result["metric_sources"]["route__drc_errors"] == "06-openroad-detailedrouting/or_metrics_out.json"
    assert "timing__setup__ws__corner:nom_slow_1p08V_125C" not in result


def test_synthesis_area_is_available_without_openroad_metrics(tmp_path):
    step = tmp_path / "06-yosys-synthesis"
    step.mkdir()
    (step / "state_out.json").write_text(json.dumps({
        "metrics": {"design__instance__area": 293010.6312, "design__instance_unmapped__count": 0}
    }))
    result = FLOW.gate_summary(tmp_path)
    assert result["design__instance__area"] == 293010.6312
    assert result["metric_sources"]["design__instance__area"] == "06-yosys-synthesis/state_out.json"


def test_final_cumulative_metrics_do_not_reintroduce_inherited_corners(tmp_path):
    step = tmp_path / "27-openroad-stamidpnr"
    step.mkdir()
    typical = "timing__setup__ws__corner:nom_typ_1p20V_25C"
    slow = "timing__setup__ws__corner:nom_slow_1p08V_125C"
    (step / "or_metrics_out.json").write_text(json.dumps({typical: 6.37713}))
    (tmp_path / "final").mkdir()
    # LibreLane carries old pre-PnR corners through resumed state into this file.
    (tmp_path / "final/metrics.json").write_text(json.dumps({typical: 6.37713, slow: -272.955966}))
    result = FLOW.gate_summary(tmp_path)
    assert slow not in result
    assert result["metric_sources"][typical] == "27-openroad-stamidpnr/or_metrics_out.json"


def test_opensta_corner_log_measurements_keep_stage_order_and_violation_counts(tmp_path):
    early = tmp_path / "12-openroad-staprepnr/nom_slow_1p08V_125C"
    late = tmp_path / "27-openroad-stamidpnr"
    early.mkdir(parents=True)
    late.mkdir()
    typical = "timing__setup__ws__corner:nom_typ_1p20V_25C"
    slow = "timing__setup__ws__corner:nom_slow_1p08V_125C"
    slew = "design__max_slew_violation__count__corner:nom_slow_1p08V_125C"
    (early / "sta.log").write_text(
        f"%OL_METRIC_F {slow} -0.14145\n%OL_METRIC_I {slew} 24\n%OL_METRIC_F {typical} -160.399\n"
    )
    (late / "or_metrics_out.json").write_text(json.dumps({typical: 6.37713}))
    result = FLOW.gate_summary(tmp_path)
    assert result[slow] == -0.14145
    assert result[slew] == 24
    assert result[typical] == 6.37713
    assert result["metric_sources"][slow] == "12-openroad-staprepnr/nom_slow_1p08V_125C/sta.log"


def _global_route(tmp_path, overflow, *, ndr=False, complete=True):
    step = tmp_path / "01-openroad-globalrouting"
    step.mkdir()
    log = ("[INFO GRT-0096] Final congestion report:\n"
           "Layer Resource Demand Usage (%) Max H / Max V / Total Overflow\n"
           f"Total 609361 332270 54.53% 7 / 2 / {overflow}\n")
    if ndr:
        log += "[WARNING GRT-0273] Disabled NDR for clock net\n"
    if overflow:
        log += "[WARNING GRT-0115] Global routing finished with congestion.\n"
    (step / "openroad-globalrouting.log").write_text(log)
    if complete:
        (step / "state_out.json").write_text("{}")
    return FLOW.gate_summary(tmp_path)


def test_congested_route_fails_even_when_the_flow_continued(tmp_path):
    gate = _global_route(tmp_path, 612)["global_route_gate"]
    assert gate["status"] == "fail"
    assert gate["overflow"] == 612


def test_zero_overflow_with_stripped_clock_rules_still_fails(tmp_path):
    gate = _global_route(tmp_path, 0, ndr=True)["global_route_gate"]
    assert gate["status"] == "fail"
    assert gate["ndr_disabled"] == 1


def test_completed_zero_overflow_route_passes_only_its_own_gate(tmp_path):
    gate = _global_route(tmp_path, 0)["global_route_gate"]
    assert gate["status"] == "pass"
    assert gate["overflow"] == 0


def test_incomplete_or_absent_route_remains_unknown(tmp_path):
    assert FLOW.gate_summary(tmp_path)["global_route_gate"]["status"] == "unknown"
    assert _global_route(tmp_path, 0, complete=False)["global_route_gate"]["status"] == "unknown"
