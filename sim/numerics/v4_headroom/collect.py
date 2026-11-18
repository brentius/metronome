"""Summarise one TT harden run for the v4 Phase 1 headroom table (runs on the pod; python3, stdlib only).

    python3 collect.py TAG            -> /workspace/results/TAG/v4p1_summary.json (+ prints it)

Reads the LibreLane run directory /root/work/TAG/runs/wokwi (container disk) and the result dir. Per stage: std-cell
area, count and utilisation (or_metrics_out.json); GRT final congestion table; detailed-route DRC count; post-PnR
extracted setup/hold worst slack per corner (same metric parse as verify_v2_pipeline.physical_result); LVS; harden rc.
"""
import json
import re
import sys
from pathlib import Path

tag = sys.argv[1]
run = Path("/root/work") / tag / "runs/wokwi"
res = Path("/workspace/results") / tag
out = {"tag": tag, "run": str(run)}
log = res / "harden.log"
txt = log.read_text(errors="replace") if log.exists() else ""
m = re.findall(r"^\S* ?%s rc=(\d+) wall_s=(\d+)" % re.escape(tag), (Path("/workspace/results/runs.log").read_text()), re.M)
if m:
    out["rc"], out["wall_s"] = int(m[-1][0]), int(m[-1][1])
stages = sorted(p.name for p in run.iterdir() if p.is_dir() and re.match(r"\d+-", p.name)) if run.exists() else []
out["last_stage"] = stages[-1] if stages else None
err = (run / "error.log").read_text(errors="replace")[-3000:] if (run / "error.log").exists() else ""
out["error_log_tail"] = err
area = {}
for s in stages:
    f = run / s / "or_metrics_out.json"
    if f.exists():
        d = json.loads(f.read_text())
        if "design__instance__area__stdcell" in d:
            area[s] = {k: d.get(k) for k in ("design__instance__area__stdcell", "design__instance__count__stdcell",
                                              "design__instance__utilization__stdcell",
                                              "design__instance__area__class:timing_repair_buffer",
                                              "design__instance__area__class:clock_buffer")}
out["area_by_stage"] = area
grt = [s for s in stages if "globalrouting" in s]
if grt:
    g = (run / grt[0] / "openroad-globalrouting.log")
    gt = g.read_text(errors="replace") if g.exists() else ""
    i = gt.rfind("Final congestion report")
    out["grt_congestion"] = gt[i:i + 900] if i >= 0 else gt[-2500:]
drt = [s for s in stages if "detailedrouting" in s]
if drt:
    f = run / drt[0] / "or_metrics_out.json"
    if f.exists():
        d = json.loads(f.read_text())
        out["drt"] = {k: v for k, v in d.items() if k.startswith("route__drc_errors") or k == "route__wirelength"}
values = {}
for lg in sorted(run.glob("*stapostpnr*/*/sta.log")):
    for line in lg.read_text(errors="replace").splitlines():
        mm = re.match(r"%OL_METRIC_F\s+timing__(setup|hold)__ws__corner:(\S+)\s+(\S+)", line)
        if mm and mm.group(2).startswith("nom_"):
            values[f"{mm.group(1)}_{mm.group(2)}"] = float(mm.group(3))
out["sta_postpnr_ws_ns"] = values
fm = run / "final/metrics.json"
if fm.exists():
    d = json.loads(fm.read_text())
    keep = ("design__instance__area__stdcell", "design__instance__utilization__stdcell", "route__drc_errors",
            "design__lvs_error__count", "antenna__violating__nets", "route__wirelength", "global_route__wirelength",
            "design__instance__area__class:timing_repair_buffer", "design__instance__area__class:clock_buffer",
            "design__max_slew_violation__count", "design__max_cap_violation__count", "timing__setup_vio__count",
            "timing__hold_vio__count", "design__instance__count__stdcell", "flow__errors__count")
    out["final"] = {k: d.get(k) for k in keep}
    out["final_ws"] = {k: v for k, v in d.items() if re.match(r"timing__(setup|hold)__ws__corner:nom", k)}
ps = {}
for f in run.glob("*/*.process_stats.json"):
    try:
        d = json.loads(f.read_text())
        ps[f.parent.name] = {"runtime": d["time"]["runtime"], "peak_rss": d["peak_resources"]["memory_rss"]}
    except Exception:
        pass
out["process_stats"] = dict(sorted(ps.items()))
ok_t = len(values) >= 6 and all(v >= 0 for v in values.values())
out["timing_closed_all_corners"] = ok_t
out["pass"] = bool(out.get("rc") == 0 and ok_t and out.get("final", {}).get("route__drc_errors") == 0
                   and out.get("final", {}).get("design__lvs_error__count") == 0)
(res / "v4p1_summary.json").write_text(json.dumps(out, indent=1))
print(json.dumps({k: v for k, v in out.items() if k not in ("process_stats", "error_log_tail")}, indent=1))
print("ERRTAIL", err[-1200:])
