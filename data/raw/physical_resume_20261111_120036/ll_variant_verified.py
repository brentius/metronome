#!/usr/bin/env python3
"""Run a LibreLane variant of an existing TT harden work dir, optionally resuming from a saved step state.

    ll_variant.py BASE VARIANT [--from STEP --state RUNDIR/NN-step] [--to STEP] [--set KEY=JSON ...]

  BASE     work dir name under /root/work (from tt_harden.sh), e.g. metronome_r2
  VARIANT  new run name; runs/VARIANT is created (refuses to reuse one)
  --from/--state  resume: e.g. --from OpenROAD.GlobalRouting --state wokwi/39-openroad-stamidpnr-2
  --set    config override, value parsed as JSON (e.g. --set GRT_ADJUSTMENT=0.15)

Writes src/config_VARIANT.json (base config_merged.json + overrides), runs LibreLane, then gate_summary() of the
run to /workspace/results/BASE__VARIANT/summary.json and a line in /workspace/results/runs.log. The tt_tool
harden command is `python -m librelane --run-tag wokwi --force-run-dir runs/wokwi src/config_merged.json`; this
mirrors it with a different run dir.
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

WORK = Path("/root/work")
RES = Path("/workspace/results")

GATE_KEYS = [
    "design__instance__count", "design__instance__area", "design__instance_unmapped__count",
    "synthesis__check_error__count",
    "design__instance__utilization__stdcell", "design__instance__area__stdcell",
    "global_route__wirelength", "route__drc_errors", "route__wirelength", "route__vias",
    "timing__setup__ws", "timing__hold__ws", "timing__setup__tns", "timing__hold__tns",
    "timing__setup__ws__corner:nom_slow_1p08V_125C", "timing__hold__ws__corner:nom_fast_1p32V_m40C",
    "timing__setup__ws__corner:max_ss_100C_1v60", "antenna__violating__nets", "antenna__violating__pins",
    "magic__drc_error__count", "klayout__drc_error__count", "design__lvs_error__count",
    "design__max_slew_violation__count", "design__max_cap_violation__count",
]


def gate_summary(run: Path) -> dict:
    """Diagnostic metrics with provenance; only completed GRT gets a gate ruling.

    Flat metrics may originate in different stages and do not constitute final
    timing, detailed-route or signoff approval. Missing corners stay missing.
    """
    out: dict = {"metric_sources": {}, "global_route_gate": {"status": "unknown"}}
    # final/metrics.json is cumulative: after checkpoint resume it can contain
    # obsolete timing corners inherited from pre-PnR. Never call those fresh
    # measurements. Native per-step reports provide the measurement provenance.
    files = (list(run.glob("*yosys-synthesis/state_out.json"))
             + list(run.glob("*/or_metrics_out.json")) + list(run.glob("*/*/sta.log")))
    def stage_order(path: Path):
        stage = path.relative_to(run).parts[0]
        number = re.match(r"(\d+)-", stage)
        return (int(number.group(1)) if number else -1, path.as_posix())

    files.sort(key=stage_order)
    for f in files:
        try:
            if f.name == "sta.log":
                # OpenSTA emits measurements to its log instead of OpenROAD's
                # JSON metrics file. Read actual records, not cumulative state.
                d = {}
                with f.open(errors="replace") as log:
                    for line in log:
                        match = re.match(r"%OL_METRIC_([IF])\s+(\S+)\s+(\S+)\s*$", line)
                        if match:
                            kind, name, value = match.groups()
                            d[name] = int(value) if kind == "I" else float(value)
            else:
                d = json.loads(f.read_text())
                if f.name == "state_out.json":
                    d = d["metrics"]
        except Exception:
            continue
        for k, v in d.items():
            if k in GATE_KEYS or k.startswith("timing__setup__ws__corner") or k.startswith("timing__hold__ws__corner") \
                    or k.startswith("global_route__") or k.startswith("route__drc") \
                    or k.startswith(("design__max_slew_violation__count", "design__max_cap_violation__count",
                                     "design__max_fanout_violation__count")):
                out[k] = v
                out["metric_sources"][k] = Path(f).relative_to(run).as_posix()
    steps = sorted(p.name for p in run.iterdir() if p.is_dir() and p.name[:2].isdigit())
    out["last_step"] = steps[-1] if steps else None
    grt = sorted(run.glob("*globalrouting*/*.log"))
    if grt:
        txt = grt[-1].read_text(errors="replace")
        out["grt_extra_iterations"] = txt.count("Start extra iteration")
        out["grt_ndr_disabled"] = txt.count("GRT-0273")
        # The last report matters if OpenROAD attempted several routing passes.
        final = txt.rsplit("Final congestion report:", 1)[-1] if "Final congestion report:" in txt else ""
        total = re.search(r"^\s*Total\s+\d+\s+\d+\s+[\d.]+%\s+\d+\s*/\s*\d+\s*/\s*(\d+)\s*$",
                          final, re.MULTILINE)
        overflow = int(total.group(1)) if total else None
        complete = (grt[-1].parent / "state_out.json").is_file()
        failed = bool(overflow or out["grt_ndr_disabled"] or "GRT-0115" in txt)
        status = "fail" if failed else "pass" if complete and overflow == 0 else "unknown"
        out["global_route_gate"] = {
            "status": status, "overflow": overflow, "step_completed": complete,
            "extra_iterations": out["grt_extra_iterations"], "ndr_disabled": out["grt_ndr_disabled"],
            "evidence_file": grt[-1].relative_to(run).as_posix(),
        }
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("base")
    ap.add_argument("variant")
    ap.add_argument("--from", dest="frm")
    ap.add_argument("--state")
    ap.add_argument("--to")
    ap.add_argument("--set", action="append", default=[])
    a = ap.parse_args()
    wd = WORK / a.base
    run = wd / "runs" / a.variant
    if run.exists():
        print(f"refusing to reuse {run}")
        return 2
    run.mkdir(parents=True)        # LibreLane's --force-run-dir requires an existing directory
    cfg = json.load(open(wd / "src/config_merged.json"))
    over = {}
    for s in a.set:
        k, v = s.split("=", 1)
        over[k] = json.loads(v)
    cfg.update(over)
    cpath = wd / f"src/config_{a.variant}.json"
    json.dump(cfg, open(cpath, "w"), indent=2)
    cmd = [sys.executable if "librelane" in sys.executable else "python3", "-m", "librelane",
           "--pdk-root", os.environ.get("PDK_ROOT", "/root/pdk"), "--pdk", os.environ.get("PDK", "ihp-sg13cmos5l"),
           "--run-tag", a.variant, "--force-run-dir", f"runs/{a.variant}"]
    if a.frm:
        cmd += ["--from", a.frm]
    if a.state:
        st = wd / "runs" / a.state / "state_out.json"
        cmd += ["--with-initial-state", str(st)]
    if a.to:
        cmd += ["--to", a.to]
    cmd.append(str(cpath))
    print("CMD", " ".join(cmd), flush=True)
    t0 = time.time()
    rc = subprocess.call(cmd, cwd=wd)
    wall = int(time.time() - t0)
    summ = gate_summary(run) if run.exists() else {}
    summ.update(rc=rc, wall_s=wall, base=a.base, variant=a.variant, overrides=over, frm=a.frm, state=a.state, to=a.to)
    out = RES / f"{a.base}__{a.variant}"
    out.mkdir(parents=True, exist_ok=True)
    json.dump(summ, open(out / "summary.json", "w"), indent=1)
    subprocess.call(f"tar czf {out}/run_text.tgz --exclude='*.odb' --exclude='*.def' --exclude='*.gds' "
                    f"--exclude='*.spef' --exclude='*.sdf' runs/{a.variant} src/config_{a.variant}.json", shell=True, cwd=wd)
    line = (f"{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())} {a.base}__{a.variant} rc={rc} wall_s={wall} "
            f"last={summ.get('last_step')} over={json.dumps(over, separators=(',', ':'))}")
    with open(RES / "runs.log", "a") as f:
        f.write(line + "\n")
    print(json.dumps(summ, indent=1))
    print("VARIANT_END", line)
    return rc


if __name__ == "__main__":
    sys.exit(main())
