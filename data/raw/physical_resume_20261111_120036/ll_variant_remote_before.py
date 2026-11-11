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
import subprocess
import sys
import time
from pathlib import Path

WORK = Path("/root/work")
RES = Path("/workspace/results")

GATE_KEYS = [
    "design__instance__utilization__stdcell", "design__instance__area__stdcell",
    "global_route__wirelength", "route__drc_errors", "route__wirelength", "route__vias",
    "timing__setup__ws", "timing__hold__ws", "timing__setup__tns", "timing__hold__tns",
    "timing__setup__ws__corner:nom_slow_1p08V_125C", "timing__hold__ws__corner:nom_fast_1p32V_m40C",
    "timing__setup__ws__corner:max_ss_100C_1v60", "antenna__violating__nets", "antenna__violating__pins",
    "magic__drc_error__count", "klayout__drc_error__count", "design__lvs_error__count",
    "design__max_slew_violation__count", "design__max_cap_violation__count",
]


def gate_summary(run: Path) -> dict:
    """Latest value of each gate metric across the run's steps (later steps override earlier ones)."""
    out: dict = {"steps": []}
    for f in sorted(glob.glob(str(run / "*/or_metrics_out.json"))) + sorted(glob.glob(str(run / "final/metrics.json"))):
        try:
            d = json.load(open(f))
        except Exception:
            continue
        out["steps"].append(Path(f).parent.name)
        for k, v in d.items():
            if k in GATE_KEYS or k.startswith("timing__setup__ws__corner") or k.startswith("timing__hold__ws__corner") \
                    or k.startswith("global_route__") or k.startswith("route__drc"):
                out[k] = v
    steps = sorted(p.name for p in run.iterdir() if p.is_dir() and p.name[:2].isdigit())
    out["last_step"] = steps[-1] if steps else None
    grt = sorted(run.glob("*globalrouting*/*.log"))
    if grt:
        txt = grt[-1].read_text(errors="replace")
        out["grt_extra_iterations"] = txt.count("Start extra iteration")
        out["grt_ndr_disabled"] = txt.count("GRT-0273")
    out.pop("steps")
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
