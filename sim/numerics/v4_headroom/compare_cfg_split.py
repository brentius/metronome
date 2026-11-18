"""Run frozen v4 configurations on the same pinned flow pod."""
import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path("/workspace")
HERE = Path(__file__).resolve().parent
FLOW = ROOT / "jsc/flow"
RESULTS = ROOT / "results"
PROJECT = "tt_um_brentius_metronome"
KINDS = ("setup", "hold")
CORNERS = ("nom_fast_1p32V_m40C", "nom_slow_1p08V_125C", "nom_typ_1p20V_25C")
CHECKS = ("route__drc_errors", "design__lvs_error__count", "antenna__violating__nets",
          "design__max_slew_violation__count", "design__max_cap_violation__count",
          "timing__setup_vio__count", "timing__hold_vio__count")


def run_logged(argv, path):
    with path.open("wb") as log:
        return subprocess.call(argv, stdout=log, stderr=subprocess.STDOUT)


def audit(tag, harden_rc):
    result = RESULTS / tag
    run = Path("/root/work") / tag / "runs/wokwi"
    options = ("python3", str(HERE / "collect.py"), tag)
    collect_rc = run_logged(options, result / "collect.log")
    metrics_path = result / "final/metrics.json"
    metrics = json.loads(metrics_path.read_text()) if metrics_path.exists() else {}
    timing = {}
    for log in sorted(run.glob("*stapostpnr*/*/sta.log")):
        for kind, corner, value in re.findall(
                r"^%OL_METRIC_F\s+timing__(setup|hold)__ws__corner:(\S+)\s+(\S+)",
                log.read_text(errors="replace"), re.M):
            if corner in CORNERS:
                timing.setdefault(f"{kind}:{corner}", []).append(float(value))
    clock_ok = set(timing) == {f"{k}:{c}" for k in KINDS for c in CORNERS} and all(
        len(values) == 1 and values[0] >= 0 for values in timing.values())
    sta_logs = [p for p in run.glob("*stapostpnr*/**/*.log")]
    pin_counts = sorted({int(count) for p in sta_logs for count in re.findall(
        r"config latch D pins under the 2-cycle setup exception: (\d+)",
        p.read_text(errors="replace"))})
    precheck = gl = None
    if clock_ok and harden_rc == 0:
        precheck = run_logged(["bash", str(FLOW / "tt_precheck.sh"), tag],
                              result / "precheck_launcher.log")
        work = run.parent.parent
        for name in ("code/md2", "sim/reference"):
            shutil.copytree(HERE / "support" / name, work / name, dirs_exist_ok=True)
        gl = run_logged(["bash", str(FLOW / "gl_v2.sh"), tag], result / "gl_launcher.log")
    defs = sorted((result / "final/def").glob("*.def"))
    lef = (Path("/root/pdk/ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lef")
           / "sg13cmos5l_stdcell.lef")
    geometry = grt_geometry = None
    if defs and lef.exists():
        geometry = run_logged(["python3", str(HERE / "def_hotspots.py"), str(defs[0]),
                               str(lef), "--out", str(result / "cfg_geometry.json")],
                              result / "cfg_geometry.log")
    grt_defs = sorted(run.glob("*-openroad-globalrouting/*.def"))
    if grt_defs and lef.exists():
        grt_geometry = run_logged(["python3", str(HERE / "def_hotspots.py"), str(grt_defs[0]),
                                   str(lef), "--out", str(result / "grt_latch_placement.json")],
                                  result / "grt_latch_placement.log")
    return dict(tag=tag, harden_rc=harden_rc, collect_rc=collect_rc, timing=timing,
                timing_pass=clock_ok, latch_d_endpoint_counts=pin_counts,
                violations={k: metrics.get(k) for k in CHECKS}, precheck_rc=precheck,
                gl_rc=gl, geometry_rc=geometry, grt_geometry_rc=grt_geometry, qualified=bool(
                    harden_rc == collect_rc == 0 and clock_ok and pin_counts == [2112]
                    and precheck == gl == 0 and all(metrics.get(k) == 0 for k in CHECKS)))


def main(prefix, labels):
    output = RESULTS / prefix
    output.mkdir()
    setup_rc = run_logged(["bash", str(FLOW / "setup_flow.sh")], output / "setup.log")
    if setup_rc:
        return setup_rc
    inputs = json.loads((HERE / "inputs.json").read_text())["files"]
    processes = {}
    for label in labels:
        source = HERE / (label + ".tgz")
        with source.open("rb") as stream:
            assert hashlib.file_digest(stream, "sha256").hexdigest() == inputs[source.name]
        tag = f"{prefix}_{label}"
        with (output / (tag + ".log")).open("wb") as log:
            processes[tag] = subprocess.Popen(
                ["bash", str(FLOW / "tt_harden.sh"), str(source), tag],
                stdout=log, stderr=subprocess.STDOUT)
    outcomes = {tag: audit(tag, process.wait()) for tag, process in processes.items()}
    (output / "summary.json").write_text(json.dumps(outcomes, indent=2) + "\n")
    (output / "DONE").write_text("Both experiments collected. Consult summary.json for gate results.\n")
    print(json.dumps(outcomes, indent=2), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2:] or ("control", "split")))
