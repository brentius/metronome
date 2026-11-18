"""Unattended v3.0 verification on the prepared flow pod (V3_PLAN.md). Two independent parts, run concurrently:

  --part checks    software, model, RTL lockstep (v2 + v3 scenarios), v3 formal, compiled-program BMC, ISA sweep,
                   compiled-image RTL runs (score_rtl, protocol_campaign).
  --part physical  TT harden at 16.667 ns, then ONLY if extracted setup and hold close in every corner: precheck
                   (KLayout DRC, LVS-dependent export), TT GL, full-netlist lockstep, three-corner SDF, and the
                   compiled-image and protocol matrices on the routed netlist.

Reuses verify_v2_pipeline.Pipeline (failed/skipped/absent/timed-out stages cannot pass; atomic summary; DONE marker).
No cloud credentials or lifecycle mutations here.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import signal
import sys
import tarfile
import traceback
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_v2_pipeline import Pipeline, physical_result, stamp  # noqa: E402

CELLS = Path(os.environ.get("PDK_ROOT", "/root/pdk")) / "ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog"
OSS = Path("/root/oss-cad-suite")


def checks(p, repo, out, py):
    suites = [
        ("model", ["sim/reference/tests_v2"], {}),
        ("host_md2", ["code/host2/tests", "code/tests/md2"], {}),
        ("score", ["code/tests/score"], {}),
        ("compiler", ["code/tests/scorec"], {}),
        ("score_lib", ["code/tests/score_lib"], {"SCORE_LIB_SLOW": "1"}),
        ("transcribe", ["code/tests/transcribe"], {}),
        ("rtl_blocks_lint", ["code/tests/rtl_v2"], {"BLOCK_SEEDS": "64"}),
        ("rtl_lockstep", ["code/tests/lockstep_v2"], {"LOCKSTEP_SEEDS": "64", "LOCKSTEP_TAG": "_v3"}),
        ("rtl_behav_sram", ["code/tests/lockstep_v2"], {"LOCKSTEP_SEEDS": "16", "LOCKSTEP_BEHAV_SRAM": "1",
                                                        "LOCKSTEP_TAG": "_v3_behav"}),
        ("flow_safety", ["code/tests/flow", "code/flow/cdc"], {}),
    ]
    for name, paths, env in suites:
        xml = out / f"{name}.xml"
        p.step(name, [py, "-m", "pytest", *paths, "-q", "-ra", f"--junitxml={xml}"], xml=xml, env=env, timeout=4 * 3600)
    p.step("tt_rtl", [py, "test/run_local.py"], xml=repo / "test/sim_build/rtl/results.xml")
    p.step("score_rtl", [py, "code/tests/score_rtl/run_score.py", "--repo", str(repo), "--out", str(out / "score_rtl")],
           timeout=3 * 3600)
    p.step("protocol_rtl", [py, "code/tests/protocol_campaign/run_campaign.py", "--repo", str(repo),
                            "--out", str(out / "protocol_rtl")], timeout=3 * 3600)
    # five sweeps in parallel (about 5 min per slot run on one core); every one must exit 0
    runs = [("slot0", "--group exhaustive --slots 0"), ("slot1", "--group exhaustive --slots 1"),
            ("slot2", "--group exhaustive --slots 2"), ("cond", "--group cond"), ("tstop", "--group tstop")]
    script = "pids=''; " + " ".join(
        f"{py} code/tests/isa_sweep/sweep.py --root . --out {out}/isa/{n} {opt} > {out}/isa_{n}.log 2>&1 & pids=\"$pids $!\";"
        for n, opt in runs) + " rc=0; for q in $pids; do wait $q || rc=1; done; exit $rc"
    (out / "isa").mkdir(exist_ok=True)
    p.step("isa_sweep", ["bash", "-c", script], timeout=3 * 3600)
    if (OSS / "bin/sby").exists():
        env = {"PATH": f"{OSS}/bin:{OSS}/py3bin:" + os.environ["PATH"]}
        xml = out / "formal_v3.xml"
        p.step("formal_v3", [py, "-m", "pytest", "code/tests/formal/test_v3_formal.py", "-q", "-ra", f"--junitxml={xml}"],
               xml=xml, env=env, timeout=3600)
        p.step("bmc_uart_tx", [py, "code/tests/formal_programs/run_proofs.py", "--root", ".", "--out",
                               str(out / "bmc_uart_tx"), "--task", "hazard", "--timeout", "5400"],
               env=env, timeout=6000)
    else:
        p.unavailable("formal_v3", f"{OSS}/bin/sby absent")
        p.unavailable("bmc_uart_tx", f"{OSS}/bin/sby absent")


def physical(p, repo, out, py, tag, scripts):
    physical_tag = tag + "_pnr"
    phys = Path("/workspace/results") / physical_tag
    project = out / "tt_project.tgz"
    with tarfile.open(project, "w:gz") as tar:
        for name in ("info.yaml", "src", "test", "docs", "librelane_plugin_sram_pdn.py", "odb_stripes.py"):
            path = repo / name
            for source in ([path] if path.is_file() else sorted(path.rglob("*"))):
                if source.is_file() and not any(x in source.parts for x in ("__pycache__", "sim_build", ".pytest_cache")):
                    tar.add(source, arcname=source.relative_to(repo))
    p.summary["physical_results"] = str(phys)
    p.step("harden", ["bash", str(scripts / "tt_harden.sh"), str(project), physical_tag], timeout=6 * 3600)
    timing = physical_result(Path("/root/work") / physical_tag / "runs/wokwi")
    p.summary["stages"].append({"name": "extracted_timing", "status": "passed" if timing["ok"] else "failed", **timing})
    p.save()
    if not timing["ok"]:
        for name in ("precheck", "tt_gl", "gl_lockstep", "sdf_typ", "sdf_slow", "sdf_fast", "score_gates", "protocol_gates"):
            p.unavailable(name, "timing did not close; DRC/GL gated on timing (user order 2026-11-16)")
        return
    work = Path("/root/work") / physical_tag
    for name in ("sim/reference", "code/md2"):
        shutil.copytree(repo / name, work / name, dirs_exist_ok=True)
    if list((phys / "tt_submission").glob("*.gds*")):
        p.step("precheck", ["bash", str(scripts / "tt_precheck.sh"), physical_tag], timeout=3600)
    else:
        p.unavailable("precheck", "hardening did not export submission GDS")
    netlists = sorted((phys / "final/nl").glob("*.nl.v"))
    if not netlists:
        for name in ("tt_gl", "gl_lockstep", "sdf_typ", "sdf_slow", "sdf_fast", "score_gates", "protocol_gates"):
            p.unavailable(name, "no final netlist")
        return
    p.step("tt_gl", ["bash", str(scripts / "gl_v2.sh"), physical_tag], xml=phys / "gl/results.xml")
    base = [py, str(scripts / "verify_v2_gates.py"), "--repo", str(repo), "--netlist", str(netlists[0]), "--cells", str(CELLS)]
    p.step("gl_lockstep", [*base, "--out", str(out / "gl_lockstep"), "--seeds", "16"], timeout=7200)
    for corner in ("typ", "slow", "fast"):
        sdfs = sorted((phys / "final/sdf").glob(f"*{corner}*/*.sdf"))
        if sdfs:
            p.step(f"sdf_{corner}", [*base, "--sdf", str(sdfs[0]), "--out", str(out / f"sdf_{corner}"), "--seeds", "4"],
                   timeout=7200)
        else:
            p.unavailable(f"sdf_{corner}", "no exported corner SDF")
    p.step("score_gates", [py, "code/tests/score_rtl/run_matrix.py", "--repo", str(repo), "--out", str(out / "score_matrix"),
                           "--rtl-src", str(repo / "src"), "--physical", str(phys / "final"), "--cells", str(CELLS),
                           "--modes", "gates", "typ", "slow", "fast"], timeout=3 * 3600)
    for mode in ("gates", "typ", "slow", "fast"):
        cmd = [py, "code/tests/protocol_campaign/run_campaign.py", "--repo", str(repo), "--out",
               str(out / f"protocol_{mode}"), "--netlist", str(netlists[0]), "--cells", str(CELLS)]
        if mode != "gates":
            cmd += ["--sdf", str(sorted((phys / "final/sdf").glob(f"*{mode}*/*.sdf"))[0])]
        p.step(f"protocol_{mode}", cmd, timeout=3 * 3600)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--tag", required=True)
    ap.add_argument("--part", choices=("checks", "physical"), required=True)
    ap.add_argument("--hours", type=float, default=12)
    args = ap.parse_args()
    repo, out = args.repo.resolve(), args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    (out / "pipeline.pid").write_text(str(os.getpid()) + "\n")
    summary = {"started": stamp(), "status": "running", "tag": args.tag, "part": args.part, "repo": str(repo),
               "clock_period_ns": 16.667, "stages": [], "limitations": [
                   "Icarus delay simulation does not implement setup/hold timing checks.",
                   "SDF conversion omits SRAM timing and cell-to-cell interconnect.",
                   "Formal: v3 freeze unit (k-induction) and one compiled UART TX program (bounded); not the full chip.",
                   "No hardware measurement."]}
    p = Pipeline(repo, out, summary, args.hours * 3600)
    py = sys.executable
    p.save()

    def terminate(signum, frame):
        raise KeyboardInterrupt(f"signal {signum}")

    signal.signal(signal.SIGTERM, terminate)
    try:
        snapshot = json.loads((repo / "snapshot.json").read_text())
        for name, expected in snapshot["files"].items():
            if hashlib.sha256((repo / name).read_bytes()).hexdigest() != expected:
                raise RuntimeError(f"snapshot checksum mismatch: {name}")
        summary["source_revision"] = snapshot["revision"]
        shutil.copy2(repo / "snapshot.json", out / "snapshot.json")
        p.step("versions", ["bash", "-c", "cat /root/flow_versions.txt; python --version; iverilog -V; yosys -V; "
                            "python -m pip freeze; ls /root/oss-cad-suite/bin/sby /root/oss-cad-suite/bin/bitwuzla"],
               timeout=60)
        for name, script in (("md2_generated", "code/md2/gen.py"), ("rtl_tables", "code/tests/rtl_v2/gen_rtl_tables.py")):
            p.step(name, [py, script, "--check"], timeout=60)
        if args.part == "checks":
            checks(p, repo, out, py)
        else:
            physical(p, repo, out, py, args.tag, repo / "code/flow/runpod")
        summary["status"] = "passed" if all(s["status"] == "passed" for s in summary["stages"]) else "failed"
    except BaseException as exc:
        p.stop_active()
        summary.update(status="interrupted" if isinstance(exc, KeyboardInterrupt) else "failed", exception=repr(exc))
        (out / "exception.txt").write_text(traceback.format_exc())
    finally:
        work = Path("/root/work") / (args.tag + "_pnr") / "runs/wokwi"
        if args.part == "physical" and work.exists():
            with tarfile.open(out / "pnr_native_reports.tgz", "w:gz") as tar:
                for source in work.rglob("*"):
                    if source.is_file() and source.suffix in (".log", ".rpt", ".json", ".sdc"):
                        tar.add(source, arcname=source.relative_to(work))
            if (work / "final").exists():
                shutil.copytree(work / "final", out / "pnr_final_backup", dirs_exist_ok=True)
        if args.part == "checks":
            for prefix in ("code/tests", "test"):
                for source in (repo / prefix).rglob("*.xml"):
                    target = out / "simulator_xml" / source.relative_to(repo)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(source, target)
        summary["finished"] = stamp()
        p.save()
        hashes = {str(f.relative_to(out)): hashlib.sha256(f.read_bytes()).hexdigest()
                  for f in out.rglob("*") if f.is_file() and f.name not in ("manifest.json", "pipeline.pid")}
        (out / "manifest.json").write_text(json.dumps(hashes, indent=2) + "\n")
        (out / "DONE").write_text(summary["status"] + "\n")
        print(stamp(), "PIPELINE_DONE", summary["status"], flush=True)
    return 0 if summary["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
