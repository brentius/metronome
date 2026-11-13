"""Unattended full-v2 qualification. Run inside the pinned, prepared flow image.

No cloud credentials or lifecycle mutations: the external controller stops the pod.
Outputs go on the network volume; a failed, skipped, absent or timed-out gate cannot pass.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import time
import traceback
import xml.etree.ElementTree as ET


def stamp():
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def xml_result(path):
    result = {"tests": 0, "failures": 0, "errors": 0, "skipped": 0, "ok": False}
    try:
        cases = list(ET.parse(path).getroot().iter("testcase"))
        result.update(tests=len(cases), failures=sum(c.find("failure") is not None for c in cases),
                      errors=sum(c.find("error") is not None for c in cases),
                      skipped=sum(c.find("skipped") is not None for c in cases))
        result["ok"] = bool(cases) and not any(result[k] for k in ("failures", "errors", "skipped"))
    except (OSError, ET.ParseError) as exc:
        result["problem"] = str(exc)
    return result


def physical_result(run):
    """Require fresh extracted post-PnR setup AND hold in every PDK corner."""
    values = {}
    for log in sorted(Path(run).glob("*stapostpnr*/*/sta.log")):
        for line in log.read_text(errors="replace").splitlines():
            match = re.match(r"%OL_METRIC_F\s+(timing__(setup|hold)__ws__corner:nom_(typ|slow|fast)_\S+)\s+(\S+)", line)
            if match:
                key, kind, corner, value = match.groups()
                values[f"{kind}_{corner}"] = {"value_ns": float(value), "metric": key,
                                               "source": str(log.relative_to(run))}
    required = {f"{kind}_{corner}" for kind in ("setup", "hold") for corner in ("typ", "slow", "fast")}
    return {"ok": required <= values.keys() and all(v["value_ns"] >= 0 for v in values.values()),
            "missing": sorted(required - values.keys()), "timing": values}


class Pipeline:
    def __init__(self, repo, out, summary, seconds):
        self.repo, self.out, self.summary = Path(repo), Path(out), summary
        self.deadline = time.monotonic() + seconds
        self.active = None

    def save(self):
        tmp = self.out / "summary.tmp"
        tmp.write_text(json.dumps(self.summary, indent=2) + "\n")
        tmp.replace(self.out / "summary.json")

    def stop_active(self):
        if self.active and self.active.poll() is None:
            if os.name == "posix":
                os.killpg(self.active.pid, signal.SIGTERM)
            else:
                self.active.terminate()
            try:
                self.active.wait(timeout=15)
            except subprocess.TimeoutExpired:
                if os.name == "posix":
                    os.killpg(self.active.pid, signal.SIGKILL)
                else:
                    self.active.kill()
                self.active.wait()

    def unavailable(self, name, reason):
        self.summary["stages"].append({"name": name, "status": "unavailable", "reason": reason})
        self.save()

    def step(self, name, command, timeout=7200, xml=None, env=None):
        entry = {"name": name, "command": list(map(str, command)), "started": stamp(), "status": "running"}
        self.summary["stages"].append(entry)
        self.save()
        remaining = self.deadline - time.monotonic()
        if remaining <= 0:
            entry.update(status="timeout", reason="pipeline runtime limit", finished=stamp())
            self.save()
            return entry
        started = time.monotonic()
        try:
            with (self.out / f"{name}.log").open("x", encoding="utf-8") as log:
                print(stamp(), "START", name, flush=True)
                self.active = subprocess.Popen(command, cwd=self.repo, stdout=log, stderr=subprocess.STDOUT,
                                               env={**os.environ, **(env or {})}, start_new_session=os.name == "posix")
                try:
                    entry["returncode"] = self.active.wait(timeout=min(timeout, remaining))
                    entry["status"] = "passed" if entry["returncode"] == 0 else "failed"
                except subprocess.TimeoutExpired:
                    self.stop_active()
                    entry.update(status="timeout", returncode=self.active.returncode)
                if xml:
                    entry["xml"] = xml_result(xml)
                    if not entry["xml"]["ok"] and entry["status"] == "passed":
                        entry["status"] = "failed"
        except KeyboardInterrupt:
            self.stop_active()
            entry.update(status="interrupted", returncode=self.active.returncode if self.active else None)
            raise
        except Exception as exc:
            entry.update(status="failed", reason=repr(exc))
        finally:
            self.active = None
            entry.update(finished=stamp(), wall_seconds=round(time.monotonic() - started, 3))
            self.save()
            print(stamp(), "END", name, entry["status"], flush=True)
        return entry


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--tag", required=True)
    ap.add_argument("--hours", type=float, default=11)
    args = ap.parse_args()
    repo, out = args.repo.resolve(), args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    (out / "pipeline.pid").write_text(str(os.getpid()) + "\n")
    summary = {"started": stamp(), "status": "running", "tag": args.tag, "repo": str(repo),
               "clock_period_ns": 16.667, "existing_rtl_lockstep_period_ns": 16,
               "rtl_random_seeds": 64, "gl_random_seeds": 16,
               "sdf_random_seeds_per_corner": 4, "stages": [], "limitations": [
                   "Icarus delay simulation does not implement setup/hold timing checks.",
                   "SDF conversion omits SRAM timing and cell-to-cell interconnect; retain converter logs.",
                   "No full-v2 formal suite exists; legacy-v1 formal is not v2 evidence.",
                   "Compiler supports its documented UART/SPI/Ethernet subset only.",
                   "No hardware measurement; a passing aggregate is limited to these verification gates."]}
    p = Pipeline(repo, out, summary, args.hours * 3600)
    py = sys.executable
    scripts = repo / "code/flow/runpod"
    p.save()
    if (repo / "snapshot.json").exists():
        shutil.copy2(repo / "snapshot.json", out / "snapshot.json")

    def terminate(signum, frame):
        raise KeyboardInterrupt(f"signal {signum}")

    signal.signal(signal.SIGTERM, terminate)
    try:
        snapshot = json.loads((repo / "snapshot.json").read_text())
        for name, expected in snapshot["files"].items():
            actual = hashlib.sha256((repo / name).read_bytes()).hexdigest()
            if actual != expected:
                raise RuntimeError(f"snapshot checksum mismatch: {name}")
        summary["source_revision"] = snapshot["revision"]
        p.save()
        for tool in ("iverilog", "vvp", "verilator", "yosys", "openroad", "klayout", "netgen"):
            if shutil.which(tool) is None:
                raise RuntimeError(f"missing required tool {tool}")
        p.step("versions", ["bash", "-c", "cat /root/flow_versions.txt; python --version; iverilog -V; verilator --version; yosys -V; python -m pip freeze"], timeout=60)
        for name, script in (("md2_generated", "code/md2/gen.py"),
                             ("rtl_tables", "code/tests/rtl_v2/gen_rtl_tables.py")):
            p.step(name, [py, script, "--check"], timeout=60)
        suites = [
            ("model", ["sim/reference/tests_v2"], {}),
            ("host_md2", ["code/host2/tests", "code/tests/md2"], {}),
            ("score", ["code/tests/score"], {}),
            ("compiler", ["code/tests/scorec"], {}),
            ("rtl_blocks_lint", ["code/tests/rtl_v2"], {"BLOCK_SEEDS": "64"}),
            ("rtl_lockstep", ["code/tests/lockstep_v2"], {"LOCKSTEP_SEEDS": "64", "LOCKSTEP_TAG": "_overnight"}),
            ("rtl_behav_sram", ["code/tests/lockstep_v2"], {"LOCKSTEP_SEEDS": "16", "LOCKSTEP_BEHAV_SRAM": "1", "LOCKSTEP_TAG": "_overnight_behav"}),
            ("sizing_supplement", ["code/tests/v2_sizing"], {}),
            ("flow_safety", ["code/tests/flow"], {}),
        ]
        for name, paths, env in suites:
            xml = out / f"{name}.xml"
            p.step(name, [py, "-m", "pytest", *paths, "-q", "-ra", f"--junitxml={xml}"], xml=xml, env=env)
        p.step("tt_rtl", [py, "test/run_local.py"], xml=repo / "test/sim_build/rtl/results.xml")
        physical_tag = args.tag + "_pnr"
        physical = Path("/workspace/results") / physical_tag
        project = out / "tt_project.tgz"
        with tarfile.open(project, "w:gz") as tar:
            for name in ("info.yaml", "src", "test", "docs", "librelane_plugin_sram_pdn.py", "odb_stripes.py"):
                path = repo / name
                for source in ([path] if path.is_file() else sorted(path.rglob("*"))):
                    if not source.is_file() or any(x in source.parts for x in ("__pycache__", "sim_build", ".pytest_cache")):
                        continue
                    tar.add(source, arcname=source.relative_to(repo))
        summary["physical_results"] = str(physical)
        p.step("harden", ["bash", str(scripts / "tt_harden.sh"), str(project), physical_tag], timeout=5 * 3600)
        timing = physical_result(Path("/root/work") / physical_tag / "runs/wokwi")
        summary["stages"].append({"name": "extracted_timing", "status": "passed" if timing["ok"] else "failed", **timing})
        p.save()
        # Archive the reference/toolchain inputs needed by the TT GL smoke's Python imports.
        work = Path("/root/work") / physical_tag
        if work.exists():
            for name in ("sim/reference", "code/md2"):
                dest = work / name
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copytree(repo / name, dest, dirs_exist_ok=True)
        if list((physical / "tt_submission").glob("*.gds*")):
            p.step("precheck", ["bash", str(scripts / "tt_precheck.sh"), physical_tag], timeout=3600)
        else:
            p.unavailable("precheck", "hardening did not export submission GDS")
        netlists = sorted((physical / "final/nl").glob("*.nl.v"))
        if netlists:
            p.step("tt_gl", ["bash", str(scripts / "gl_v2.sh"), physical_tag],
                   xml=physical / "gl/results.xml")
            cells = Path(os.environ.get("PDK_ROOT", "/root/pdk")) / "ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/verilog"
            base = [py, str(scripts / "verify_v2_gates.py"), "--repo", str(repo), "--netlist", str(netlists[0]), "--cells", str(cells)]
            p.step("gl_lockstep", [*base, "--out", str(out / "gl_lockstep"), "--seeds", "16"], timeout=7200)
            for corner in ("typ", "slow", "fast"):
                sdfs = sorted((physical / "final/sdf").glob(f"*{corner}*/*.sdf"))
                if sdfs:
                    p.step(f"sdf_{corner}", [*base, "--sdf", str(sdfs[0]), "--out", str(out / f"sdf_{corner}"), "--seeds", "4"], timeout=7200)
                else:
                    p.unavailable(f"sdf_{corner}", "no exported corner SDF")
        else:
            for name in ("tt_gl", "gl_lockstep", "sdf_typ", "sdf_slow", "sdf_fast"):
                p.unavailable(name, "hardening did not export a final netlist")
        summary["status"] = "passed" if all(s["status"] == "passed" for s in summary["stages"]) else "failed"
    except BaseException as exc:
        p.stop_active()
        summary.update(status="interrupted" if isinstance(exc, KeyboardInterrupt) else "failed", exception=repr(exc))
        (out / "exception.txt").write_text(traceback.format_exc())
    finally:
        # A timeout must not erase the only native reports when the pod is stopped.
        work = Path("/root/work") / (args.tag + "_pnr") / "runs/wokwi"
        if work.exists():
            with tarfile.open(out / "pnr_native_reports.tgz", "w:gz") as tar:
                for source in work.rglob("*"):
                    if source.is_file() and source.suffix in (".log", ".rpt", ".json", ".sdc"):
                        tar.add(source, arcname=source.relative_to(work))
            final = work / "final"
            if final.exists():
                shutil.copytree(final, out / "pnr_final_backup", dirs_exist_ok=True)
        # Retain simulator XML and generated inputs even when an intermediate stage fails.
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
