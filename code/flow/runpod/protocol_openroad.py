#!/usr/bin/env python3
"""Replay post-route IHP SG13 STA from the archived r4b database/SPEF.

This intentionally runs only OpenROAD STA. It does not invoke LibreLane or
modify the archived artifact. Requires the extracted r4b tar tree and the
pinned IHP PDK installed by setup_flow.sh.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

RUN = "metronome-v2-b-r4b_20261113T1143"
CORNER_INFO = {
    "nom_typ_1p20V_25C": ("typ", "typ_1p20V_25C", "typ_1p2V_3p3V_25C", "typ_1p20V_25C"),
    "nom_slow_1p08V_125C": ("slow", "slow_1p08V_125C", "slow_1p08V_3p0V_125C", "slow_1p08V_125C"),
    "nom_fast_1p32V_m40C": ("fast", "fast_1p32V_m40C", "fast_1p32V_3p6V_m40C", "fast_1p32V_m55C"),
}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def tclquote(path: Path) -> str:
    return "{" + str(path).replace("\\", "/").replace("}", "\\}") + "}"


def unique(root: Path, pattern: str) -> Path:
    matches = list(root.glob(pattern))
    if len(matches) != 1:
        raise RuntimeError(f"Expected one {pattern!r} under {root}, found {len(matches)}")
    return matches[0]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--artifact-root", required=True, type=Path,
                    help="extracted archive root containing root/work/... and workspace/results/...")
    ap.add_argument("--output-root", required=True, type=Path,
                    help="new evidence directory; must not already exist")
    ap.add_argument("--pdk-root", type=Path, default=Path("/root/pdk"))
    ap.add_argument("--openroad", default="openroad")
    args = ap.parse_args()

    artifact = args.artifact_root.resolve()
    out = args.output_root.resolve()
    if out.exists():
        raise SystemExit(f"Refusing to overwrite existing output directory: {out}")
    runroot = unique(artifact, f"root/work/*_pnr/runs/{RUN}")
    odb = runroot / "12-odb-cellfrequencytables/tt_um_brentius_metronome.odb"
    netlist = runroot / "11-openroad-fillinsertion/tt_um_brentius_metronome.nl.v"
    spef = runroot / "13-openroad-rcx/nom/tt_um_brentius_metronome.nom.spef"
    # Reuse the archived expanded constraints. Native signoff read project.sdc
    # through SIGNOFF_SDC_FILE; equivalence is reviewed against its expanded SDC
    # and six native corner slacks, rather than claiming identical entry files.
    native_state = runroot / "14-openroad-stapostpnr/state_in.json"
    state = json.loads(native_state.read_text(encoding="utf-8"))
    sdc = artifact / state["sdc"].lstrip("/")
    for p in (odb, netlist, spef, sdc):
        if not p.is_file():
            raise SystemExit(f"Missing required archived input: {p}")
    sdc_text = sdc.read_text(encoding="utf-8", errors="replace")
    clock_match = re.search(r"create_clock\s+(?:-[^\s]+\s+[^\s]+\s+)*-period\s+([0-9.]+).*?-name\s+(\S+)", sdc_text)
    if not clock_match:
        # SDC option order is not fixed; accept period/name anywhere on the create_clock line.
        clock_line = next((line for line in sdc_text.splitlines() if "create_clock" in line and "-period" in line), "")
        period_match = re.search(r"-period\s+([0-9.]+)", clock_line)
        name_match = re.search(r"-name\s+(\S+)", clock_line)
        if not period_match or not name_match:
            raise SystemExit("Could not determine clock name and period from archived SDC")
        clock_period_ns, clock_name = float(period_match.group(1)), name_match.group(1)
    else:
        clock_period_ns, clock_name = float(clock_match.group(1)), clock_match.group(2)
    if abs(clock_period_ns - 16.667) > 1e-6:
        raise SystemExit(f"Archived SDC clock period is {clock_period_ns} ns, expected 16.667 ns")

    versions = sorted((args.pdk_root / "ciel/ihp-sg13/versions").glob("*/ihp-sg13cmos5l"))
    if len(versions) != 1:
        raise SystemExit(f"Expected exactly one installed ihp-sg13 PDK version under {args.pdk_root}; got {versions}")
    pdk = versions[0]
    libdir = pdk / "libs.ref"
    std = libdir / "sg13cmos5l_stdcell/lib"
    io = libdir / "sg13cmos5l_io/lib"
    sram = libdir / "sg13cmos5l_sram/lib"

    out.mkdir(parents=True)
    inputs = {"odb": odb, "post_fill_netlist": netlist, "spef": spef, "sdc": sdc,
              "native_state": native_state}
    input_meta = {k: {"path": str(v), "bytes": v.stat().st_size, "sha256": sha256(v)} for k, v in inputs.items()}
    version = subprocess.run([args.openroad, "-version"], text=True, capture_output=True)
    if version.returncode:
        raise SystemExit(f"Cannot run OpenROAD {args.openroad}: {version.stderr}")

    results = {}
    for corner, (label, std_suffix, io_suffix, ram_suffix) in CORNER_INFO.items():
        libraries = [
            std / f"sg13cmos5l_stdcell_{std_suffix}.lib",
            io / f"sg13cmos5l_io_{io_suffix}.lib",
            sram / f"RM_IHPSG13_1P_256x64_c2_bm_bist_{ram_suffix}.lib",
            sram / f"RM_IHPSG13_1P_512x32_c2_bm_bist_{ram_suffix}.lib",
        ]
        for lib in libraries:
            if not lib.is_file():
                raise SystemExit(f"Missing {corner} timing library: {lib}")
        tcl = out / f"sta_{label}.tcl"
        log = out / f"sta_{label}.log"
        tcl.write_text("\n".join([
            f"define_corners {corner}",
            *[f"read_liberty -corner {corner} {tclquote(lib)}" for lib in libraries],
            f"read_db {tclquote(odb)}",
            f"read_sdc {tclquote(sdc)}",
            f"read_spef -corner {corner} {tclquote(spef)}",
            "set_propagated_clock [all_clocks]",
            "puts {=== SETUP MAX ===}",
            "report_checks -corner " + corner + " -path_delay max -format full_clock_expanded -fields {slew cap input_pin net fanout} -digits 9 -group_path_count 1",
            "puts {=== HOLD MIN ===}",
            "report_checks -corner " + corner + " -path_delay min -format full_clock_expanded -fields {slew cap input_pin net fanout} -digits 9 -group_path_count 1",
            "exit",
            "",
        ]), encoding="utf-8")
        proc = subprocess.run([args.openroad, "-exit", str(tcl)], text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log.write_text(proc.stdout, encoding="utf-8", errors="replace")
        setup_block = proc.stdout.split("=== SETUP MAX ===", 1)[-1].split("=== HOLD MIN ===", 1)[0]
        hold_block = proc.stdout.split("=== HOLD MIN ===", 1)[-1]
        slack_re = r"^\s*([-+]?[0-9]+\.[0-9]+)\s+slack\s+\((?:MET|VIOLATED)\)"
        # report_checks emits one worst path per path group. The first group
        # is not necessarily the global worst (notably SRAM/clock-gating hold).
        setup = [float(v) for v in re.findall(slack_re, setup_block, re.MULTILINE)]
        hold = [float(v) for v in re.findall(slack_re, hold_block, re.MULTILINE)]
        # Keep report excerpts easy to inspect and establish report commands ran.
        setup_section = "=== SETUP MAX ===" in proc.stdout
        hold_section = "=== HOLD MIN ===" in proc.stdout
        errors = [line for line in proc.stdout.splitlines()
                  if re.search(r"^\s*(?:\[ERROR\b|Error:|Tcl error)", line, re.IGNORECASE)]
        results[label] = {
            "corner": corner,
            "process_returncode": proc.returncode,
            "setup_worst_slack_ns": min(setup) if setup else None,
            "hold_worst_slack_ns": min(hold) if hold else None,
            "setup_path_group_slacks_ns": setup,
            "hold_path_group_slacks_ns": hold,
            "setup_report_present": setup_section,
            "hold_report_present": hold_section,
            "fatal_log_lines": errors,
            "log": log.name,
            "tcl": tcl.name,
            "libraries": {str(lib): sha256(lib) for lib in libraries},
        }

    reported = all(r["process_returncode"] == 0 and not r["fatal_log_lines"] and r["setup_worst_slack_ns"] is not None
                 and r["hold_worst_slack_ns"] is not None and r["setup_report_present"]
                 and r["hold_report_present"] for r in results.values())
    passed = reported and all(r["setup_worst_slack_ns"] >= 0 and r["hold_worst_slack_ns"] >= 0
                              for r in results.values())
    summary = {
        "kind": "fresh_openroad_postroute_sta_replay",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "baseline_revision": "e8f669fe9cdc6041becd9827b6f63d0f01c10873",
        "source_revision": "ce37924d8738b1185fe2d40da9246ee548ab9b79",
        "clock": {"name": clock_name, "period_ns": clock_period_ns, "source": str(sdc)},
        "openroad_version": version.stdout.strip() or version.stderr.strip(),
        "pdk": str(pdk),
        "pdk_version": pdk.parent.name,
        "inputs": input_meta,
        "corners": results,
        "all_six_slacks_reported": reported,
        "all_six_slacks_nonnegative": passed,
        "status": "PASS" if passed else "FAIL",
        "limitations": ["Setup/hold STA replay only; no RTL synthesis or PNR rerun",
                        "Uses archived expanded SDC, final routed ODB and extracted nominal SPEF",
                        "No fresh electrical, DRC, LVS or precheck checks; original qualification is inherited",
                        "Timing result is not silicon or hardware measurement"],
    }
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    (out / "README.txt").write_text(
        "Fresh OpenROAD post-route STA replay. See summary.json and sta_*.log.\n"
        f"Command: python3 protocol_openroad.py --artifact-root {artifact} --output-root {out} --pdk-root {args.pdk_root}\n"
        f"OpenROAD: {summary['openroad_version']}\n", encoding="utf-8")
    print(json.dumps(summary, indent=2))
    return 0 if passed else 2


if __name__ == "__main__":
    sys.exit(main())
