"""Rebuild the local-only evidence audit/bundle from the preserved inputs.

Run from the repository root. Outputs belong to this dated analysis, and the
bundle explicitly does not contain a successful new physical-flow result.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import xml.etree.ElementTree as ET
import zipfile

ROOT = Path.cwd()
RAW = Path("data/raw/template_port_20261111T2055")
OUT = Path("data/processed/template_port_local_audit_20261111T2210.json")
BUNDLE = Path("data/processed/template_port_local_verified_20261111T2210.zip")
REV = "c83a7f4f0b3443ab065fc4619414ffa5bbd36f21"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
recorded = json.loads((RAW / "inputs.json").read_text())
byte_mismatches = [p for p, h in recorded["inputs"].items() if sha(Path(p)) != h]
normalized_mismatches = []
for p in recorded["inputs"]:
    blob = subprocess.check_output(["git", "show", f"{REV}:{p}"])
    if blob.replace(b"\r\n", b"\n") != Path(p).read_bytes().replace(b"\r\n", b"\n"):
        normalized_mismatches.append(p)
info_sources = re.findall(r'^    - "([^\"]+)"$', Path("info.yaml").read_text(), re.M)
make_sources = re.search(r"^PROJECT_SOURCES = (.*)$", Path("test/Makefile").read_text(), re.M).group(1).split()
old = json.loads(Path("data/raw/metronome_v1.0/evidence/config_r6_ant_setup.json").read_text())
new = json.loads(Path("src/config.json").read_text())
supplied_by_template = {"DESIGN_NAME", "VERILOG_FILES", "DIE_AREA", "FP_DEF_TEMPLATE", "VDD_PIN", "GND_PIN", "RT_MAX_LAYER", "OPENROAD_THREADS", "STA_THREADS"}
config_changes = {k: {"saved": v, "current": new.get(k)} for k, v in old.items()
                  if k != "//" and k not in supplied_by_template and v != new.get(k)}
suite = ET.parse(RAW / "regression_final.xml").find("testsuite")
regression = {k: int(suite.get(k)) for k in ("tests", "failures", "errors", "skipped")}
gl_root = ET.parse(RAW / "saved_v1_gl_smoke.xml").getroot()
gl_ok = len(gl_root.findall(".//testcase")) == 1 and not gl_root.findall(".//failure") and not gl_root.findall(".//error")
gl_inputs = json.loads((RAW / "saved_v1_gl_inputs.json").read_text())
gl_input_mismatches = [p for p, h in gl_inputs["inputs"].items() if sha(Path(p)) != h]
original_gl_matches = sha(Path(gl_inputs["original_netlist"])) == gl_inputs["original_netlist_sha256"]
log = (RAW / "github_gds_snapshot_2111.log").read_text(encoding="utf-8-sig")
lines = log.splitlines()
provenance = {}
for key, pattern in {
    "gds_action": r"Download action repository.*TinyTapeout/tt-gds-action",
    "librelane": r"Collecting librelane==",
    "yosys": r" Yosys [0-9]",
    "verilator": r"Verilator [0-9]",
}.items():
    provenance[key] = next((l for l in lines if re.search(pattern, l)), None)
checks = {
    "recorded_byte_hashes_match": not byte_mismatches,
    "source_matches_built_commit_ignoring_crlf": not normalized_mismatches,
    "source_lists_match": info_sources == make_sources and all((Path("src") / p).is_file() for p in info_sources),
    "saved_v1_project_config_matches": not config_changes,
    "full_regression_passes": regression == {"tests": 574, "failures": 0, "errors": 0, "skipped": 0},
    "saved_v1_gl_smoke_passes": bool(gl_ok),
    "saved_v1_gl_inputs_match": not gl_input_mismatches and original_gl_matches,
}
result = {
    "source_commit": REV, "class": "local verification and provenance audit; physical CI pending",
    "checks": checks, "byte_mismatches": byte_mismatches,
    "normalized_source_mismatches": normalized_mismatches,
    "saved_v1_gl_input_mismatches": gl_input_mismatches,
    "config_changes": config_changes, "template_supplied_keys": sorted(supplied_by_template),
    "source_count": len(info_sources), "regression": regression,
    "partial_ci_provenance": provenance,
    "pdk_revision_seen_in_ci_log": "89d42ee6d2fd9b50b86a1aada6fee6673c3e6008" in log,
    "raw_files": {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted((ROOT / RAW).rglob("*")) if p.is_file()},
}
OUT.write_text(json.dumps(result, indent=2) + "\n")
assert all(checks.values()), json.dumps(checks)
with zipfile.ZipFile(BUNDLE, "w", zipfile.ZIP_DEFLATED) as z:
    for p in sorted(RAW.rglob("*")):
        if p.is_file():
            z.write(p, p.as_posix())
    for p in sorted(Path("code/.build/template_gl_models").glob("*.v")):
        z.write(p, "models/" + p.name)
    p = Path("data/raw/metronome_v1.0/gds/tt_um_metronome.nl.v")
    z.write(p, "saved_v1/" + p.name)
    z.write(OUT, OUT.as_posix())
    z.write(Path(__file__), "analysis/" + Path(__file__).name)
with zipfile.ZipFile(BUNDLE) as z:
    assert z.testzip() is None, "bundle CRC check failed"
    for name, expected in result["raw_files"].items():
        assert hashlib.sha256(z.read(name)).hexdigest() == expected, name
BUNDLE.with_suffix(".zip.sha256").write_text(sha(BUNDLE) + "  " + BUNDLE.name + "\n")
print(json.dumps({"checks": checks, "source_count": len(info_sources), "bundle": str(BUNDLE),
                  "bundle_bytes": BUNDLE.stat().st_size, "bundle_sha256": sha(BUNDLE)}, indent=2))
