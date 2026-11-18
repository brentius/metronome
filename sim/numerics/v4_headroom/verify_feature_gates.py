"""Run the v4 gate and SDF regression against an already qualified harden."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def gate_job_specs(repo, final, out, cells, rtl_src):
    [netlist] = sorted((final / "nl").glob("*.nl.v"))
    sdf = {}
    for corner in ("typ", "slow", "fast"):
        [sdf[corner]] = sorted((final / "sdf").glob(f"nom_{corner}_*/*.sdf"))
    base = [sys.executable, str(repo / "code/flow/runpod/verify_v2_gates.py"), "--repo", str(repo),
            "--netlist", str(netlist), "--cells", str(cells)]
    short_v4 = ["--scenario", "v4_config_write", "--scenario", "v4_replay"]
    long_v4 = ["--scenario", "v4_stage1", "--scenario", "v4_stage2"]
    yield "gate_v4", [*base, "--out", str(out / "gate_v4"), *short_v4, *long_v4], 7200
    yield "gate_v3_regression", [*base, "--out", str(out / "gate_v3_regression"), "--seeds", "16"], 7200
    for corner, annotation in sdf.items():
        yield (f"sdf_{corner}", [*base, "--out", str(out / f"sdf_{corner}"),
                                "--sdf", str(annotation), "--seeds", "4"], 7200)
        yield (f"sdf_{corner}_v4", [*base, "--out", str(out / f"sdf_{corner}_v4"),
                                   "--sdf", str(annotation), *short_v4], 7200)
    yield ("score_matrix", [sys.executable, "code/tests/score_rtl/run_matrix.py",
                            "--repo", str(repo), "--out", str(out / "score_matrix"),
                            "--physical", str(final), "--cells", str(cells),
                            "--rtl-src", str(rtl_src), "--modes", "gates", "typ", "slow", "fast"], 10800)
    for mode, annotation in [("gates", None), *sdf.items()]:
        command = [sys.executable, "code/tests/protocol_campaign/run_campaign.py", "--repo", str(repo),
                   "--out", str(out / f"protocol_{mode}"), "--netlist", str(netlist), "--cells", str(cells)]
        if annotation is not None:
            command.extend(["--sdf", str(annotation)])
        yield f"protocol_{mode}", command, 10800


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True, help="frozen verification inputs")
    parser.add_argument("--physical", type=Path, required=True, help="one harden result directory")
    parser.add_argument("--qualification", type=Path, required=True, help="compare_cfg_split summary")
    parser.add_argument("--rtl-src", type=Path, required=True)
    parser.add_argument("--cells", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--hours", type=float, required=True)
    args = parser.parse_args()
    repo, physical, out = args.repo.resolve(), args.physical.resolve(), args.out.resolve()
    qualification = json.loads(args.qualification.read_text())[physical.name]
    if not qualification["qualified"]:
        parser.error(f"{physical.name} did not pass physical qualification")
    for fixture in (
        "wiki/SPEC_V2_SCORE.md",
        "code/score/examples/spi_mode0_late_sample.score",
        "sim/numerics/v2_sizing/tt_v2_pnr/test/sdf_for_icarus.py",
    ):
        if not (repo / fixture).is_file():
            parser.error(f"missing verification fixture: {fixture}")

    sys.path.insert(0, str(repo / "code/flow/runpod"))
    from verify_v2_pipeline import Pipeline, stamp

    job_specs = list(gate_job_specs(repo, physical / "final", out, args.cells.resolve(), args.rtl_src.resolve()))
    out.mkdir()
    summary = {"design": physical.name, "qualification": qualification, "started": stamp(), "stages": []}
    pipeline = Pipeline(repo, out, summary, args.hours * 3600)

    for name, command, timeout in job_specs:
        pipeline.step(name, command, timeout=timeout)

    passed = all(entry["status"] == "passed" for entry in summary["stages"])
    summary.update(finished=stamp(), status="passed" if passed else "failed")
    pipeline.save()
    (out / "DONE").write_text(summary["status"] + "\n")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
