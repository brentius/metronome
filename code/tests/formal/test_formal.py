"""Runs every SymbiYosys proof (and its cover sanity task) in this directory. Skips if sby is not installed.

Run: python -m pytest code/tests/formal -v   (after `source code/tools/env.sh`, or with OSS_CAD_SUITE set)
Each proof uses the smtbmc engine with bitwuzla; a PASS for a `prove` task is a k-induction proof (unbounded);
a PASS for a `cover` task shows the interesting events are reachable (the proofs are not vacuous).
"""
import os
import shutil
import subprocess
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
SUITE = [
    ("beatgen", ["prove", "cover"]),
    ("wgroup", ["prove", "cover"]),
    ("movebus", ["prove"]),
    ("ptrs", ["prove", "cover"]),
    ("engine", ["prove", "cover"]),
    ("lfsr", ["prove", "cover"]),
    ("acc", ["prove", "cover"]),
    ("core", ["prove", "cover"]),
]
CASES = [(unit, task) for unit, tasks in SUITE for task in tasks]


def _env():
    env = dict(os.environ)
    root = env.get("OSS_CAD_SUITE", str(Path.home() / "tools" / "oss-cad-suite"))
    bindir = Path(root) / "bin"
    if bindir.is_dir():
        env["PATH"] = os.pathsep.join([str(bindir), str(Path(root) / "lib"), env.get("PATH", "")])
    return env


@pytest.mark.parametrize("unit,task", CASES, ids=[f"{u}-{t}" for u, t in CASES])
def test_sby(unit, task, tmp_path):
    env = _env()
    sby = shutil.which("sby", path=env["PATH"])
    if sby is None:
        pytest.skip("sby (OSS CAD Suite) not found")
    work = tmp_path / f"{unit}_{task}"
    proc = subprocess.run([sby, "-f", "-d", str(work), str(HERE / f"{unit}.sby"), task],
                          cwd=HERE, env=env, capture_output=True, text=True, timeout=600)
    tail = "\n".join((proc.stdout + proc.stderr).splitlines()[-12:])
    assert proc.returncode == 0 and "DONE (PASS" in proc.stdout, tail
