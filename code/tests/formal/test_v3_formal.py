"""v3 formal checks (wiki/SPEC_V2.md 12.3, 12.4): v3_freeze.sby proves, by k-induction, that a frozen cycle holds
md2_stream (S0 instance, with capture) and md2_mem state apart from the RAM landing capture, that only the host is
served while frozen, and the capture push/overflow rules. Each planted mutant of the RTL must make the proof fail.

    python -m pytest code/tests/formal/test_v3_formal.py -v      (OSS CAD Suite with sby, slang plugin, bitwuzla)
"""
import os
import shutil
import subprocess
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
SRC = HERE.parents[2] / "src"

MUTANTS = {   # name: (file, original text, mutated text)
    "stream_no_freeze_hold": ("md2_stream.v", "            if (frz) begin", "            if (1'b0) begin"),
    "mem_pointer_lands_twice": ("md2_mem.v", "if (land & ~frzd) p_dat", "if (land) p_dat"),
    "capture_pos_plus_1": ("md2_stream.v", "pos <= pos + 12'd4; end", "pos <= pos + 12'd1; end"),
    "mem_serves_stream_frozen": ("md2_mem.v", "wire gs0 = s_req[0] & ~frz;", "wire gs0 = s_req[0];"),
}


def _env():
    env = dict(os.environ)
    root = env.get("OSS_CAD_SUITE", str(Path.home() / "tools" / "oss-cad-suite"))
    bindir = Path(root) / "bin"
    if bindir.is_dir():
        env["PATH"] = os.pathsep.join([str(bindir), str(Path(root) / "lib"), env.get("PATH", "")])
    return env


def _sby(sby_text, work, task, env):
    sby = shutil.which("sby", path=env["PATH"])
    if sby is None:
        pytest.skip("sby (OSS CAD Suite) not found")
    f = work / "v3.sby"
    work.mkdir(parents=True, exist_ok=True)
    f.write_text(sby_text)
    p = subprocess.run([sby, "-f", "-d", str(work / task), str(f), task], cwd=work, env=env, capture_output=True,
                       text=True, timeout=900)
    return p.returncode, p.stdout + p.stderr


def _prepare(work, mutant=None):
    """Copy the two RTL files (one possibly mutated) and the properties into a work directory without spaces."""
    work.mkdir(parents=True, exist_ok=True)
    for f in ("md2_stream.v", "md2_mem.v"):
        txt = (SRC / f).read_text()
        if mutant and mutant[0] == f:
            assert txt.count(mutant[1]) == 1, (f, mutant[1])
            txt = txt.replace(mutant[1], mutant[2])
        (work / f).write_text(txt)
    shutil.copy(HERE / "fv_v3_freeze.sv", work / "fv_v3_freeze.sv")
    return (HERE / "v3_freeze.sby").read_text().replace("../../../src/", "")


@pytest.mark.parametrize("task", ["prove", "cover"])
def test_v3_freeze(task, tmp_path):
    rc, out = _sby(_prepare(tmp_path), tmp_path, task, _env())
    assert rc == 0 and "DONE (PASS" in out, out[-2000:]


@pytest.mark.parametrize("name", list(MUTANTS))
def test_v3_freeze_mutant_rejected(name, tmp_path):
    rc, out = _sby(_prepare(tmp_path, MUTANTS[name]), tmp_path, "prove", _env())
    assert "summary: successful proof" not in out and "failed assertion" in out, out[-1500:]
    assert rc != 0 and "DONE (PASS" not in out, f"mutant {name} survived the proof"
