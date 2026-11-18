"""Verify configuration placement and host writes against the frozen v3 RTL."""
import json
import shutil
import subprocess
import sys
import tarfile
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE.parent / "lockstep_v2"))
from rtl_sources import SRC, rtl_files  # noqa: E402

TOP = "tt_um_brentius_metronome"
FROZEN = ROOT / "data/raw/v4_phase1_20261117/v3_baseline/tt_project.tgz"
SPLIT = ROOT / "data/raw/v4_feature_checked_20261117/split.tgz"


@pytest.fixture(params=("central", "split"))
def bank_rtl(request, tmp_path):
    files, defines = rtl_files(ihp_sram=False)
    if request.param == "central":
        return request.param, SRC, files, defines
    if not SPLIT.is_file():
        pytest.skip("requires the frozen v4 split-bank prototype")
    source = tmp_path / "split_src"
    source.mkdir()
    with tarfile.open(SPLIT) as archive:
        for name in [*(file.name for file in files), "md2_defs.vh", "md2_map.vh"]:
            (source / name).write_bytes(archive.extractfile(f"src/{name}").read())
    return request.param, source, [source / file.name for file in files], defines


@pytest.mark.skipif(not FROZEN.is_file() or not shutil.which("iverilog"),
                    reason="requires frozen v3 inputs and Icarus")
def test_cfg_host_write_matches_v3(tmp_path, bank_rtl):
    _, source, files, defines = bank_rtl
    with tarfile.open(FROZEN) as archive:
        project = archive.extractfile("src/project.v").read().decode()
        bank = archive.extractfile("src/md2_cfg_bank.v").read().decode()
    ref = tmp_path / "frozen_v3.v"
    ref.write_text(project.replace(TOP, "frozen_v3_top").replace("md2_cfg_bank", "frozen_v3_bank")
                   + "\n" + bank.replace("md2_cfg_bank", "frozen_v3_bank"), encoding="utf-8")
    target = tmp_path / "cfg_split.vvp"
    subprocess.run(["iverilog", "-g2012", "-s", "cfg_split_tb", "-I", str(source),
                    *(f"-D{k}={v}" for k, v in defines.items()), "-o", str(target),
                    str(HERE / "cfg_split_tb.v"), str(ref), *map(str, files)],
                   check=True, capture_output=True, text=True)
    run = subprocess.run(["vvp", str(target)], check=True, capture_output=True, text=True)
    assert "PASS 512 addresses" in run.stdout


@pytest.mark.skipif(not shutil.which("yosys"), reason="requires Yosys")
def test_cfg_partition_in_flat_netlist(tmp_path, bank_rtl):
    organization, source, files, _ = bank_rtl
    netlist = tmp_path / "flat.json"
    script = "\n".join([
        "read_verilog -D SYNTHESIS -D USE_IHP_CELLS -D USE_IHP_SRAM -I. "
        + " ".join(p.name for p in files),
        f"hierarchy -top {TOP}", "proc", "flatten", "opt_clean",
        f'write_json "{netlist.as_posix()}"',
    ])
    script_path = tmp_path / "partition.ys"
    script_path.write_text(script, encoding="utf-8")
    run = subprocess.run(["yosys", "-Q", "-s", str(script_path)], cwd=source,
                         capture_output=True, text=True)
    assert run.returncode == 0, run.stdout[-3000:] + run.stderr
    cells = json.loads(netlist.read_text())["modules"][TOP]["cells"]
    latches = {name: c for name, c in cells.items() if c["type"] == "sg13cmos5l_dlhrq_1"}
    assert len(latches) == 2112
    assert all(n.endswith(".u_l") and len(c["connections"]["D"]) == 1
               for n, c in latches.items())
    if organization == "central":
        assert all(name.startswith("u_cfg.") for name in latches)
    else:
        for line in range(4):
            prefix = f"g_ln[{line}].u_cfg_line."
            assert sum(name.startswith(prefix) for name in latches) == 225
            assert sum(name.startswith(prefix) and c["type"] == "sg13cmos5l_lgcp_1"
                       for name, c in cells.items()) == 29
        assert sum(name.startswith("u_cfg_rest.") for name in latches) == 1212
    assert len({c["connections"]["D"][0] for c in latches.values()}) == 8
    assert len({c["connections"]["RESET_B"][0] for c in latches.values()}) == 1
