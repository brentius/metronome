"""RTL mutation check for the v3 lockstep scenarios: each mutant of a copy of src/ must fail the named scenario.

    python code/tests/lockstep_v2/mutate_v3.py [--log FILE]       (OSS CAD Suite environment, iverilog + cocotb)

A mutant that passes its scenario is a gap in the scenario, reported as SURVIVED (exit status 1).
"""
from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

MUTANTS = [   # (name, file, original, mutated, scenario)
    ("live_pin_swapped", "project.v", "obind[3] ? l_pina[ln]", "obind[3] ? l_pinb[ln]", "v3_live_misr"),
    ("misr_poly", "project.v", "localparam [31:0] MISR_POLY = 32'h04C11DB7;",
     "localparam [31:0] MISR_POLY = 32'h04C11DB6;", "v3_live_misr"),
    ("freeze_pins_not_held", "project.v", "else if (!frz) o_out[k] <= lut[idx];", "else o_out[k] <= lut[idx];",
     "v3_freeze"),
    ("step_ignored", "project.v", "frz <= h_wd[0] & ~h_wd[1];", "frz <= h_wd[0];", "v3_freeze"),
    ("ir_not_held", "md2_core.v", "if (!frz) ir <= rdata;", "ir <= rdata;", "v3_freeze"),
    ("ecap_dc_restart_0", "project.v", "else if (cev)               dc <= 19'd1;",
     "else if (cev)               dc <= 19'd0;", "v3_ecap"),
    # review follow-up (v3_freeze2)
    ("p_dat_no_frzd", "md2_mem.v", "if (land & ~frzd) p_dat", "if (land) p_dat", "v3_freeze2"),
    ("p_dat_gated_frz", "md2_mem.v", "if (land & ~frzd) p_dat", "if (land & ~frz) p_dat", "v3_freeze2"),
    ("misr_on_freeze", "project.v", "else if (men & ~frz)     misr", "else if (men)           misr", "v3_freeze2"),
    ("misr_not_on_step", "project.v", "else if (men & ~frz)     misr", "else if (men & ~frz & ~frzd) misr",
     "v3_freeze2"),
    ("dc_not_cleared_by_ectl", "project.v", "if (d_wr_ectl) dc <= 19'd0;", "if (1'b0) dc <= 19'd0;", "v3_freeze2"),
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--log", type=Path)
    ap.add_argument("--only", nargs="*")
    a = ap.parse_args()
    lines, bad = [], 0
    for name, fn, old, new, scn in MUTANTS:
        if a.only and name not in a.only:
            continue
        with tempfile.TemporaryDirectory() as td:
            dst = Path(td) / "src"
            shutil.copytree(ROOT / "src", dst)
            txt = (dst / fn).read_text()
            assert txt.count(old) == 1, (name, old)
            (dst / fn).write_text(txt.replace(old, new))
            env = dict(os.environ, RTL_V2_SRC=str(dst), LOCKSTEP_TAG=f"_mut_{name}")
            node = f"{(HERE / 'test_lockstep_v2.py').as_posix()}::test_lockstep[{scn}]"
            p = subprocess.run([sys.executable, "-m", "pytest", node, "-q"], cwd=ROOT, env=env, capture_output=True,
                               text=True)
            killed = p.returncode != 0 and "1 failed" in p.stdout
            bad += not killed
            msg = f"{name:24s} {scn:14s} {'KILLED' if killed else 'SURVIVED'}"
            print(msg, flush=True)
            lines.append(msg)
            shutil.rmtree(HERE / f"sim_build_mut_{name}", ignore_errors=True)
    if a.log:
        a.log.write_text("\n".join(lines) + "\n")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
