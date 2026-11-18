"""Build a v4 Phase 1 headroom variant of the v3 Tiny Tapeout tree (NOT FOR TAPEOUT).

    python sim/numerics/v4_headroom/make_variant.py --stages 8 --out build/v4p1/b8 [--set PL_TARGET_DENSITY_PCT=55]
        [--macros alt1] [--tgz build/v4p1/b8.tgz]

Source: the exact v3 hardened tree, data/raw/v4_phase1_20261117/v3_baseline/tt_project.tgz (same bytes as the
v3r1_20261116T1655 run input; src/ identical to the working tree on 2026-11-17).

Ballast (stages > 0): md2_ballast, D stages of 32 flops with XOR/AND/OR mixing, fed from the MISR digest input and
reduced to one registered bit. That bit is ANDed with bal_en (host MCTL bit 7, written with men, 0 after reset, not
read anywhere else) and XORed into MISR digest bit 22, which is 0 in v3. With bal_en = 0 the chip behaves exactly as
v3; synthesis cannot prove bal_en constant, so the ballast is kept. stages = 0 gives the unmodified tree.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / "data/raw/v4_phase1_20261117/v3_baseline/tt_project.tgz"

BALLAST = r"""
// ---------------------------------------------------------------------------------------------------------------
// v4 Phase 1 headroom ballast (sim/numerics/v4_headroom/make_variant.py). NOT FOR TAPEOUT: area probe only.
`default_nettype none
module md2_ballast #(parameter integer D = 1) (
    input  wire        clk,
    input  wire [31:0] din,
    output reg         y
);
    function [31:0] mix(input [31:0] a);
        mix = a ^ ({a[30:0], a[31]} & {a[26:0], a[31:27]}) ^ ({a[28:0], a[31:29]} | {a[20:0], a[31:21]})
                ^ {a[24:0], a[31:25]};
    endfunction
    wire [32*D-1:0] s;
    genvar i;
    generate
        for (i = 0; i < D; i = i + 1) begin : g_st
            reg [31:0] q;
            wire [31:0] prev = (i == 0) ? din : s[32*(i-1) +: 32];
            always @(posedge clk) q <= mix(prev) ^ {q[0], q[31:1]};
            assign s[32*i +: 32] = q;
        end
    endgenerate
    always @(posedge clk) y <= ^s[32*(D-1) +: 32];
endmodule
`default_nettype wire
"""

def patch_project(text: str, stages: int) -> str:
    def sub(old, new):
        nonlocal text
        assert text.count(old) == 1, old
        text = text.replace(old, new)

    sub("^ {10'd0, o_oe, o_out};", "^ {9'd0, bal_y & bal_en, o_oe, o_out};")
    sub("    wire err = conflict", "    // v4 phase-1 ballast (NOT FOR TAPEOUT)\n    reg bal_en;\n    wire bal_y;\n"
        f"    md2_ballast #(.D({stages})) u_ballast (.clk(clk), .din(misr ^ {{10'd0, o_oe, o_out}}), .y(bal_y));\n"
        "    wire err = conflict")
    sub("            dc <= 19'd0;\n        end else begin", "            dc <= 19'd0; bal_en <= 1'b0;\n        end else begin")
    sub("            if (d_wr_mctl) men <= h_wd[0];", "            if (d_wr_mctl) men <= h_wd[0];\n"
        "            if (d_wr_mctl) bal_en <= h_wd[7];")
    return text + BALLAST


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--stages", type=int, required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--tgz", type=Path)
    ap.add_argument("--set", action="append", default=[], help="config.json KEY=JSON_VALUE (top-level)")
    ap.add_argument("--macro", action="append", default=[], help="INSTANCE=X,Y,ORIENT macro placement override")
    a = ap.parse_args()
    out = a.out.resolve()
    if out.exists():
        shutil.rmtree(out)
    out.mkdir(parents=True)
    with tarfile.open(BASE) as tar:
        tar.extractall(out, filter="data")
    if a.stages:
        p = out / "src/project.v"
        p.write_text(patch_project(p.read_text(), a.stages), newline="\n")
    cfg_path = out / "src/config.json"
    cfg_text = cfg_path.read_text()
    for kv in a.set:
        key, val = kv.split("=", 1)
        try:
            val = json.loads(val)
        except json.JSONDecodeError:   # bare string (shell quoting stripped)
            pass
        pat = re.compile(r'^(\s*)"%s":\s*[^\n]*?(,?)$' % re.escape(key), re.M)
        if pat.search(cfg_text):
            cfg_text, n = pat.subn(lambda m: f'{m.group(1)}"{key}": {json.dumps(val)}{m.group(2)}', cfg_text)
            assert n == 1, key
        else:   # new key: insert before the closing brace of the top-level object
            cfg_text = cfg_text.rstrip()
            assert cfg_text.endswith("}")
            cfg_text = cfg_text[:-1].rstrip() + f',\n  "{key}": {json.dumps(val)}\n}}\n'
    for spec in a.macro:
        inst, rest = spec.split("=", 1)
        x, y, orient = rest.split(",")
        pat = re.compile(r'("%s": \{ "location": )\[[^\]]*\], "orientation": "[A-Z]+"' % re.escape(inst))
        cfg_text, n = pat.subn(lambda m: f'{m.group(1)}[{float(x)}, {float(y)}], "orientation": "{orient}"', cfg_text)
        assert n == 1, inst
    cfg_path.write_text(cfg_text, newline="\n")
    json.loads("\n".join(l for l in cfg_text.splitlines()))   # still valid JSON
    if a.tgz:
        a.tgz.parent.mkdir(parents=True, exist_ok=True)
        with tarfile.open(a.tgz, "w:gz") as tar:
            for f in sorted(out.rglob("*")):
                if f.is_file():
                    tar.add(f, arcname=f.relative_to(out).as_posix())
    print("variant", out, "stages", a.stages, "set", a.set, "macro", a.macro)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
