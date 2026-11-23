"""Check the chip-top operation strobes against `Metronome/Strobes.lean`.

SPEC_V2 §6 resolves the six moves to one winner per write group; `project.v`
then turns each winner's destination into the per-unit operation strobes with the
`hits` / `dsteq` / `OPG` macros, the pointer's port select `p_sel`, the line
symbol operation `sop`, the stream control glue (§6.3, §13.2) and the `DBG`
register write strobes (§12.4, §13.1).  The unit, memory, line, stream and debug
Lean cuts take those strobes as free per-cycle leaves; this module closes them.

It re-elaborates the chip top with `verify.py`'s Yosys recipe and, from the
actual cells, extracts:

* `OPG(G, D) = |(HITG(G) & dsteq(c_dst, D))` for all 22 unit strobes: the six
  counter `LO`/`HI`, the eight LFSR `ST`/`B0..B2`, the two shifter `SH` and the
  six stream `CTL`/`ADV`/`RX`;
* the accumulator's hit mask `HITG(DG_ACC)`, so its `OneHotOrZero` premise is
  discharged;
* the counter, LFSR and shifter selector encodings, the pointer `p_sel`, the
  line `sop` and the six accumulator op-code slices;
* the stream `rewind`/`flush`/`clr_starved` merge of move and host writes, and
  `cap_en = cen & ~replay`;
* the `DBG` write strobes `h_* | (cw_drain & (cw_dbg_off == offset))` with the
  `cw_dbg_off` subtraction.

It emits Lean that proves each extracted cone equal to the independent
specification, and the generated theorems compose with `Metronome.Moves`' pick
(`opg_eq_pick`: the strobe is `(pickWord …).we && dst == D`) and with
`Metronome.Units`' unit cuts.

Run it from the repository root:

    python lean/strobes_check.py
    python lean/strobes_check.py --mutations

`run_mutations()` plants eight regressions on temporary copies of `src/` (never
the repository).  Each must be rejected by the generated Lean or by a
fail-closed structural check.
"""

import argparse
from collections import OrderedDict
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile

from rtlil import UnsupportedRTL, require
from verify import HERE, ROOT, TOP, run
import corectl_check as corectl
import moves_check as moves
import units_check


DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_strobes_v4_20261121"
TEMPLATE = HERE / "StrobesEquivalence.lean.in"
STROBES_LEAN = HERE / "Metronome" / "Strobes.lean"
AXIOM_LINE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)
NO_AXIOM_LINE = re.compile(r"^'([^']+)' does not depend on any axioms$", re.MULTILINE)

# The move bus bound free by every `OPG` cone.
OPG_FREE = (("mv_en", 6, "en"), ("grp_v", 30, "grp"), ("c_dst", 36, "dst"),
            ("c_dat", 48, "dat"))

# Documented constants of the generated headers.  `key` also names the Lean
# abbreviation the theorem compares against (`dg_cnt0` -> `dgCnt0`).
PARAMS = (
    "dg_acc", "dg_sh0", "dg_sh1", "dg_cnt0", "dg_cnt1", "dg_cnt2",
    "dg_lf0", "dg_lf1", "dg_p0", "dg_s0", "dg_s1",
    "d_l_sym", "d_l_dbit",
    "d_sh0_sh", "d_sh1_sh",
    "d_cnt0_lo", "d_cnt0_hi", "d_cnt1_lo", "d_cnt1_hi", "d_cnt2_lo", "d_cnt2_hi",
    "d_lf0_st", "d_lf1_st", "d_lf0_b0", "d_lf0_b1", "d_lf0_b2", "d_lf0_b3",
    "d_lf1_b0", "d_lf1_b1", "d_lf1_b2", "d_lf1_b3",
    "d_p0_al", "d_p0_ah", "d_p0_w", "d_p0_r",
    "d_s0_adv", "d_s1_adv", "d_s0_rx", "d_s1_rx", "d_s0_ctl", "d_s1_ctl",
)

STREAM_DECODE = (
    ("ha_srt_base", r"localparam \[15:0\] HA_SRT_BASE = 16'h([0-9A-Fa-f]+);", 16),
    ("hs_srt", r"localparam integer HS_SRT = (\d+);", 10),
    ("hspan_srt", r"localparam \[15:0\] HSPAN_SRT = 16'h([0-9A-Fa-f]+);", 16),
    ("ho_srt_ctl", r"localparam integer HO_SRT_CTL = (\d+);", 10),
    ("ha_dbg_base", r"localparam \[15:0\] HA_DBG_BASE = 16'h([0-9A-Fa-f]+);", 16),
    ("ho_ectl", r"localparam integer HO_DBG_ECTL = (\d+);", 10),
    ("ho_emask", r"localparam integer HO_DBG_EMASK = (\d+);", 10),
    ("ho_rlv", r"localparam integer HO_DBG_RLV = (\d+);", 10),
)


class StrobesRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated strobes."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


def lean_name(key):
    """`dg_cnt0` -> `dgCnt0`, `d_cnt0_lo` -> `dCnt0Lo`."""
    head, _, rest = key.partition("_")
    return head if not rest else head + "".join(
        part[:1].upper() + part[1:] for part in rest.split("_"))


def elaborate(snapshot, work, yosys):
    return corectl.elaborate(snapshot, work, yosys)


def snapshot_of(directory):
    return corectl.snapshot_of(directory)


def load_modules(rtlil_or_json):
    return corectl.load_modules(rtlil_or_json)


def net(top, name, width):
    return corectl.net(top, name, width)


def intrail(top, entry):
    """The bits of an OPG root: a named net or a cell port."""
    if "net" in entry:
        return net(top, entry["net"], 1)
    cell = top["cells"].get(entry["cell"])
    require(cell is not None, f"{TOP}.{entry['cell']}: missing instance")
    bits = tuple(cell["connections"][entry["pin"]])
    require(len(bits) == 1, f"{TOP}.{entry['cell']}.{entry['pin']}: expected one bit")
    return bits


def entry_label(entry):
    """The elaborated net or instance port an OPG strobe is read from."""
    return entry["net"] if "net" in entry else f"{entry['cell']}.{entry['pin']}"


def strobes_params(snapshot):
    """Read the destination and group codes and the stream/DBG decode constants."""
    text = "".join(snapshot[name].decode("latin-1") for name in sorted(snapshot)
                   if name.endswith(".vh"))
    values = {}
    for key in PARAMS:
        header = key.upper()
        width = 5 if key.startswith("dg_") else 6
        pattern = rf"localparam \[{width - 1}:0\] {header} = {width}'d(\d+);"
        match = re.search(pattern, text)
        require(match is not None, f"{header}: constant pattern changed in the headers")
        values[key] = int(match.group(1), 10)
    for key, pattern, base in STREAM_DECODE:
        match = re.search(pattern, text)
        require(match is not None, f"{key}: constant pattern changed in the headers")
        values[key] = int(match.group(1), base)
    require(values["hs_srt"] == 4, "HS_SRT is not 4")
    require(values["hspan_srt"] == 8, "HSPAN_SRT is not 8 bytes")
    require(values["ho_srt_ctl"] == 2, "HO_SRT_CTL is not 2")
    require(values["ha_srt_base"] + values["hspan_srt"] <= 0x10000,
            "the SRT window leaves the address space")
    require(values["ho_ectl"] == 2 and values["ho_emask"] == 8 and
            values["ho_rlv"] == 18, "the DBG byte offsets are not 2/8/18")
    require(values["ha_dbg_base"] == 0x2460, "HA_DBG_BASE is not 0x2460")
    # Distinct destination codes are what makes the op strobes exclusive.
    for lo, hi in (("d_cnt0_lo", "d_cnt0_hi"), ("d_cnt1_lo", "d_cnt1_hi"),
                   ("d_cnt2_lo", "d_cnt2_hi")):
        require(values[lo] != values[hi], f"{lo} and {hi} are the same code")
    return values


def opg_units():
    """Every `OPG` strobe of the chip top, in elaborated-instance order."""
    units = []
    for k in range(3):
        units.append({"net": f"g_cn[{k}].op_lo", "name": f"rtlOpgCnt{k}Lo",
                      "group": f"dg_cnt{k}", "dest": f"d_cnt{k}_lo",
                      "label": f"counter {k} LO"})
        units.append({"net": f"g_cn[{k}].op_hi", "name": f"rtlOpgCnt{k}Hi",
                      "group": f"dg_cnt{k}", "dest": f"d_cnt{k}_hi",
                      "label": f"counter {k} HI"})
    for k in range(2):
        for op in ("st", "b0", "b1", "b2"):
            units.append({"net": f"g_lf[{k}].op_{op}", "name": f"rtlOpgLf{k}{op.upper()[0]}{op[1:]}",
                          "group": f"dg_lf{k}", "dest": f"d_lf{k}_{op}",
                          "label": f"LFSR {k} {op.upper()}"})
    for k in range(2):
        units.append({"cell": f"g_sh[{k}].u", "pin": "sel", "name": f"rtlOpgSh{k}Sh",
                      "group": f"dg_sh{k}", "dest": f"d_sh{k}_sh",
                      "label": f"shifter {k} SH"})
    for k in range(2):
        units.append({"net": f"g_s[{k}].mctl", "name": f"rtlOpgS{k}Ctl",
                      "group": f"dg_s{k}", "dest": f"d_s{k}_ctl",
                      "label": f"stream {k} CTL"})
        units.append({"cell": f"g_s[{k}].u", "pin": "adv", "name": f"rtlOpgS{k}Adv",
                      "group": f"dg_s{k}", "dest": f"d_s{k}_adv",
                      "label": f"stream {k} ADV"})
        units.append({"cell": f"g_s[{k}].u", "pin": "rx_we", "name": f"rtlOpgS{k}Rx",
                      "group": f"dg_s{k}", "dest": f"d_s{k}_rx",
                      "label": f"stream {k} RX"})
    return units


def free_bits(top, frees):
    return {bit for name, _, _ in frees for bit in top["netnames"][name]["bits"]}


def extract_cone(top, name, roots, frees):
    cone = corectl.VectorCone(name, top)
    for leaf, bits, value in frees:
        cone.overwrite(leaf, bits, value)
    return cone, {root: cone.expression(bits) for root, bits in roots}


def check_cw_dbg_off(modules, params):
    """`cw_dbg_off` is the zero-extended queued address minus `HA_DBG_BASE`."""
    top = modules[TOP]
    bits = net(top, "cw_dbg_off", 32)
    cone = corectl.VectorCone("dbgoff", top)
    cone.overwrite("cw_pending_addr", 16, "addr")
    cells = corectl.cone_of(modules, top, bits)
    subs = [cell for cell in cells if cell["type"] == "$sub"]
    require(len(subs) == 1, "cw_dbg_off: expected one subtraction")
    sub = subs[0]
    address = net(top, "cw_pending_addr", 16)
    require(tuple(sub["connections"]["A"]) == address + ("0",) * 16,
            "cw_dbg_off: the subtraction does not zero-extend cw_pending_addr")
    value = corectl.cell_value(sub["connections"]["B"])
    require(value == params["ha_dbg_base"],
            f"cw_dbg_off: base 0x{value:04X} is not HA_DBG_BASE")
    expression = cone.expression(bits)
    return {"lines": list(cone.lines), "expr": expression,
            "base": value}


def extract_opg(modules, params):
    """The 22 `OPG` strobes with their documented group comparators."""
    top = modules[TOP]
    stops = free_bits(top, OPG_FREE)
    strobes = []
    for entry in opg_units():
        bits = intrail(top, entry)
        group = moves.word_groups(modules, bits, stops)
        require(group == params[entry["group"]],
                f"{entry_label(entry)}: group {group} is not "
                f"{entry['group']} = {params[entry['group']]}")
        cone, expressions = extract_cone(top, entry["name"].lower(), [(entry["name"], bits)],
                                         OPG_FREE)
        strobes.append({**entry, "lines": list(cone.lines),
                        "expr": expressions[entry["name"]], "group_code": group})
    return strobes


def extract_acc_hit(modules, params):
    """`HITG(DG_ACC)` as a function of the move bus."""
    top = modules[TOP]
    bits = net(top, "acc_hit", 6)
    stops = free_bits(top, OPG_FREE)
    group = moves.word_groups(modules, bits, stops)
    require(group == params["dg_acc"], f"acc_hit: group {group} is not DG_ACC")
    cone, expressions = extract_cone(top, "acchit", [("acc_hit", bits)], OPG_FREE)
    return {"lines": list(cone.lines), "expr": expressions["acc_hit"]}


def extract_units(modules, params):
    """The counter/LFSR selector muxes, `p_sel`, the line `sop` and `acc_sel6`."""
    top = modules[TOP]
    info = {"counter_sel": [], "lfsr_sel": [], "sop": [], "acc_sel": []}
    for k in range(3):
        frees = ((f"g_cn[{k}].op_lo", 1, "opLo"), (f"g_cn[{k}].op_hi", 1, "opHi"))
        cone, expressions = extract_cone(
            top, f"selcn{k}", [(f"g_cn[{k}].sel", net(top, f"g_cn[{k}].sel", 2))], frees)
        info["counter_sel"].append({"lines": list(cone.lines),
                                    "expr": expressions[f"g_cn[{k}].sel"]})
    for k in range(2):
        names = tuple(f"g_lf[{k}].op_{op}" for op in ("st", "b0", "b1", "b2"))
        frees = tuple((name, 1, value) for name, value in
                      zip(names, ("opSt", "opB0", "opB1", "opB2")))
        cone, expressions = extract_cone(
            top, f"sellf{k}", [(f"g_lf[{k}].sel", net(top, f"g_lf[{k}].sel", 3))], frees)
        info["lfsr_sel"].append({"lines": list(cone.lines),
                                 "expr": expressions[f"g_lf[{k}].sel"]})

    w_p0 = net(top, "w_p0", 15)
    cone, expressions = extract_cone(top, "psel", [("p_sel", net(top, "p_sel", 2))],
                                     (("w_p0", 15, "w"),))
    codes = moves.comparators(modules, top, net(top, "p_sel", 2),
                              free_bits(top, (("w_p0", 15, "w"),)), w_p0[8:14], 6)
    require(codes == {params["d_p0_al"], params["d_p0_ah"], params["d_p0_w"]},
            f"p_sel: destination comparators are {sorted(codes)}")
    info["p_sel"] = {"lines": list(cone.lines), "expr": expressions["p_sel"]}

    for k in range(4):
        ws = net(top, f"g_ln[{k}].ws", 15)
        cone, expressions = extract_cone(
            top, f"sop{k}", [(f"g_ln[{k}].sop", net(top, f"g_ln[{k}].sop", 2))],
            ((f"g_ln[{k}].ws", 15, "ws"),))
        codes = moves.comparators(modules, top, net(top, f"g_ln[{k}].sop", 2),
                                  free_bits(top, ((f"g_ln[{k}].ws", 15, "ws"),)),
                                  ws[8:14], 6)
        require(codes == {params["d_l_sym"], params["d_l_dbit"]},
                f"g_ln[{k}].sop: destination comparators are {sorted(codes)}")
        info["sop"].append({"lines": list(cone.lines),
                            "expr": expressions[f"g_ln[{k}].sop"]})

    for slot in range(6):
        lets, expr = units_check.extract_acc_sel(modules, slot)
        info["acc_sel"].append({"lines": lets.splitlines(), "expr": expr})
    return info


def extract_control(modules, params):
    """The stream control merge, `cap_en` and the `DBG` write strobes."""
    top = modules[TOP]
    info = {"streams": []}
    for k in range(2):
        leaves = ((f"g_s[{k}].w", 15, "w"), (f"g_s[{k}].mctl", 1, "mctl"),
                  ("w_srt", 1, "wSrt"), ("a_srt", 16, "aSrt"), ("h_wd", 8, "hd"))
        roots = {}
        for pin in ("rewind", "flush", "clr_starved"):
            bits = tuple(top["cells"][f"g_s[{k}].u"]["connections"][pin])
            cone, expressions = extract_cone(top, f"ctl{k}{pin[:1]}", [(pin, bits)], leaves)
            roots[pin] = {"lines": list(cone.lines), "expr": expressions[pin]}
        info["streams"].append(roots)

    cap = []
    for k in range(2):
        bits = tuple(top["cells"][f"g_s[{k}].u"]["connections"]["cap_en"])
        cone, expressions = extract_cone(
            top, f"cap{k}", [(f"{k}.cap", bits)],
            (("cen", 1, "cen"), ("replay", 1, "replay")))
        cap.append({"lines": list(cone.lines), "expr": expressions[f"{k}.cap"]})
    info["cap"] = cap

    dbg = []
    w_dbg = net(top, "w_dbg", 1)
    a_dbg = net(top, "a_dbg", 16)
    cw_drain = net(top, "cw_drain", 1)
    cw_addr = net(top, "cw_pending_addr", 16)
    for name, key in (("d_wr_ectl", "ectl"), ("d_wr_em0", "em0"), ("d_wr_em1", "em1"),
                      ("d_wr_rlv0", "rlv0"), ("d_wr_rlv1", "rlv1")):
        cone, expressions = extract_cone(
            top, f"dbg{key}", [(name, net(top, name, 1))],
            (("w_dbg", 1, "wDbg"), ("a_dbg", 16, "aDbg"), ("cw_drain", 1, "drain"),
             ("cw_pending_addr", 16, "addr")))
        dbg.append({"name": name, "lean": f"rtlDbg{key[:1].upper()}{key[1:]}",
                    "lines": list(cone.lines), "expr": expressions[name]})
    info["dbg"] = dbg
    info["dbg_off"] = check_cw_dbg_off(modules, params)
    return info


# The five DBG byte offsets of the generated Lean definitions.
DBG_BYTES = (("Ectl", "hoDbgEctl"), ("Em0", "hoDbgEmask"),
             ("Em1", "hoDbgEmaskPlus1"), ("Rlv0", "hoDbgRlv"),
             ("Rlv1", "hoDbgRlvPlus1"))


def indent(text, prefix="  "):
    lines = text.splitlines() if isinstance(text, str) else text
    return "\n".join(prefix + line for line in lines)


def lean_opg(info):
    blocks = []
    for entry in info["strobes"]:
        blocks.append(f"""/-- `{entry_label(entry)}`: the {entry['label']} strobe. -/
def {entry['name']} (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) : Bool :=
{indent(entry['lines'])}
  {entry['expr']}

/-- `{entry['name']}` is `OPG({entry['group']}, {entry['dest']})`: the group's winner writes
`{entry['dest']}`. -/
theorem {entry['name']}_spec (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) :
    {entry['name']} en grp dst = opg en grp dst {lean_name(entry['group'])} {lean_name(entry['dest'])} := by
  simp only [{entry['name']}, opg, dsteqMask, hitsMask, bits6, hitAt, slice, bitAt,
    {lean_name(entry['group'])}, {lean_name(entry['dest'])}]
  bv_decide""")
    acc = info["acc"]
    blocks.append(f"""/-- `acc_hit`: the accumulator group's hit mask `HITG(DG_ACC)`. -/
def rtlAccHit (en : BitVec 6) (grp : BitVec 30) : BitVec 6 :=
{indent(acc['lines'])}
  {acc['expr']}

/-- The extracted hit mask is `hitsMask` of the accumulator group. -/
theorem rtlAccHit_spec (en : BitVec 6) (grp : BitVec 30) :
    rtlAccHit en grp = hitsMask en grp dgAcc := by
  simp only [rtlAccHit, hitsMask, bits6, hitAt, bitAt, slice, dgAcc]
  bv_decide

/-- **The Units cut's accumulator premise.**  `acc_hit` is zero or one-hot, so
`Metronome.Units.Acc.rtlStep_eq_step`'s `OneHotOrZero input.hit` holds of the
elaborated net for every move bus. -/
theorem rtlAccHit_oneHotOrZero (en : BitVec 6) (grp : BitVec 30) :
    Metronome.Units.Acc.OneHotOrZero (rtlAccHit en grp) := by
  rw [rtlAccHit_spec]
  exact accHit_oneHotOrZero en grp""")
    for k in range(2):
        blocks.append(f"""/-- The shifter-{k} selector is the `SH` strobe of the group winner. -/
theorem rtlSelSh{k}_spec (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) :
    shifterSel (rtlOpgSh{k}Sh en grp dst) = shifterSel (opg en grp dst dgSh{k} dSh{k}Sh) := by
  rw [rtlOpgSh{k}Sh_spec]""")
    for k in range(3):
        blocks.append(f"""/-- The counter-{k} selector from its `LO`/`HI` strobes. -/
theorem counterSel{k}_ops (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) :
    counterSel (opg en grp dst dgCnt{k} dCnt{k}Lo) (opg en grp dst dgCnt{k} dCnt{k}Hi) =
      (if opg en grp dst dgCnt{k} dCnt{k}Lo then (0 : BitVec 2)
       else if opg en grp dst dgCnt{k} dCnt{k}Hi then 1 else 2) :=
  counterSel_of_opg en grp dst dgCnt{k} dCnt{k}Lo dCnt{k}Hi

/-- The counter-{k} `LO` and `HI` strobes never fire together. -/
theorem counterSel{k}_exclusive (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) :
    (opg en grp dst dgCnt{k} dCnt{k}Lo && opg en grp dst dgCnt{k} dCnt{k}Hi) = false := by
  apply counter_ops_exclusive
  decide""")
    for k in range(2):
        blocks.append(f"""/-- The LFSR-{k} selector from its four strobes. -/
theorem lfsrSel{k}_ops (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) :
    lfsrSel (opg en grp dst dgLf{k} dLf{k}St) (opg en grp dst dgLf{k} dLf{k}B0)
        (opg en grp dst dgLf{k} dLf{k}B1) (opg en grp dst dgLf{k} dLf{k}B2) =
      (if opg en grp dst dgLf{k} dLf{k}St then (0 : BitVec 3)
       else if opg en grp dst dgLf{k} dLf{k}B0 then 1
       else if opg en grp dst dgLf{k} dLf{k}B1 then 2
       else if opg en grp dst dgLf{k} dLf{k}B2 then 3 else 4) :=
  lfsrSel_of_opg en grp dst dgLf{k} dLf{k}St dLf{k}B0 dLf{k}B1 dLf{k}B2

/-- `ST` and `B0` of the LFSR-{k} never fire together (nor any other pair). -/
theorem lfsrSel{k}_exclusive (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) :
    (opg en grp dst dgLf{k} dLf{k}St && opg en grp dst dgLf{k} dLf{k}B0) = false := by
  apply lfsr_ops_exclusive
  decide""")
    names = ["rtlAccHit_spec", "rtlAccHit_oneHotOrZero"]
    names += [entry["name"] + "_spec" for entry in info["strobes"]]
    names += [f"rtlSelSh{k}_spec" for k in range(2)]
    names += [f"counterSel{k}_ops" for k in range(3)] + \
             [f"counterSel{k}_exclusive" for k in range(3)]
    names += [f"lfsrSel{k}_ops" for k in range(2)] + \
             [f"lfsrSel{k}_exclusive" for k in range(2)]
    return "\n\n".join(blocks), names


def lean_units(info):
    blocks = []
    for k, sel in enumerate(info["counter_sel"]):
        blocks.append(f"""/-- The counter-{k} `sel` mux from `opLo`/`opHi`. -/
def rtlSelCn{k} (opLo opHi : Bool) : BitVec 2 :=
{indent(sel['lines'])}
  {sel['expr']}

/-- The elaborated counter-{k} mux is the documented `LO`/`HI`/`DEC` map. -/
theorem rtlSelCn{k}_spec (opLo opHi : Bool) :
    rtlSelCn{k} opLo opHi = counterSel opLo opHi := by
  simp only [rtlSelCn{k}, counterSel, Metronome.Units.Counter.selOf]

/-- The counter-{k} selector of the group winner's destination. -/
theorem rtlSelCn{k}_opg (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) :
    rtlSelCn{k} (opg en grp dst dgCnt{k} dCnt{k}Lo) (opg en grp dst dgCnt{k} dCnt{k}Hi) =
      counterSel (opg en grp dst dgCnt{k} dCnt{k}Lo) (opg en grp dst dgCnt{k} dCnt{k}Hi) :=
  rtlSelCn{k}_spec _ _""")
    for k, sel in enumerate(info["lfsr_sel"]):
        blocks.append(f"""/-- The LFSR-{k} `sel` mux from its four strobes. -/
def rtlSelLf{k} (opSt opB0 opB1 opB2 : Bool) : BitVec 3 :=
{indent(sel['lines'])}
  {sel['expr']}

/-- The elaborated LFSR-{k} mux is the documented `ST`/`B0..B3` map. -/
theorem rtlSelLf{k}_spec (opSt opB0 opB1 opB2 : Bool) :
    rtlSelLf{k} opSt opB0 opB1 opB2 = lfsrSel opSt opB0 opB1 opB2 := by
  simp only [rtlSelLf{k}, lfsrSel, Metronome.Units.Lfsr.selOf]

/-- The LFSR-{k} selector of the group winner's destination. -/
theorem rtlSelLf{k}_opg (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) :
    rtlSelLf{k} (opg en grp dst dgLf{k} dLf{k}St) (opg en grp dst dgLf{k} dLf{k}B0)
        (opg en grp dst dgLf{k} dLf{k}B1) (opg en grp dst dgLf{k} dLf{k}B2) =
      lfsrSel (opg en grp dst dgLf{k} dLf{k}St) (opg en grp dst dgLf{k} dLf{k}B0)
        (opg en grp dst dgLf{k} dLf{k}B1) (opg en grp dst dgLf{k} dLf{k}B2) :=
  rtlSelLf{k}_spec _ _ _ _""")

    p0 = info["p_sel"]
    blocks.append(f"""/-- The pointer port select `p_sel` from `w_p0[13:8]`. -/
def rtlPSel (w : BitVec 15) : BitVec 2 :=
{indent(p0['lines'])}
  {p0['expr']}

/-- The elaborated `p_sel` is the documented `AL`/`AH`/`W`/`R` map. -/
theorem rtlPSel_spec (w : BitVec 15) : rtlPSel w = p0Sel (slice w 8 6) := by
  simp only [rtlPSel, p0Sel, slice, dP0Al, dP0Ah, dP0W]
  bv_decide

/-- The pointer's port select is the `P0` group winner's destination code. -/
theorem rtlPSel_word (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36)
    (dat : BitVec 48) :
    rtlPSel (pickWord (hitsMask en grp dgP0) dst dat).pack =
      p0Sel (pickWord (hitsMask en grp dgP0) dst dat).dst := by
  rw [rtlPSel_spec, pack_dst]""")

    for k, sop in enumerate(info["sop"]):
        blocks.append(f"""/-- The line-{k} symbol operation `sop` from `ws[13:8]`. -/
def rtlLineSop{k} (ws : BitVec 15) : BitVec 2 :=
{indent(sop['lines'])}
  {sop['expr']}

/-- The elaborated line-{k} `sop` is the documented `SYM`/`DBIT`/`XOR` map (the
RTL `default:` is `XOR`). -/
theorem rtlLineSop{k}_spec (ws : BitVec 15) :
    rtlLineSop{k} ws = lineSop (slice ws 8 6) := by
  simp only [rtlLineSop{k}, lineSop, slice, dLSym, dLDBit]
  bv_decide

/-- The line-{k} symbol operation of the `L.SYM` pick word is its destination. -/
theorem rtlLineSop{k}_word (win : BitVec 6) (grp : BitVec 30) (xl : BitVec 4)
    (dst : BitVec 36) (dat : BitVec 48) :
    rtlLineSop{k} (hitOr (symMask win grp xl {k}) dst dat) =
      lineSop (slice (hitOr (symMask win grp xl {k}) dst dat) 8 6) :=
  rtlLineSop{k}_spec _""")

    for slot, sel in enumerate(info["acc_sel"]):
        blocks.append(f"""/-- Accumulator slot {slot}'s op code from the destination bus. -/
def rtlAccSel{slot} (cDst : BitVec 36) : BitVec 3 :=
{indent(sel['lines'])}
  {sel['expr']}

/-- The elaborated slot-{slot} op code is the ISA map `ACC.LD..CMP` 7..13 → 0..6. -/
theorem rtlAccSel{slot}_spec (cDst : BitVec 36) :
    rtlAccSel{slot} cDst = accSel cDst {slot} := by
  simp only [rtlAccSel{slot}, accSel, Metronome.Units.Acc.opCodeOf, slice]
  bv_decide""")
    names = [f"rtlSelCn{k}_spec" for k in range(3)] + \
            [f"rtlSelCn{k}_opg" for k in range(3)]
    names += [f"rtlSelLf{k}_spec" for k in range(2)] + \
             [f"rtlSelLf{k}_opg" for k in range(2)]
    names += ["rtlPSel_spec", "rtlPSel_word"]
    names += [f"rtlLineSop{k}_spec" for k in range(4)] + \
             [f"rtlLineSop{k}_word" for k in range(4)]
    names += [f"rtlAccSel{slot}_spec" for slot in range(6)]
    return "\n\n".join(blocks), names


def lean_control(info):
    blocks = []
    for k, stream in enumerate(info["streams"]):
        rewind, flush, clr = stream["rewind"], stream["flush"], stream["clr_starved"]
        blocks.append(f"""/-- Stream-{k} `rewind`: the move's `CTL` bit 0 OR the host's. -/
def rtlRewindS{k} (w : BitVec 15) (mctl : Bool) (wSrt : Bool) (aSrt : BitVec 16)
    (hd : BitVec 8) : Bool :=
{indent(rewind['lines'])}
  {rewind['expr']}

/-- `rewind` combines a move to `Sk.CTL` (bit 0 of its data) and a host write
of `SRT.CTL` (bit 0). -/
theorem rtlRewindS{k}_spec (w : BitVec 15) (mctl : Bool) (wSrt : Bool)
    (aSrt : BitVec 16) (hd : BitVec 8) :
    rtlRewindS{k} w mctl wSrt aSrt hd =
      (streamCtlOf (slice w 0 8) mctl (hostCtl wSrt aSrt {k}) hd).rewind := by
  simp only [rtlRewindS{k}, streamCtlOf, hostCtl, slice, bitAt]
  bv_decide

/-- The stream-{k} rewind strobe of the group winner and the host decode. -/
theorem rtlRewindS{k}_word (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36)
    (dat : BitVec 48) (wSrt : Bool) (aSrt : BitVec 16) (hd : BitVec 8) :
    rtlRewindS{k} (pickWord (hitsMask en grp dgS{k}) dst dat).pack
        (opg en grp dst dgS{k} dS{k}Ctl) wSrt aSrt hd =
      (streamCtlOf (pickWord (hitsMask en grp dgS{k}) dst dat).data
        (opg en grp dst dgS{k} dS{k}Ctl) (hostCtl wSrt aSrt {k}) hd).rewind := by
  rw [rtlRewindS{k}_spec, pack_data]

/-- Stream-{k} `flush`: the move's `CTL` bit 1 OR the host's. -/
def rtlFlushS{k} (w : BitVec 15) (mctl : Bool) (wSrt : Bool) (aSrt : BitVec 16)
    (hd : BitVec 8) : Bool :=
{indent(flush['lines'])}
  {flush['expr']}

theorem rtlFlushS{k}_spec (w : BitVec 15) (mctl : Bool) (wSrt : Bool)
    (aSrt : BitVec 16) (hd : BitVec 8) :
    rtlFlushS{k} w mctl wSrt aSrt hd =
      (streamCtlOf (slice w 0 8) mctl (hostCtl wSrt aSrt {k}) hd).flush := by
  simp only [rtlFlushS{k}, streamCtlOf, hostCtl, slice, bitAt]
  bv_decide

theorem rtlFlushS{k}_word (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36)
    (dat : BitVec 48) (wSrt : Bool) (aSrt : BitVec 16) (hd : BitVec 8) :
    rtlFlushS{k} (pickWord (hitsMask en grp dgS{k}) dst dat).pack
        (opg en grp dst dgS{k} dS{k}Ctl) wSrt aSrt hd =
      (streamCtlOf (pickWord (hitsMask en grp dgS{k}) dst dat).data
        (opg en grp dst dgS{k} dS{k}Ctl) (hostCtl wSrt aSrt {k}) hd).flush := by
  rw [rtlFlushS{k}_spec, pack_data]

/-- Stream-{k} `clr_starved`: the host's `SRT.CTL` bit 7. -/
def rtlClrS{k} (wSrt : Bool) (aSrt : BitVec 16) (hd : BitVec 8) : Bool :=
{indent(clr['lines'])}
  {clr['expr']}

theorem rtlClrS{k}_spec (wSrt : Bool) (aSrt : BitVec 16) (hd : BitVec 8) :
    rtlClrS{k} wSrt aSrt hd =
      (streamCtlOf 0 false (hostCtl wSrt aSrt {k}) hd).clrStarved := by
  simp only [rtlClrS{k}, streamCtlOf, hostCtl, bitAt]
  bv_decide""")

    for k, cap in enumerate(info["cap"]):
        blocks.append(f"""/-- Stream-{k} `cap_en = cen & ~replay`. -/
def rtlCapEnS{k} (cen replay : Bool) : Bool :=
{indent(cap['lines'])}
  {cap['expr']}

theorem rtlCapEnS{k}_spec (cen replay : Bool) : rtlCapEnS{k} cen replay = capEn cen replay := by
  unfold rtlCapEnS{k} capEn
  rfl""")

    off = info["dbg_off"]
    blocks.append(f"""/-- `cw_dbg_off`: the queued configuration address as a `DBG` offset. -/
def rtlCwDbgOff (addr : BitVec 16) : BitVec 32 :=
{indent(off['lines'])}
  {off['expr']}

theorem rtlCwDbgOff_spec (addr : BitVec 16) : rtlCwDbgOff addr = cwDbgOff addr := by
  simp only [rtlCwDbgOff, cwDbgOff, haDbgBase]
  bv_decide""")
    for entry, (suffix, constant) in zip(info["dbg"], DBG_BYTES):
        blocks.append(f"""/-- `{entry['name']}`: host write of the DBG byte OR core drain to it. -/
def {entry['lean']} (wDbg : Bool) (aDbg : BitVec 16) (drain : Bool)
    (addr : BitVec 16) : Bool :=
{indent(entry['lines'])}
  {entry['expr']}

theorem {entry['lean']}_spec (wDbg : Bool) (aDbg : BitVec 16) (drain : Bool)
    (addr : BitVec 16) :
    {entry['lean']} wDbg aDbg drain addr =
      dbgByteWrite wDbg aDbg drain addr {constant} := by
  simp only [{entry['lean']}, dbgByteWrite, hostDbg, cwDbgOff, haDbgBase,
    {constant}]
  bv_decide""")
    names = ["rtlCwDbgOff_spec"]
    names += [f"rtlRewindS{k}_spec" for k in range(2)] + \
             [f"rtlRewindS{k}_word" for k in range(2)]
    names += [f"rtlFlushS{k}_spec" for k in range(2)] + \
             [f"rtlFlushS{k}_word" for k in range(2)]
    names += [f"rtlClrS{k}_spec" for k in range(2)]
    names += [f"rtlCapEnS{k}_spec" for k in range(2)]
    names += [f"{entry['lean']}_spec" for entry in info["dbg"]]
    return "\n\n".join(blocks), names


def lean_file(kind, body, names, fingerprint, case):
    template = TEMPLATE.read_text(encoding="utf-8")
    audit = "\n".join(f"#print axioms {name}" for name in names)
    values = {"TOP": TOP, "FINGERPRINT": fingerprint, "KIND": kind, "CASE": case,
              "BODY": body, "AUDIT": audit}
    for name, value in values.items():
        require("{{" + name + "}}" in template,
                f"StrobesEquivalence.lean.in: missing {{{{{name}}}}} placeholder")
        template = template.replace("{{" + name + "}}", str(value))
    require("{{" not in template, "StrobesEquivalence.lean.in: unsubstituted placeholder")
    return template


def axiom_audit(text):
    found = {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
             for name, axioms in AXIOM_LINE.findall(text)}
    for name in NO_AXIOM_LINE.findall(text):
        found.setdefault(name, [])
    return found


def run_lean(source, filename, artifact, lake, work, evidence, timeout=900):
    path = Path(work) / filename
    path.write_text(source, encoding="utf-8")
    if evidence:
        (Path(evidence) / artifact).write_text(source, encoding="utf-8")
    command = [lake, "env", "lean", "-j1", "-DwarningAsError=true", str(path)]
    return run(command, HERE, timeout=timeout)


def lean_case(source, filename, artifact, lake, work, evidence, timeout=900):
    """Run one generated file, retrying once when Lean dies without a verdict."""
    for attempt in range(2):
        try:
            result = run_lean(source, filename, artifact, lake, work, evidence, timeout)
        except Exception as exc:  # subprocess.TimeoutExpired
            if attempt:
                raise StrobesRejected(f"{filename}: Lean timed out after {timeout}s: {exc}")
            continue
        if result.returncode in (0, 1, 2, 3) or result.stdout.strip() or attempt:
            return result
    return result


# The three generated files: (kind, evidence suffix, emitter).
PARTS = (("opg strobes", "opg", lean_opg),
         ("selectors", "sel", lean_units),
         ("stream and DBG control", "ctl", lean_control))


def check_strobes(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the elaborated operation strobes and their generated Lean proofs.

    `rtlil_or_json` is a parsed Yosys design, a path to `design.json`, or a
    Verilog source directory to elaborate.  Evidence is written to `out_dir` as
    `<case>.<part>.lean`, `<case>.<part>.log` for the three generated proofs.
    Returns a result dictionary; a rejected cut raises `StrobesRejected` (proof
    or audit) or `UnsupportedRTL` (structure or wiring).
    """
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-strobes-{case}-") as tmp:
        work = Path(tmp)
        is_json = isinstance(rtlil_or_json, dict) or (
            isinstance(rtlil_or_json, (str, Path)) and Path(rtlil_or_json).suffix == ".json")
        if is_json:
            modules = load_modules(rtlil_or_json)
            fingerprint = "not recorded: parsed design JSON"
            base = Path(rtlil_or_json).parent if isinstance(
                rtlil_or_json, (str, Path)) else ROOT / "src"
            try:
                snapshot = snapshot_of(base)
            except UnsupportedRTL:
                snapshot = snapshot_of(ROOT / "src")
        else:
            snapshot = snapshot_of(rtlil_or_json)
            modules, fingerprint, commands, yosys_log = elaborate(
                snapshot, work / "rtl", yosys)
            log.append(f"RTL snapshot SHA-256: {fingerprint}\n")
            log.append(f"Yosys command: {commands}\n")
            log.append(yosys_log)

        try:
            params = strobes_params(snapshot)
            info = {"params": params,
                    "strobes": extract_opg(modules, params),
                    "acc": extract_acc_hit(modules, params)}
            info.update(extract_units(modules, params))
            info.update(extract_control(modules, params))
            log.append(f"OPG strobes: {len(info['strobes'])}, "
                       f"selectors: 3 counters + 2 LFSRs + 2 shifters, "
                       f"lines: {len(info['sop'])}, streams: {len(info['streams'])}, "
                       f"DBG bytes: {len(info['dbg'])}\n")
            for entry in info["strobes"]:
                log.append(f"  {entry['name']}: group {entry['group_code']}, "
                           f"{len(entry['lines'])} signals\n")
            sources = []
            for kind, suffix, emitter in PARTS:
                body, names = emitter(info)
                sources.append((kind, suffix,
                                lean_file(kind, body, names, fingerprint, case), names))
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the extraction: {exc}\n")
            (out_dir / f"{case}.opg.log").write_text("".join(log), encoding="utf-8")
            raise

        results = []
        try:
            for kind, suffix, source, names in sources:
                results.append((suffix, kind, names, lean_case(
                    source, f"Strobes{case}{suffix}.lean", f"{case}.{suffix}.lean",
                    lake, work, out_dir)))
        except StrobesRejected:
            (out_dir / f"{case}.opg.log").write_text("".join(log), encoding="utf-8")
            raise
        finally:
            (out_dir / f"{case}.opg.log").write_text("".join(log), encoding="utf-8")

        axioms = {}
        for suffix, kind, names, result in results:
            log.append(f"== {kind} ==\n{result.stdout}")
            axioms.update(axiom_audit(result.stdout))
        failures = [f"{kind} (exit {result.returncode})"
                    for _, kind, _, result in results if result.returncode != 0]
        sorry = any("sorryAx" in result.stdout for _, _, _, result in results)
        if failures:
            outcome = "rejected by Lean: " + ", ".join(failures)
        elif sorry:
            outcome = "rejected: the proof used sorryAx"
        else:
            outcome = "accepted"
        log.append(f"-- {case}: {outcome}\n")
        (out_dir / f"{case}.opg.log").write_text("".join(log), encoding="utf-8")
        (out_dir / f"{case}.axioms.txt").write_text(
            "".join(f"{name}: {', '.join(found)}\n" for name, found in axioms.items()),
            encoding="utf-8")
        report = {
            "case": case,
            "ok": not failures and not sorry,
            "outcome": outcome,
            "exit": max(result.returncode for _, _, _, result in results),
            "opg": len(info["strobes"]),
            "lines": len(info["sop"]),
            "streams": len(info["streams"]),
            "dbg": len(info["dbg"]),
            "fingerprint": fingerprint,
            "sources": [out_dir / f"{case}.{suffix}.lean" for _, suffix, _, _ in results],
            "log": out_dir / f"{case}.opg.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            first = next((line.strip() for _, _, _, result in results
                          for line in result.stdout.splitlines() if "error:" in line),
                         outcome)
            raise StrobesRejected(f"{case}: {outcome}\n" + "".join(log),
                                  reason=f"{outcome}: {first[:200]}",
                                  code=report["exit"])
    return report


def strobes_mutations():
    """The planted operation-strobe regressions, as snapshot transformers."""
    def replace(name, before, after):
        def apply(snapshot):
            require(name in snapshot, f"mutation: missing {name}")
            data = snapshot[name]
            require(data.count(before.encode()) == 1,
                    f"mutation: anchor changed in {name}: {before}")
            return {**snapshot, name: data.replace(before.encode(), after.encode(), 1)}
        return apply

    def replace_all(name, edits):
        def apply(snapshot):
            require(name in snapshot, f"mutation: missing {name}")
            data = snapshot[name]
            for before, after in edits:
                require(data.count(before.encode()) == 1,
                        f"mutation: anchor changed in {name}: {before}")
                data = data.replace(before.encode(), after.encode(), 1)
            return {**snapshot, name: data}
        return apply

    return OrderedDict((
        # The counter-0 LO and HI strobes test each other's destination.
        ("strobes_counter_swap", replace_all(
            "project.v",
            (("wire op_lo = `OPG(DG_CNK[5*k +: 5], D_CNLO[6*k +: 6]);",
              "wire op_lo = `OPG(DG_CNK[5*k +: 5], D_CNHI[6*k +: 6]);"),
             ("wire op_hi = `OPG(DG_CNK[5*k +: 5], D_CNHI[6*k +: 6]);",
              "wire op_hi = `OPG(DG_CNK[5*k +: 5], D_CNLO[6*k +: 6]);")))),
        # The LFSR-0 `op_b1` strobe uses B2's destination code.
        ("strobes_lfsr_b1", replace(
            "project.v",
            "wire op_b1 = `OPG(DG_LFK[5*k +: 5], D_LFB[6*(4*k+1) +: 6]);",
            "wire op_b1 = `OPG(DG_LFK[5*k +: 5], D_LFB[6*(4*k+2) +: 6]);")),
        # The shifter's `sel` strobe tests the `LD` destination codes.
        ("strobes_shifter_ld", replace(
            "project.v",
            "localparam [11:0] D_SHSH = {D_SH1_SH, D_SH0_SH};",
            "localparam [11:0] D_SHSH = {D_SH1_LD, D_SH0_LD};")),
        # The pointer's port select swaps the AH and W arms.
        ("strobes_p0_swap", replace_all(
            "project.v",
            (("(w_p0[13:8] == D_P0_AH) ? 2'd1 :",
              "(w_p0[13:8] == D_P0_W)  ? 2'd1 :"),
             ("(w_p0[13:8] == D_P0_W)  ? 2'd2 : 2'd3;",
              "(w_p0[13:8] == D_P0_AH) ? 2'd2 : 2'd3;")))),
        # The stream rewind ignores the host's `SRT.CTL` bit.
        ("strobes_rewind_no_host", replace(
            "project.v",
            ".rewind((mctl & w[0]) | (hctl & h_wd[0]))",
            ".rewind(mctl & w[0])")),
        # The line's `DBIT` symbol operation is mapped to XOR.
        ("strobes_sop_dbit", replace(
            "project.v",
            "((ws[13:8] == D_L_DBIT) ? 2'd1 : 2'd2)",
            "((ws[13:8] == D_L_DBIT) ? 2'd2 : 2'd1)")),
        # The `DBG.EMASK` byte-1 strobe uses byte 0's offset.
        ("strobes_dbg_em1", replace(
            "project.v",
            "(cw_drain & (cw_dbg_off == HO_DBG_EMASK + 1))",
            "(cw_drain & (cw_dbg_off == HO_DBG_EMASK))")),
        # `acc_hit` reads the move groups in reverse order, so with two ACC
        # contenders the highest (core, move index) wins instead of the lowest.
        ("strobes_acc_highest", replace(
            "project.v",
            "wire [5:0]  acc_hit = `HITG(DG_ACC);",
            "wire [5:0]  acc_hit = hits(mv_en, {grp_v[0 +: 5], grp_v[5 +: 5], "
            "grp_v[10 +: 5], grp_v[15 +: 5], grp_v[20 +: 5], grp_v[25 +: 5]}, DG_ACC);")),
    ))


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted operation-strobe regression is rejected.

    Returns one `(case, rejected, stage, exit)` record per mutation and raises
    `StrobesRejected` if any mutant is accepted.
    """
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-strobes-mutants-") as tmp:
        for case, transform in strobes_mutations().items():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_strobes(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"extraction: {exc}", 1))
                continue
            except StrobesRejected as exc:
                records.append((case, True, f"generated Lean: {exc.reason}", exc.code))
                continue
            records.append((case, not report["ok"], report["outcome"], report["exit"]))
    accepted = [case for case, rejected, _, _ in records if not rejected]
    require(not accepted, f"mutants accepted: {', '.join(accepted)}")
    return records


def write_status(path, records):
    """Write the run status from the actual per-case exit codes."""
    lines = ["case\toutcome\texit\texpectation"]
    for case, outcome, code, ok in records:
        lines.append(f"{case}\t{outcome}\t{code}\t{'ok' if ok else 'FAILED'}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mutations", action="store_true",
                        help="also check the planted operation-strobe regressions")
    parser.add_argument("--artifacts-dir", type=Path, default=DEFAULT_ARTIFACTS,
                        help="fresh evidence directory (default: %(default)s)")
    args = parser.parse_args(argv)
    lake, yosys = (shutil.which(tool) for tool in ("lake", "yosys"))
    if not lake or not yosys:
        parser.error("lake and yosys must be on PATH")
    artifacts = args.artifacts_dir
    if artifacts.exists():
        parser.error(f"{artifacts} already exists; use a fresh evidence directory")
    artifacts.mkdir(parents=True)

    transcript = []

    def emit(text=""):
        transcript.append(text + "\n")
        print(text, flush=True)

    records = []
    code = 0
    try:
        versions = [run([lake, "--version"], HERE), run([yosys, "-V"], HERE)]
        version_log = "".join(result.stdout for result in versions)
        (artifacts / "tools.log").write_text(version_log, encoding="utf-8")
        emit(version_log.rstrip())
        if any(result.returncode for result in versions):
            raise StrobesRejected("tool version query failed")

        source_log = []
        for path in (STROBES_LEAN, Path(__file__).resolve(), TEMPLATE):
            digest = hashlib.sha256(Path(path).read_bytes()).hexdigest()
            source_log.append(f"{digest}  {Path(path).relative_to(ROOT)}")
        (artifacts / "sources.log").write_text("\n".join(source_log) + "\n",
                                               encoding="utf-8")

        build = run([lake, "build", "Metronome.Strobes"], HERE)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise StrobesRejected("lake build Metronome.Strobes failed")

        snapshot = snapshot_of(ROOT / "src")
        try:
            report = check_strobes(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        except StrobesRejected as exc:
            emit(f"baseline: {exc.reason}")
            records.append(("baseline", exc.reason, exc.code, False))
            return 1
        except UnsupportedRTL as exc:
            emit(f"baseline: extraction: {exc}")
            records.append(("baseline", f"extraction: {exc}", 1, False))
            return 1
        emit(f"baseline: {report['outcome']} ({report['opg']} OPG strobes, "
             f"{report['lines']} lines, {report['streams']} streams, "
             f"{report['dbg']} DBG bytes)")
        records.append(("baseline", report["outcome"], report["exit"], report["ok"]))
        if not report["ok"]:
            code = 1

        if args.mutations and code == 0:
            for case, rejected, stage, case_exit in run_mutations(
                    snapshot, artifacts, lake, yosys):
                outcome = f"rejected ({stage})" if rejected else "accepted"
                emit(f"{case}: {outcome}")
                records.append((case, outcome, case_exit, rejected))
                if not rejected:
                    code = 1
    finally:
        write_status(artifacts / "run_status.txt", records)
        (artifacts / "stdout.log").write_text("".join(transcript), encoding="utf-8")
    return code


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    sys.stderr.reconfigure(encoding="utf-8")
    try:
        raise SystemExit(main())
    except (OSError, KeyError, RuntimeError, ValueError, UnsupportedRTL) as exc:
        raise SystemExit(f"Operation-strobe check failed: {exc}") from exc
