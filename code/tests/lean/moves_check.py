"""Check the chip-top move resolution of the Metronome chip top.

SPEC_V2 §6 partitions the destination ports into write groups, raises sticky
`CONFLICT` when two enabled moves target one group in a cycle, and lets only the
lowest `(core, move index)` write take effect.  This module re-elaborates the
chip top with `verify.py`'s Yosys recipe and extracts, from the actual cells:

* the destination → write-group lookup `grp[k] = DG_MAP[5*c_dst[6*k +: 6] +: 5]`;
* `mv_valid`, `mv_win` (the `same_key` blocking), `conflict_ev`;
* every unit's `pick(hits(mv_en, grp_v, G), c_dst, c_dat)` word, plus the four
  per-line `L.SYM` picks;
* the sticky `CONFLICT` and `MEMHAZ` registers with their `CTRL.STICKY` clears;
* the two source side effects: the `HOST.IN` read that clears `INV`, and the
  `P0.D` read while `!RDY` that raises `MEMHAZ`.

It emits Lean that proves each extracted cone equal to the independent
specification in `Metronome/Moves.lean`.  The destination → group table in that
module is transcribed from `code/md2/machine.json`; `--check` regenerates the
table and fails if the transcription or `md2_map.vh` drifts.

Run it from the repository root:

    python code/tests/lean/moves_check.py
    python code/tests/lean/moves_check.py --mutations
    python code/tests/lean/moves_check.py --check

`run_mutations()` plants the regressions on temporary copies of `src/` (never
the repository): a changed `DG_MAP` entry, a `same_key` that ignores the line, a
`mv_win` that prefers the highest index, a `conflict_ev` that misses a three-way
conflict, a clear that beats a same-cycle event, a `NULL` destination that gets
a group, a `mv_valid` that ignores the group, and a `hits` mask that ignores
`mv_en`.  Every one must be rejected.
"""

import argparse
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

DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_moves_v4_20261121"
TEMPLATE = HERE / "MovesEquivalence.lean.in"
MOVES_LEAN = HERE / "Metronome" / "Moves.lean"
MACHINE_JSON = ROOT / "code" / "md2" / "machine.json"
MAP_HEADER = ROOT / "src" / "md2_map.vh"
AXIOM_LINE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)
NO_AXIOM_LINE = re.compile(r"^'([^']+)' does not depend on any axioms$", re.MULTILINE)

# The unit words: (elaborated net, Lean name).  Every one is
# `pick(hits(mv_en, grp_v, G), c_dst, c_dat)`.
WORD_NETS = (
    ("w_flags", "Flags"), ("w_cw", "Cw"), ("w_p0", "P0"), ("w_hout", "HostOut"),
    ("g_r[0].w", "R0"), ("g_r[1].w", "R1"), ("g_r[2].w", "R2"), ("g_r[3].w", "R3"),
    ("g_sh[0].w", "Sh0"), ("g_sh[1].w", "Sh1"),
    ("g_sh[0].c", "Sh0Cfg"), ("g_sh[1].c", "Sh1Cfg"),
    ("g_cn[0].w", "Cnt0"), ("g_cn[1].w", "Cnt1"), ("g_cn[2].w", "Cnt2"),
    ("g_lf[0].w", "Lf0"), ("g_lf[1].w", "Lf1"),
    ("g_s[0].w", "S0"), ("g_s[1].w", "S1"),
    ("g_ln[0].wc", "Line0Ctl"), ("g_ln[1].wc", "Line1Ctl"),
    ("g_ln[2].wc", "Line2Ctl"), ("g_ln[3].wc", "Line3Ctl"),
)

# The per-line `L.SYM` picks: `pick(sh, c_dst, c_dat)` over the line's winners.
SYM_NETS = (("g_ln[0].ws", "Sym0", 0), ("g_ln[1].ws", "Sym1", 1),
            ("g_ln[2].ws", "Sym2", 2), ("g_ln[3].ws", "Sym3", 3))

# The documented write-group codes of `md2_map.vh`.
GROUP_PARAMS = (
    ("dg_l_sym", r"localparam \[4:0\] DG_L_SYM = 5'd(\d+);"),
    ("dg_t_stop", r"localparam \[4:0\] DG_T_STOP = 5'd(\d+);"),
    ("dg_flags", r"localparam \[4:0\] DG_FLAGS = 5'd(\d+);"),
    ("dg_acc", r"localparam \[4:0\] DG_ACC = 5'd(\d+);"),
    ("dg_r0", r"localparam \[4:0\] DG_R0 = 5'd(\d+);"),
    ("dg_r1", r"localparam \[4:0\] DG_R1 = 5'd(\d+);"),
    ("dg_r2", r"localparam \[4:0\] DG_R2 = 5'd(\d+);"),
    ("dg_r3", r"localparam \[4:0\] DG_R3 = 5'd(\d+);"),
    ("dg_sh0", r"localparam \[4:0\] DG_SH0 = 5'd(\d+);"),
    ("dg_sh1", r"localparam \[4:0\] DG_SH1 = 5'd(\d+);"),
    ("dg_sh0_cfg", r"localparam \[4:0\] DG_SH0_CFG = 5'd(\d+);"),
    ("dg_sh1_cfg", r"localparam \[4:0\] DG_SH1_CFG = 5'd(\d+);"),
    ("dg_cnt0", r"localparam \[4:0\] DG_CNT0 = 5'd(\d+);"),
    ("dg_cnt1", r"localparam \[4:0\] DG_CNT1 = 5'd(\d+);"),
    ("dg_cnt2", r"localparam \[4:0\] DG_CNT2 = 5'd(\d+);"),
    ("dg_lf0", r"localparam \[4:0\] DG_LF0 = 5'd(\d+);"),
    ("dg_lf1", r"localparam \[4:0\] DG_LF1 = 5'd(\d+);"),
    ("dg_p0", r"localparam \[4:0\] DG_P0 = 5'd(\d+);"),
    ("dg_s0", r"localparam \[4:0\] DG_S0 = 5'd(\d+);"),
    ("dg_s1", r"localparam \[4:0\] DG_S1 = 5'd(\d+);"),
    ("dg_l0_ctl", r"localparam \[4:0\] DG_L0_CTL = 5'd(\d+);"),
    ("dg_l1_ctl", r"localparam \[4:0\] DG_L1_CTL = 5'd(\d+);"),
    ("dg_l2_ctl", r"localparam \[4:0\] DG_L2_CTL = 5'd(\d+);"),
    ("dg_l3_ctl", r"localparam \[4:0\] DG_L3_CTL = 5'd(\d+);"),
    ("dg_host_out", r"localparam \[4:0\] DG_HOST_OUT = 5'd(\d+);"),
    ("dg_cw", r"localparam \[4:0\] DG_CW = 5'd(\d+);"),
    ("dg_none", r"localparam \[4:0\] DG_NONE = 5'd(\d+);"),
)

SRC_PARAMS = (
    ("s_p0_d", r"localparam \[5:0\] S_P0_D = 6'd(\d+);"),
    ("s_host_in", r"localparam \[5:0\] S_HOST_IN = 6'd(\d+);"),
)

# Free leaves of each cone: (net, width, Lean value).  `grp_v` is bound free so
# the arbitration cones do not drag in the destination map; the map is proved
# separately and the two compose by rewriting.
MAP_FREE = (("c_dst", 36, "dst"),)
ARB_FREE = (("mv_en", 6, "en"), ("grp_v", 30, "grp"), ("xl", 4, "xl"), ("xt", 6, "xt"))
WORD_FREE = (("mv_en", 6, "en"), ("grp_v", 30, "grp"), ("c_dst", 36, "dst"),
             ("c_dat", 48, "dat"))
SYM_FREE = (("mv_win", 6, "win"), ("grp_v", 30, "grp"), ("xl", 4, "xl"),
            ("c_dst", 36, "dst"), ("c_dat", 48, "dat"))


class MovesRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated move cut."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


class MovesCone(corectl.VectorCone):
    """A `VectorCone` that also decodes the map's multiply and wide shift.

    The destination lookup is `DG_MAP[5*d +: 5]`, which Yosys lowers to a
    32-bit `$mul` by 5, an `$add` of zero and a 320-bit `$shiftx`; the conflict
    OR's complement is a 6-bit `$not`.  Those shapes are decoded here rather
    than in the shared adapter.  Every extension stays fail-closed: a multiply
    with two non-constant operands, a shift with a non-constant or unbounded
    amount, or a wide cell of any other kind raises `UnsupportedRTL`.
    """

    def __init__(self, name, module):
        super().__init__(name, module)
        for cell_name, cell in module["cells"].items():
            kind = cell["type"]
            pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
            where = f"{name}.{cell_name} ({kind})"
            if kind == "$not" and len(pins.get("Y", ())) > 1:
                require(set(pins) == {"A", "Y"} and len(pins["A"]) == len(pins["Y"]),
                        f"{where}: expected a wide complement")
                continue
            if kind == "$shiftx":
                continue
            if kind not in ("$mul", "$shr", "$shl"):
                continue
            require(len(pins) == 3 and len(pins["Y"]) ==
                    int(cell["parameters"]["Y_WIDTH"], 2), f"{where}: unexpected ports")
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = (kind, pins, cell["parameters"], where)

    def expression(self, bits):
        driver = self.drivers.get(bits)
        if driver is not None and driver[0] == "$not" and len(bits) > 1:
            require(bits not in self.resolving, f"{driver[3]}: combinational loop")
            self.resolving.add(bits)
            expression = f"(~~~{self.expression(driver[1]['A'])})"
            self.resolving.remove(bits)
            return self._bind(bits, expression)
        if driver is not None and driver[0] == "$shiftx" and len(bits) > 1:
            _, pins, params, where = driver
            width = int(params["Y_WIDTH"], 2)
            source = int(params["A_WIDTH"], 2)
            require(len(bits) == width and width <= source, f"{where}: unexpected result bus")
            require(int(params["B_SIGNED"], 2) == 0 or self._bound(pins["B"]) < 2 ** 31,
                    f"{where}: the shift amount could be negative")
            shifted = (f"(BitVec.ushiftRight {self.expression(pins['A'])} "
                       f"({self._index(pins['B']) }))")
            return self._bind(bits, f"(BitVec.truncate {width} {shifted})")
        if driver is not None and driver[0] == "$mul":
            _, pins, params, where = driver
            width = int(params["Y_WIDTH"], 2)
            require(len(bits) == width, f"{where}: unexpected result bus")
            left, right = pins["A"], pins["B"]
            left_const, right_const = _is_constant(left), _is_constant(right)
            require(left_const != right_const, f"{where}: expected a constant multiply")
            factor, other = ((constant_value(left, where), right) if left_const
                             else (constant_value(right, where), left))
            require(factor * (2 ** len(other) - 1) < 2 ** width,
                    f"{where}: the product does not fit the result")
            expression = (f"(({factor} : BitVec {width}) * "
                          f"(BitVec.setWidth {width} {self.expression(other)}))")
            return self._bind(bits, expression)
        if driver is not None and driver[0] in ("$shr", "$shl"):
            _, pins, params, where = driver
            width = int(params["Y_WIDTH"], 2)
            require(len(bits) == width and _is_constant(pins["B"]),
                    f"{where}: expected a constant shift")
            op = ">>>" if driver[0] == "$shr" else "<<<"
            expression = (f"(BitVec.setWidth {width} {self.expression(pins['A'])} "
                          f"{op} {constant_value(pins['B'], where)})")
            return self._bind(bits, expression)
        return super().expression(bits)

    def _bound(self, bits):
        """A sound upper bound of a bus's unsigned value, for the shift guard."""
        if _is_constant(bits):
            return constant_value(bits, "bound")
        driver = self.drivers.get(bits)
        if driver is not None and driver[0] == "$mul":
            _, pins, params, _ = driver
            left, right = pins["A"], pins["B"]
            if _is_constant(left) and not _is_constant(right):
                return constant_value(left, "bound") * self._bound(right)
            if _is_constant(right) and not _is_constant(left):
                return constant_value(right, "bound") * self._bound(left)
        if driver is not None and driver[0] == "$add":
            _, pins, _, _ = driver
            return self._bound(pins["A"]) + self._bound(pins["B"])
        if driver is not None and driver[0] == "$and" and _is_constant(pins["B"]):
            return min(self._bound(pins["A"]), constant_value(pins["B"], "bound"))
        return 2 ** len(bits) - 1

    def _index(self, bits):
        """The shift amount as a Lean `Nat` expression.

        The destination lookup's index is `5*d` computed in 32 bits because the
        RTL writes `DG_MAP[5*c_dst[6k +: 6] +: 5]` with an `integer` index.
        Since the adapter requires the product to fit 32 bits, its unsigned
        value is the `Nat` product, so the index is emitted as
        `factor * x.toNat`; the same bound makes `+ 0` and any other constant
        addition exact.  A non-constant, non-product index falls back to
        `(value).toNat`, which is the unsigned shift amount whatever it is.
        """
        driver = self.drivers.get(bits)
        if _is_constant(bits):
            return str(constant_value(bits, "index"))
        if driver is not None and driver[0] == "$add":
            _, pins, _, where = driver
            left, right = pins["A"], pins["B"]
            if _is_constant(right):
                return self._index(left) + (" + %d" % constant_value(right, where)
                                            if constant_value(right, where) else "")
            if _is_constant(left):
                return self._index(right) + (" + %d" % constant_value(left, where)
                                             if constant_value(left, where) else "")
        if driver is not None and driver[0] == "$mul":
            _, pins, params, where = driver
            left, right = pins["A"], pins["B"]
            left_const, right_const = _is_constant(left), _is_constant(right)
            if left_const != right_const:
                factor, other = ((constant_value(left, where), right) if left_const
                                 else (constant_value(right, where), left))
                width = int(params["Y_WIDTH"], 2)
                require(factor * (2 ** len(other) - 1) < 2 ** width,
                        f"{where}: the product does not fit the result")
                return f"{factor} * ({self.expression(other)}).toNat"
        return f"({self.expression(bits)}).toNat"


def _is_constant(bits):
    return bool(bits) and all(bit in ("0", "1") for bit in bits)


def constant_value(bits, where):
    require(_is_constant(bits), f"{where}: expected a constant bus")
    return int("".join(reversed(bits)), 2)


def elaborate(snapshot, work, yosys):
    return corectl.elaborate(snapshot, work, yosys)


def snapshot_of(directory):
    return corectl.snapshot_of(directory)


def load_modules(rtlil_or_json):
    return corectl.load_modules(rtlil_or_json)


def net(top, name, width):
    return corectl.net(top, name, width)


def moves_params(snapshot):
    """Read the write-group and source codes from the generated headers."""
    text = "".join(snapshot[name].decode("latin-1") for name in sorted(snapshot)
                   if name.endswith(".vh"))
    values = {}
    for name, pattern in GROUP_PARAMS + SRC_PARAMS:
        match = re.search(pattern, text)
        require(match is not None, f"{name}: constant pattern changed in the headers")
        values[name] = int(match.group(1), 10)
    codes = [values[name] for name, _ in GROUP_PARAMS]
    require(len(set(codes)) == len(codes), "duplicate DG_* codes in md2_map.vh")
    require(values["dg_none"] == 31, "DG_NONE is not 31")
    return values


def machine_table(path=MACHINE_JSON):
    """The 64-code destination → group table derived from `machine.json`."""
    machine = json.loads(Path(path).read_text(encoding="utf-8"))
    destinations = machine["dst"]
    groups = machine["write_groups"]
    require(len(destinations) == 61, f"{path}: unexpected destination count")
    codes = {}
    for index, name in enumerate(groups):
        require(name not in codes, f"{path}: duplicate write group {name}")
        codes[name] = index
    table = []
    for destination in destinations:
        group = 31
        for name, members in groups.items():
            if destination in members:
                require(group == 31, f"{path}: {destination} is in two groups")
                group = codes[name]
        table.append(group)
    table += [31, 31, 31]
    require(len(table) == 64, "the table must cover all 64 destination codes")
    value = 0
    for index, group in enumerate(table):
        require(0 <= group < 32, f"{path}: group code out of range")
        value |= group << (5 * index)
    return table, value


def spec_table(path=MOVES_LEAN):
    """The `BitVec 320` literal transcribed in `Metronome/Moves.lean`."""
    text = Path(path).read_text(encoding="utf-8")
    match = re.search(r"def dgMapLiteral : BitVec 320 :=\s*(0x[0-9a-fA-F]+)", text)
    require(match is not None, f"{path}: dgMapLiteral pattern changed")
    return int(match.group(1), 16)


def header_table(path=MAP_HEADER):
    """The `DG_MAP` literal in `md2_map.vh` as a 320-bit integer."""
    text = Path(path).read_text(encoding="utf-8")
    match = re.search(r"localparam \[319:0\] DG_MAP = \{(.*?)\};", text, re.S)
    require(match is not None, f"{path}: DG_MAP pattern changed")
    entries = [int(value) for value in re.findall(r"5'd(\d+)", match.group(1))]
    require(len(entries) == 64, f"{path}: DG_MAP has {len(entries)} entries")
    value = 0
    for index, group in enumerate(reversed(entries)):
        value |= group << (5 * index)
    return value


def check_tables(moves_path=MOVES_LEAN, header_path=MAP_HEADER, machine_path=MACHINE_JSON):
    """`--check`: the transcribed table and the header agree with `machine.json`."""
    table, expected = machine_table(machine_path)
    transcribed = spec_table(moves_path)
    require(transcribed == expected,
            f"{moves_path}: dgMapLiteral is 0x{transcribed:x}, machine.json says 0x{expected:x}")
    header = header_table(header_path)
    require(header == expected,
            f"{header_path}: DG_MAP is 0x{header:x}, machine.json says 0x{expected:x}")
    return {"table": table, "value": expected}


def used_cells(modules, top, roots, stops):
    """The combinational cells feeding `roots`, stopping at the cut's leaves.

    `stops` is the set of net bits bound as free inputs; a cell that reads them
    is included, but the walk does not descend past them into the logic that
    the cut replaces (the arbitration, the map, the cores).
    """
    index = corectl.drivers(top)
    stops = set(stops)
    seen, stack, cells, walked = set(), list(roots), [], set()
    while stack:
        bit = stack.pop()
        if bit in seen or bit in ("0", "1", "x", "z") or bit in stops:
            continue
        seen.add(bit)
        owner = index.get(bit)
        if owner is None:
            continue
        cell = top["cells"][owner[0]]
        if corectl.is_cell_leaf(modules, cell) or id(cell) in walked:
            continue
        walked.add(id(cell))
        cells.append(cell)
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] == "input":
                stack.extend(bits)
    return cells


def free_bits(top, frees):
    """Every bit a cone binds as a free leaf."""
    return {bit for name, _, _ in frees for bit in top["netnames"][name]["bits"]}


def comparators(modules, top, bits, stops, operand_bus, width):
    """The constants a cone's cells compare slices of `operand_bus` with.

    Handles both `$eq` with a constant second operand and the zero test Yosys
    lowers to `$logic_not` (`x == 0` is `$logic_not(x)`, as in the
    configuration-address cut), so a zero group or line constant is found too.
    """
    found = set()
    for cell in used_cells(modules, top, bits, stops):
        if cell["type"] not in ("$eq", "$logic_not"):
            continue
        operand = tuple(cell["connections"]["A"])
        for slot in range(len(operand_bus) // width):
            if operand == operand_bus[width * slot:width * (slot + 1)]:
                if cell["type"] == "$logic_not":
                    found.add(0)
                else:
                    found.add(constant_value(tuple(cell["connections"]["B"]),
                                             "comparator"))
    return found


def word_groups(modules, bits, stops):
    """The distinct `DG_*` constants the word's `hits` comparators test.

    Every one of the six slots must compare its group with the same constant;
    anything else (a per-slot group, a non-constant operand) is rejected.
    """
    top = modules[TOP]
    found = comparators(modules, top, bits, stops, net(top, "grp_v", 30), 5)
    require(found, "word: no group comparator in the pick's cone")
    require(len(found) == 1, f"word: slots compare different groups {sorted(found)}")
    return found.pop()


def sym_lines(modules, bits, stops):
    """The `L.SYM` line constants the per-line pick's mask tests."""
    top = modules[TOP]
    found = comparators(modules, top, bits, stops, net(top, "xl", 4), 2)
    require(len(found) == 1,
            f"line pick: expected one line constant, found {sorted(found)}")
    return found.pop()


def extract_cone(top, name, roots, frees, width=None):
    """One cone: bind the free leaves, then read the root expressions."""
    cone = MovesCone(name, top)
    for leaf, bits, value in frees:
        cone.overwrite(leaf, bits, value)
    expressions = {}
    for root, root_width in roots:
        expressions[root] = cone.expression(net(top, root, root_width))
    return cone, expressions


def extract_leaf_bool(top, name, root, frees):
    cone, _ = extract_cone(top, name, [(root, 1)], frees)
    return cone, cone.expression(net(top, root, 1))


def register_step(modules, name, current, frees):
    """A register's next-state cone as a function of the free leaves."""
    top = modules[TOP]
    cone = MovesCone(name, top)
    for leaf, bits, value in frees:
        cone.overwrite(leaf, bits, value)
    data = cone.register(name, 1, current)
    return cone, cone.expression(data)


def extract_moves(modules, params):
    """Extract every cone of the cut, checking the elaborated constants."""
    top = modules[TOP]
    documented = {value for key, value in params.items() if key.startswith("dg_")}

    map_cone, map_expr = extract_cone(top, "map", [("grp_v", 30)], MAP_FREE)
    valid_cone, valid = extract_cone(top, "valid", [("mv_valid", 6)], ARB_FREE)
    win_cone, win = extract_cone(top, "win", [("mv_win", 6)], ARB_FREE)
    ev_cone, ev = extract_cone(top, "conflict", [("conflict_ev", 1)], ARB_FREE)

    words = []
    for netname, suffix in WORD_NETS:
        bits = net(top, netname, 15)
        group = word_groups(modules, bits, free_bits(top, WORD_FREE))
        require(group in documented,
                f"{netname}: group {group} is not a documented DG_* code")
        require(group != params["dg_none"], f"{netname}: picks the NULL group")
        cone, _ = extract_cone(top, f"w{suffix}", [(netname, 15)], WORD_FREE)
        words.append({"net": netname, "name": f"rtlWord{suffix}", "group": group,
                      "lines": cone.lines, "expr": cone.expression(bits)})

    sym_words = []
    for netname, suffix, line in SYM_NETS:
        bits = net(top, netname, 15)
        group = word_groups(modules, bits, free_bits(top, SYM_FREE))
        require(group == params["dg_l_sym"],
                f"{netname}: the line pick does not test DG_L_SYM")
        found_line = sym_lines(modules, bits, free_bits(top, SYM_FREE))
        require(found_line == line,
                f"{netname}: the line comparator reads {found_line}, not {line}")
        cone, _ = extract_cone(top, f"s{suffix}", [(netname, 15)], SYM_FREE)
        sym_words.append({"net": netname, "name": f"rtlSymWord{suffix}", "line": line,
                          "lines": cone.lines, "expr": cone.expression(bits)})

    return {"params": params, "map": map_cone, "map_expr": map_expr["grp_v"],
            "valid": valid_cone, "valid_expr": valid["mv_valid"],
            "win": win_cone, "win_expr": win["mv_win"],
            "ev": ev_cone, "ev_expr": ev["conflict_ev"],
            "words": words, "sym_words": sym_words}


def extract_sticky(modules, params, header):
    top = modules[TOP]
    sticky = corectl.extract_strobe(modules, "c_wr_stk", header,
                                    "ctrl_base", "ctrl_span", "ctrl_offset")
    conflict_cone, conflict_expr = register_step(
        modules, "conflict", "state",
        (("rst_q", 1, "resetN"), ("conflict_ev", 1, "ev"), ("c_wr_stk", 1, "stk"),
         ("h_wd", 8, "hd")))
    memhaz_cone, memhaz_expr = register_step(
        modules, "memhaz", "state",
        (("rst_q", 1, "resetN"), ("memhaz_ev", 1, "ev"), ("c_wr_stk", 1, "stk"),
         ("h_wd", 8, "hd")))
    mev_cone, mev_expr = extract_leaf_bool(
        top, "memhazev", "memhaz_ev",
        (("p_haz", 1, "haz"), ("p_rdy", 1, "ready"), ("rd_pd", 6, "rdPd")))
    inv_cone, inv_expr = register_step(
        modules, "inv", "state",
        (("rst_q", 1, "resetN"), ("c_wr_hin", 1, "hostWrite"), ("rd_hin", 6, "rdHin")))
    hin_cone, hin = extract_cone(top, "rdhin", [("rd_hin", 6)],
                                 (("mv_en", 6, "en"), ("c_src", 36, "src")))
    pd_cone, pd = extract_cone(top, "rdpd", [("rd_pd", 6)],
                               (("mv_en", 6, "en"), ("c_src", 36, "src")))
    return {"sticky": sticky, "conflict_lines": conflict_cone.lines,
            "conflict_expr": conflict_expr,
            "memhaz_lines": memhaz_cone.lines, "memhaz_expr": memhaz_expr,
            "mev_lines": mev_cone.lines, "mev_expr": mev_expr,
            "inv_lines": inv_cone.lines, "inv_expr": inv_expr,
            "hin_lines": hin_cone.lines, "hin_expr": hin["rd_hin"],
            "pd_lines": pd_cone.lines, "pd_expr": pd["rd_pd"]}


def lean_words(info):
    """The generated `pick` word definitions and their spec equalities."""
    group_abbrevs = []
    blocks = []
    seen = set()
    for word in info["words"]:
        group = word["group"]
        abbrev = f"dgWord{group}"
        if abbrev not in seen:
            seen.add(abbrev)
            group_abbrevs.append(
                f"/-- Write-group code {group} of `md2_map.vh`. -/\nabbrev {abbrev} : BitVec 5 := {group}")
    blocks.append("\n\n".join(group_abbrevs))
    for word in info["words"]:
        abbrev = f"dgWord{word['group']}"
        blocks.append(f"""/-- The elaborated `{word['net']}` word ({word['name'][3:]}). -/
def {word['name']} (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36) (dat : BitVec 48) :
    BitVec 15 :=
{chr(10).join(word['lines'])}
  {word['expr']}

/-- `{word['net']}` is the pick of group `{word['group']}`: the lowest-index
contender's `{{1, dst, data}}`. -/
theorem {word['name']}_spec (en : BitVec 6) (grp : BitVec 30) (dst : BitVec 36)
    (dat : BitVec 48) :
    {word['name']} en grp dst dat = (pickWord (hitsMask en grp {abbrev}) dst dat).pack := by
  simp only [{word['name']}, pickWord, hitsMask, bits6, GroupWord.pack, makeWord, chain,
    hitAt, bitAt, slice, {abbrev}]
  bv_decide""")
    for word in info["sym_words"]:
        blocks.append(f"""/-- The elaborated line-{word['line']} `L.SYM` word. -/
def {word['name']} (win : BitVec 6) (grp : BitVec 30) (xl : BitVec 4) (dst : BitVec 36)
    (dat : BitVec 48) : BitVec 15 :=
{chr(10).join(word['lines'])}
  {word['expr']}

/-- The line-{word['line']} symbol word is the pick over the line's winners. -/
theorem {word['name']}_spec (win : BitVec 6) (grp : BitVec 30) (xl : BitVec 4)
    (dst : BitVec 36) (dat : BitVec 48) :
    {word['name']} win grp xl dst dat =
      hitOr (symMask win grp xl {word['line']}) dst dat := by
  simp only [{word['name']}, hitOr, symMask, bits6, makeWord, bitAt, slice, dgLSym]
  bv_decide""")
    for word in info["words"]:
        blocks.append(f"#print axioms {word['name']}_spec")
    for word in info["sym_words"]:
        blocks.append(f"#print axioms {word['name']}_spec")
    return "\n\n".join(blocks)


def lean_moves(info, fingerprint):
    template = TEMPLATE.read_text(encoding="utf-8")
    _, table_value = machine_table()
    values = {
        "TOP": TOP,
        "FINGERPRINT": fingerprint,
        "MACHINE_TABLE": f"0x{table_value:x}",
        "STICKY_ADDR": f"0x{info['sticky']['address']:04X}",
        "MAP_LINES": "\n".join(info["map"].lines),
        "MAP_EXPR": info["map_expr"],
        "VALID_LINES": "\n".join(info["valid"].lines),
        "VALID_EXPR": info["valid_expr"],
        "WIN_LINES": "\n".join(info["win"].lines),
        "WIN_EXPR": info["win_expr"],
        "EV_LINES": "\n".join(info["ev"].lines),
        "EV_EXPR": info["ev_expr"],
        "STICKY_LINES": "\n".join(info["sticky"]["lines"]),
        "STICKY_EXPR": info["sticky"]["expression"],
        "CONFLICT_LINES": "\n".join(info["conflict_lines"]),
        "CONFLICT_EXPR": info["conflict_expr"],
        "MEMHAZ_LINES": "\n".join(info["memhaz_lines"]),
        "MEMHAZ_EXPR": info["memhaz_expr"],
        "MEMHAZ_EV_LINES": "\n".join(info["mev_lines"]),
        "MEMHAZ_EV_EXPR": info["mev_expr"],
        "INV_LINES": "\n".join(info["inv_lines"]),
        "INV_EXPR": info["inv_expr"],
        "HIN_LINES": "\n".join(info["hin_lines"]),
        "HIN_EXPR": info["hin_expr"],
        "PD_LINES": "\n".join(info["pd_lines"]),
        "PD_EXPR": info["pd_expr"],
    }
    for name, value in values.items():
        require("{{" + name + "}}" in template,
                f"MovesEquivalence.lean.in: missing {{{{{name}}}}} placeholder")
        template = template.replace("{{" + name + "}}", str(value))
    require("{{" not in template, "MovesEquivalence.lean.in: unsubstituted placeholder")
    return template


WORDS_HEADER = """import Metronome.Moves

/-!
# The elaborated per-unit `pick` words against `Metronome.Moves`

Generated by `code/tests/lean/moves_check.py` from the Yosys RTLIL of
`{{TOP}}`.  Each unit's `{we, dst, data}` word is
`pick(hits(mv_en, grp_v, G), c_dst, c_dat)` for the group the elaborated
comparators name; the four per-line `L.SYM` words are
`pick(mv_win & (grp == DG_L_SYM) & (xl == line), c_dst, c_dat)`.

What stays free: `mv_en`, `mv_win`, `grp_v`, `c_dst`, `c_dat` and `xl` — the
core pipeline, the arbitration and the line configuration are other cuts.
-/

set_option autoImplicit false
set_option exponentiation.threshold 1024
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Metronome.Moves

open Metronome.CoreCtl (bitAt slice chain GroupWord makeWord)

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {{FINGERPRINT}}

{{WORDS}}

end Metronome.Moves
"""


def axiom_audit(text):
    """Collect the `#print axioms` records from a Lean run."""
    found = {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
             for name, axioms in AXIOM_LINE.findall(text)}
    for name in NO_AXIOM_LINE.findall(text):
        found.setdefault(name, [])
    return found


def run_lean(source, filename, artifact, lake, work, evidence, timeout=900):
    """Run `lake env lean` on a generated file and keep the evidence."""
    path = Path(work) / filename
    path.write_text(source, encoding="utf-8")
    if evidence:
        (Path(evidence) / artifact).write_text(source, encoding="utf-8")
    command = [lake, "env", "lean", "-j1", "-DwarningAsError=true", str(path)]
    return run(command, HERE, timeout=timeout)


def lean_case(source, filename, artifact, lake, work, evidence, timeout=900):
    """Run one generated file, retrying once on a cold-start stall.

    Windows Lean cold starts have been observed to die with an empty log and a
    `-1` exit code; one retry keeps a transient tool-startup failure from
    failing the check, as `verify.py` does for the same reason.
    """
    for attempt in range(2):
        try:
            result = run_lean(source, filename, artifact, lake, work, evidence, timeout)
        except Exception as exc:  # subprocess.TimeoutExpired
            if attempt:
                raise MovesRejected(f"{filename}: Lean timed out after {timeout}s: {exc}")
            continue
        if result.returncode in (0, 1, 2, 3) or result.stdout.strip() or attempt:
            return result
    return result


def check_moves(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the elaborated move resolution and its generated Lean proofs.

    `rtlil_or_json` is a parsed Yosys design, a path to `design.json`, or a
    Verilog source directory to elaborate.  Evidence is written to `out_dir` as
    `<case>.moves.lean`, `<case>.moves.log`, `<case>.words.lean` and
    `<case>.words.log`.  Returns a result dictionary; a rejected cut raises
    `MovesRejected` (proof or audit) or `UnsupportedRTL` (structure or wiring).
    """
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-moves-{case}-") as tmp:
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
            params = moves_params(snapshot)
            header = corectl.header_params(snapshot)
            info = extract_moves(modules, params)
            info.update(extract_sticky(modules, params, header))
            log.append(f"Groups: {len(info['words'])} unit words, "
                       f"{len(info['sym_words'])} line picks\n")
            log.append(f"CTRL.STICKY at 0x{info['sticky']['address']:04X}\n")
            core_source = lean_moves(info, fingerprint)
            words_source = (WORDS_HEADER.replace("{{TOP}}", TOP)
                            .replace("{{FINGERPRINT}}", fingerprint)
                            .replace("{{WORDS}}", lean_words(info)))
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the extraction: {exc}\n")
            (out_dir / f"{case}.moves.log").write_text("".join(log), encoding="utf-8")
            raise

        results = []
        try:
            results.append(("moves", lean_case(
                core_source, f"MovesProof{case}.lean", f"{case}.moves.lean",
                lake, work, out_dir)))
            results.append(("words", lean_case(
                words_source, f"MovesWords{case}.lean", f"{case}.words.lean",
                lake, work, out_dir)))
        except MovesRejected:
            (out_dir / f"{case}.moves.log").write_text("".join(log), encoding="utf-8")
            raise

        axioms = {}
        for stage, result in results:
            log.append(f"== {stage} ==\n{result.stdout}")
            axioms.update(axiom_audit(result.stdout))
        failures = [f"{stage} (exit {result.returncode})"
                    for stage, result in results if result.returncode != 0]
        sorry = any("sorryAx" in result.stdout for _, result in results)
        if failures:
            outcome = "rejected by Lean: " + ", ".join(failures)
        elif sorry:
            outcome = "rejected: the proof used sorryAx"
        else:
            outcome = "accepted"
        log.append(f"-- {case}: {outcome}\n")
        (out_dir / f"{case}.moves.log").write_text("".join(log), encoding="utf-8")
        (out_dir / f"{case}.axioms.txt").write_text(
            "".join(f"{name}: {', '.join(found)}\n" for name, found in axioms.items()),
            encoding="utf-8")
        report = {
            "case": case,
            "ok": not failures and not sorry,
            "outcome": outcome,
            "exit": max(result.returncode for _, result in results),
            "words": len(info["words"]),
            "sym_words": len(info["sym_words"]),
            "sticky_addr": info["sticky"]["address"],
            "fingerprint": fingerprint,
            "sources": [out_dir / f"{case}.moves.lean", out_dir / f"{case}.words.lean"],
            "log": out_dir / f"{case}.moves.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            first = next((line.strip() for stage, result in results
                          for line in result.stdout.splitlines() if "error:" in line),
                         outcome)
            raise MovesRejected(f"{case}: {outcome}\n" + "".join(log),
                                reason=f"{outcome}: {first[:200]}",
                                code=report["exit"])
    return report


def moves_mutations():
    """The planted move-resolution regressions, as snapshot transformers."""
    def replace(name, before, after):
        def apply(snapshot):
            require(name in snapshot, f"mutation: missing {name}")
            data = snapshot[name]
            require(data.count(before.encode()) == 1,
                    f"mutation: anchor changed in {name}: {before}")
            return {**snapshot, name: data.replace(before.encode(), after.encode(), 1)}
        return apply

    return [
        # One DG_MAP entry changes group: CW.D (destination 60) becomes FLAGS.
        ("moves_map_entry", replace(
            "md2_map.vh",
            "{5'd31, 5'd31, 5'd31, 5'd25, 5'd25, 5'd25, 5'd24,",
            "{5'd31, 5'd31, 5'd31, 5'd2, 5'd25, 5'd25, 5'd24,")),
        # The NULL destination gets a group, so an enabled NULL move is valid.
        ("moves_null_group", replace(
            "md2_map.vh",
            "5'd0, 5'd0, 5'd0, 5'd31};",
            "5'd0, 5'd0, 5'd0, 5'd2};")),
        # `same_key` ignores the executing line for L.SYM.
        ("moves_same_key_line", replace(
            "project.v",
            "((ga != DG_L_SYM) || (la == lb))",
            "((ga != DG_L_SYM) || 1'b1)")),
        # `mv_win` prefers the highest (core, move index).
        ("moves_win_highest", replace(
            "project.v",
            "if (j < k) begin : g_lo",
            "if (j > k) begin : g_lo")),
        # `conflict_ev` only looks at slots 0 and 1, missing a three-way
        # conflict among the later slots.
        ("moves_conflict_three_way", replace(
            "project.v",
            "wire conflict_ev = |(mv_valid & ~mv_win);",
            "wire conflict_ev = |((mv_valid & ~mv_win) & 6'b000011);")),
        # The clear beats a same-cycle event.
        ("moves_clear_beats_event", replace(
            "project.v",
            "conflict <= conflict_ev | (conflict & ~(c_wr_stk & h_wd[0]));",
            "conflict <= (conflict_ev | conflict) & ~(c_wr_stk & h_wd[0]);")),
        # `mv_valid` ignores the group, so a NULL move counts.
        ("moves_valid_no_group", replace(
            "project.v",
            "assign mv_valid[k] = mv_en[k] & (grp[k] != DG_NONE);",
            "assign mv_valid[k] = mv_en[k];")),
        # The `hits` mask ignores the move enable.
        ("moves_hits_ignores_en", replace(
            "project.v",
            "for (q = 0; q < 6; q = q + 1) v[q] = en[q] & (g[5*q +: 5] == want);",
            "for (q = 0; q < 6; q = q + 1) v[q] = (g[5*q +: 5] == want);")),
    ]


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted move-resolution regression is rejected.

    Returns one `(case, rejected, stage, exit)` record per mutation and raises
    `MovesRejected` if any mutant is accepted.
    """
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-moves-mutants-") as tmp:
        for case, transform in moves_mutations():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_moves(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"extraction: {exc}", 1))
                continue
            except MovesRejected as exc:
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
                        help="also check the planted move-resolution regressions")
    parser.add_argument("--artifacts-dir", type=Path, default=DEFAULT_ARTIFACTS,
                        help="fresh evidence directory (default: %(default)s)")
    parser.add_argument("--check", action="store_true",
                        help="only check the transcribed table against machine.json")
    args = parser.parse_args(argv)

    if args.check:
        tables = check_tables()
        print("moves tables: machine.json, Moves.dgMapLiteral and md2_map.vh agree "
              f"on 0x{tables['value']:x} ({len(tables['table'])} codes)")
        return 0

    lake, yosys = (shutil.which(tool) for tool in ("lake", "yosys"))
    if not lake or not yosys:
        parser.error("lake and yosys must be on PATH")
    check_tables()
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
            raise MovesRejected("tool version query failed")

        source_log = []
        for path in (MOVES_LEAN, Path(__file__).resolve(), TEMPLATE, MACHINE_JSON):
            digest = hashlib.sha256(Path(path).read_bytes()).hexdigest()
            source_log.append(f"{digest}  {Path(path).relative_to(ROOT)}")
        (artifacts / "sources.log").write_text("\n".join(source_log) + "\n", encoding="utf-8")

        build = run([lake, "build", "Metronome.Moves"], HERE)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise MovesRejected("lake build Metronome.Moves failed")

        snapshot = snapshot_of(ROOT / "src")
        report = check_moves(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        emit(f"baseline: {report['outcome']} ({report['words']} unit words, "
             f"{report['sym_words']} line picks)")
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
        raise SystemExit(f"Move resolution check failed: {exc}") from exc
