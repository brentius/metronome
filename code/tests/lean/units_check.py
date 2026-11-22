"""Check the four engine data units of the Metronome chip top in Lean.

`verify.py`, `hostcmd_check.py`, `corectl_check.py` and the other cuts cover the
configuration and host plumbing.  This cut covers the data units of SPEC_V2
§6.1: the counters `CNT0..CNT2`, the shifters `SH0, SH1`, the LFSR/CRC units
`LF0, LF1` and the accumulator `A` with its scratch registers `R0..R3`.

For every unit it re-elaborates the design with `verify.py`'s Yosys recipe,
checks the chip-top wiring of the unit instances, extracts each register's
next-state cone from the elaborated module as a Lean function, and emits Lean
that proves the extracted transition equal to `Metronome.Units`' independent
statement of the specification (`UnitsEquivalence.lean.in`).  It then lifts the
one-step equality to traces and audits the axiom dependencies.

Run it from the repository root:

    python code/tests/lean/units_check.py
    python code/tests/lean/units_check.py --mutations

`run_mutations()` plants the required regressions on temporary copies of `src/`
(never the repository): a counter that wraps instead of saturating, a shifter
whose `LEN = 0` loads 0, an LFSR that feeds back `d[1]`, an accumulator `SUB`
that reports a borrow at equality, an accumulator `CMP` that writes `A`, and a
second counter regression swapping the `LO` and `HI` byte lanes.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile

from rtlil import DffCone, UnsupportedRTL, require
from verify import HERE, ROOT, TOP, run


DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_units_v4_20261121"
TEMPLATE = HERE / "UnitsEquivalence.lean.in"
AXIOM_LINE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)
NO_AXIOM_LINE = re.compile(r"^'([^']+)' does not depend on any axioms$", re.MULTILINE)

ACC_MODULE_HINT = "md2_acc"


class UnitsRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated unit cut."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


class UnitCone(DffCone):
    """A `DffCone` with the cell shapes the four data units elaborate to.

    On top of `rtlil.DffCone` this adds Yosys's `$pmux` (a `case` statement),
    `$xor`, multi-bit `$and`/`$or`, and `$reduce_or`/`$reduce_bool` (`!= 0`
    tests).  The extensions live here rather than in the shared adapter, which
    every other cut uses.

    Every one-bit cell output is bound as a `BitVec 1` value, even for the
    scalar comparisons and reductions that `rtlil.Cone` would emit as Lean
    `Bool`: the ALU packs those bits into a 13-bit result, so they are data as
    well as conditions.  `_bit_bool` converts such a bit to a `Bool` with
    `!= 0` wherever a select needs a condition.

    Fail-closed: a `$pmux` is only decoded when every select is an equality or
    zero test of one common bus against distinct constants (so the branches are
    mutually exclusive and the branch order cannot matter); an unsupported
    cell, a missing driver, a second register driver or an unresolvable bus
    still raises `UnsupportedRTL`.
    """

    EXTRA = ("$pmux", "$xor", "$reduce_or", "$reduce_bool", "$logic_not",
             "$gt", "$le")
    SCALAR = ("$eq", "$ne", "$ge", "$lt", "$gt", "$le", "$logic_not",
              "$logic_and", "$logic_or", "$not", "$reduce_or", "$reduce_bool",
              "$and", "$or", "$shiftx")

    def __init__(self, name, module):
        super().__init__(name, module)
        for cell_name, cell in module["cells"].items():
            kind = cell["type"]
            if kind not in self.EXTRA:
                continue
            pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
            where = f"{name}.{cell_name} ({kind})"
            if kind == "$pmux":
                width = int(cell["parameters"]["WIDTH"], 2)
                selects = int(cell["parameters"]["S_WIDTH"], 2)
                require(len(pins["Y"]) == width and len(pins["A"]) == width and
                        len(pins["B"]) == width * selects and len(pins["S"]) == selects,
                        f"{where}: unexpected pmux widths")
                pmux_selects_exclusive(module, pins["S"], where)
            elif kind in ("$reduce_or", "$reduce_bool"):
                require(len(pins["Y"]) == 1 and len(pins["A"]) > 0 and
                        len(pins["A"]) == int(cell["parameters"]["A_WIDTH"], 2),
                        f"{where}: unexpected reduction widths")
            elif kind in ("$ge", "$lt", "$gt", "$le", "$shiftx"):
                require(len(pins["Y"]) == 1, f"{where}: expected one scalar result")
            elif kind == "$logic_not":
                require(len(pins["Y"]) == 1 and len(pins["A"]) > 0 and
                        len(pins["A"]) == int(cell["parameters"]["A_WIDTH"], 2),
                        f"{where}: unexpected logic-not widths")
            else:
                require(len(pins["A"]) == len(pins["Y"]) and len(pins["A"]) > 0,
                        f"{where}: unexpected widths")
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = (kind, pins, cell["parameters"], where)

    def expression(self, bits):
        if len(bits) == 1 and all(bit in ("0", "1") for bit in bits):
            return "(1 : BitVec 1)" if bits == ("1",) else "(0 : BitVec 1)"
        driver = self.drivers.get(bits)
        if driver is not None:
            kind, pins, params, where = driver
            if len(bits) == 1 and kind in self.SCALAR:
                value = self._bool_of(kind, pins, params, where)
                return self._bind(bits, f"(if {value} then (1 : BitVec 1) else 0)")
            if kind == "$mux":
                width = int(params["WIDTH"], 2)
                require(len(bits) == width and len(pins["A"]) == len(pins["B"]) == width
                        and len(pins["S"]) == 1, f"{where}: inconsistent mux widths")
                return self._bind(
                    bits, f"(if {self._bit_bool(pins['S'][0])} then "
                          f"{self.expression(pins['B'])} else {self.expression(pins['A'])})")
            if kind == "$pmux":
                width = int(params["WIDTH"], 2)
                selects = int(params["S_WIDTH"], 2)
                require(len(bits) == width, f"{where}: unexpected result bus")
                expr = self.expression(pins["A"])
                # Higher select indices are applied first so the lowest set
                # select wins, as a Verilog `case` does; the exclusivity check
                # above makes the order immaterial.
                for index in reversed(range(selects)):
                    branch = self.expression(
                        tuple(pins["B"][index * width:(index + 1) * width]))
                    expr = f"(if {self._bit_bool(pins['S'][index])} then {branch} else {expr})"
                return self._bind(bits, expr)
            if kind in ("$xor",) or (kind in ("$and", "$or") and len(bits) > 1):
                require(len(pins["A"]) == len(pins["B"]) == len(bits),
                        f"{where}: expected an equal-width bitwise cell")
                operator = {"$and": "&&&", "$or": "|||", "$xor": "^^^"}[kind]
                return self._bind(bits, f"({self.expression(pins['A'])} {operator} "
                                        f"{self.expression(pins['B'])})")
        return super().expression(bits)

    def _bool_of(self, kind, pins, params, where):
        """The Lean `Bool` of a scalar (one-bit result) cell."""
        a = pins["A"]
        b = pins.get("B", ())
        if kind in ("$eq", "$ne"):
            require(len(a) == len(b) and len(a) > 0,
                    f"{where}: expected an equal-width comparison")
            operator = "==" if kind == "$eq" else "!="
            return f"({self.expression(a)} {operator} {self.expression(b)})"
        if kind in ("$ge", "$lt", "$gt", "$le"):
            require(len(a) == len(b) and len(a) > 0,
                    f"{where}: expected an equal-width comparison")
            operator = {"$ge": ">=", "$lt": "<", "$gt": ">", "$le": "<="}[kind]
            return f"({self.expression(a)} {operator} {self.expression(b)})"
        if kind in ("$reduce_or", "$reduce_bool"):
            require(len(a) > 0, f"{where}: expected a bus operand")
            return f"({self.expression(a)} != 0)"
        if kind == "$shiftx":
            require(len(a) > 0 and len(b) > 0, f"{where}: expected an indexed shift")
            width = len(a)
            return (f"(((BitVec.ushiftRight {self.expression(a)} "
                    f"({self.expression(b)}).toNat) &&& (1 : BitVec {width})) != 0)")
        if kind == "$logic_not":
            require(len(a) > 0, f"{where}: expected a bus operand")
            if len(a) == 1:
                return f"!{self._bit_bool(a[0])}"
            return f"({self.expression(a)} == (0 : BitVec {len(a)}))"
        if kind == "$not":
            require(len(a) == 1, f"{where}: expected scalar logic")
            return f"!{self._bit_bool(a[0])}"
        if kind in ("$and", "$logic_and", "$or", "$logic_or"):
            require(len(a) == 1 and len(b) == 1, f"{where}: expected scalar logic")
            operator = "&&" if kind in ("$and", "$logic_and") else "||"
            return f"{self._bit_bool(a[0])} {operator} {self._bit_bool(b[0])}"
        raise UnsupportedRTL(f"{where}: unsupported scalar cell")

    def _bind(self, bits, expr):
        wire = f"{self.name}{len(self.lines)}"
        self.lines.append(f"  let {wire} := {expr}")
        self.bound[bits] = wire
        return wire

    def _bit_bool(self, bit):
        if bit == "0":
            return "false"
        if bit == "1":
            return "true"
        for key, value in self.bound.items():
            if bit in key:
                index = key.index(bit)
                if len(key) == 1:
                    return f"({value} != 0)"
                return (f"((BitVec.truncate 1 (BitVec.ushiftRight {value} "
                        f"{index})) != 0)")
        for output, (kind, _, _, _) in self.drivers.items():
            if bit in output:
                index = output.index(bit)
                if len(output) == 1:
                    return f"({self.expression(output)} != 0)"
                return (f"((BitVec.truncate 1 (BitVec.ushiftRight "
                        f"{self.expression(output)} {index})) != 0)")
        raise UnsupportedRTL(f"{self.name}: undriven net bit {bit}")


def pmux_selects_exclusive(module, selects, where):
    """Require every `$pmux` select to be a distinct test of one shared bus."""
    constants = []
    shared = None
    for bit in selects:
        owners = [cell for cell in module["cells"].values()
                  if cell["port_directions"].get("Y", "") in ("output", "inout") and
                  tuple(cell["connections"]["Y"]) == (bit,)]
        require(len(owners) == 1, f"{where}: select {bit} has multiple or no driver")
        cell = owners[0]
        pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
        if cell["type"] == "$eq":
            require(pins["A"] and len(pins["A"]) == len(pins["B"]),
                    f"{where}: select {bit} is not an equal-width comparison")
            value = constant_value(pins["B"], f"{where}: select {bit}")
            bus = pins["A"]
        elif cell["type"] == "$logic_not":
            value = 0
            bus = pins["A"]
        else:
            raise UnsupportedRTL(f"{where}: select {bit} is not an equality or zero test")
        if shared is None:
            shared = bus
        require(bus == shared, f"{where}: selects test different buses")
        constants.append(value)
    require(len(set(constants)) == len(constants), f"{where}: select constants repeat")


def constant_value(bits, where):
    """Read a Yosys constant bus (little-endian) as an integer."""
    require(bits and all(bit in ("0", "1") for bit in bits),
            f"{where}: expected a constant bus")
    return int("".join(reversed(bits)), 2)


def elaborate(snapshot, work, yosys):
    """Elaborate a source snapshot with the same recipe as `verify.py`."""
    work = Path(work)
    src = work / "src"
    src.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256()
    for name, content in sorted(snapshot.items()):
        (src / name).write_bytes(content)
        digest.update(name.encode() + b"\0" + hashlib.sha256(content).digest())
    files = " ".join(f"src/{path.name}" for path in sorted(src.glob("*.v")))
    commands = (f"read_verilog -I src {files}; hierarchy -check -top {TOP}; "
                "proc; opt_clean; write_json design.json")
    result = run([yosys, "-Q", "-q", "-p", commands], work)
    if result.returncode != 0:
        raise UnitsRejected(f"Yosys elaboration failed: {result.stdout.strip()}")
    modules = json.loads((work / "design.json").read_text(encoding="utf-8"))["modules"]
    return modules, digest.hexdigest(), commands, result.stdout


def snapshot_of(directory):
    """Read a Verilog source directory as a name -> bytes mapping."""
    directory = Path(directory)
    require(directory.is_dir(), f"{directory}: expected a source directory")
    snapshot = {path.name: path.read_bytes() for path in directory.iterdir()
                if path.suffix in (".v", ".vh")}
    require(snapshot, f"{directory}: no Verilog sources")
    return snapshot


def load_modules(rtlil_or_json):
    """Accept a parsed Yosys design dictionary or a path to its JSON file."""
    if isinstance(rtlil_or_json, dict):
        return rtlil_or_json.get("modules", rtlil_or_json)
    path = Path(rtlil_or_json)
    require(path.suffix == ".json", f"{path}: expected a Yosys JSON design")
    return json.loads(path.read_text(encoding="utf-8"))["modules"]


HEADER_CONST = re.compile(
    r"localparam\s+\[(\d+):0\]\s+(\w+)\s*=\s*\d+'([dhb])([0-9A-Fa-f]+)\s*;")


def header_constants(snapshot):
    """The `[w:0] NAME = w'dN;` constants of the Verilog headers."""
    text = "".join(snapshot[name].decode("latin-1") for name in sorted(snapshot)
                   if name.endswith(".vh"))
    values = {}
    for width, name, base, digits in HEADER_CONST.findall(text):
        values[name] = int(digits, {"d": 10, "h": 16, "b": 2}[base])
    needed = ["D_ACC_LD", "D_ACC_ADD", "D_ACC_SUB", "D_ACC_AND", "D_ACC_OR",
              "D_ACC_XOR", "D_ACC_CMP", "D_SH0_LD", "D_SH1_LD", "D_SH0_SH",
              "D_SH1_SH", "D_CNT0_LO", "D_CNT1_LO", "D_CNT2_LO", "D_CNT0_HI",
              "D_CNT1_HI", "D_CNT2_HI", "D_CNT0_DEC", "D_CNT1_DEC", "D_CNT2_DEC",
              "D_LF0_ST", "D_LF1_ST", "D_LF0_B0", "D_LF0_B1", "D_LF0_B2",
              "D_LF0_B3", "D_LF1_B0", "D_LF1_B1", "D_LF1_B2", "D_LF1_B3",
              "DG_ACC", "DG_R0", "DG_R1", "DG_R2", "DG_R3", "DG_SH0", "DG_SH1",
              "DG_CNT0", "DG_CNT1", "DG_CNT2", "DG_LF0", "DG_LF1"]
    missing = [name for name in needed if name not in values]
    require(not missing, f"headers: missing constants {', '.join(missing)}")
    return values


def net(top, name, width):
    """The bits of a named top-level net."""
    entry = top["netnames"].get(name)
    require(entry is not None, f"{TOP}.{name}: missing net")
    bits = tuple(entry["bits"])
    require(len(bits) == width, f"{TOP}.{name}: expected {width} bits, got {len(bits)}")
    return bits


def bus_equals(pins, pin, bits, where):
    require(tuple(pins[pin]) == tuple(bits), f"{where}.{pin}: unexpected connection")


def instances(top, module_type):
    """The cells of a given elaborated module type, in name order."""
    return [(name, cell) for name, cell in sorted(top["cells"].items())
            if cell["type"] == module_type]


REGISTERS = ("$dff", "$adff", "$sdff", "$dffe", "$adffe", "$sr")


def cone_cells(top, roots):
    """Combinational builtin cells reachable backwards from these net bits.

    Registers and module instances are leaves: their outputs are state or
    another block's boundary, so the walk stops instead of descending.
    """
    drivers = {}
    for name, cell in top["cells"].items():
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] not in ("output", "inout"):
                continue
            for bit in bits:
                require(bit not in drivers, f"{TOP}: bit {bit} has two drivers")
                drivers[bit] = name
    cells, seen, walked = [], set(), set()
    stack = list(roots)
    while stack:
        bit = stack.pop()
        if bit in seen or bit in ("0", "1"):
            continue
        seen.add(bit)
        name = drivers.get(bit)
        if name is None:
            continue
        cell = top["cells"][name]
        if id(cell) in walked or cell["type"] in REGISTERS or "\\" in cell["type"]:
            continue
        walked.add(id(cell))
        cells.append(cell)
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] == "input":
                stack.extend(bits)
    return cells


def compares_against(cells, operand, width):
    """Constants compared with slices of one operand bus, by slice offset.

    The destination decode is `dsteq(c_dst, code)`: six comparisons, one per
    move slot, each against a `width`-bit slice of `c_dst`.  The group mask is
    the same shape against `grp_v`.  Other comparators in the backward cone
    (the `DG_MAP` table lookup compares the whole destination word) are not
    part of the decode and are ignored by the slice test.
    """
    found = {}
    operand = tuple(operand)
    for cell in cells:
        if cell["type"] != "$eq":
            continue
        a = tuple(cell["connections"]["A"])
        b = tuple(cell["connections"]["B"])
        if len(a) != width or len(b) != width:
            continue
        value = constant_value(b, "$eq")
        for offset in range(len(operand) - width + 1):
            if operand[offset:offset + width] == a:
                found.setdefault(offset, set()).add(value)
                break
    return found


def require_decode(cells, operand, width, expected, name):
    """Require every slice of `operand` to compare with exactly `expected`."""
    found = compares_against(cells, operand, width)
    offsets = sorted(found)
    require(offsets == list(range(0, len(operand), width)),
            f"{name}: comparators cover slices {offsets}, not every {width}-bit slice")
    for offset, values in found.items():
        require(values == {expected},
                f"{name}: slice {offset} compares with {sorted(values)}, not {expected}")


def check_units_top(modules, consts):
    """Check the unit instances' clock, reset, write and data wiring."""
    top = modules[TOP]
    clk = tuple(top["ports"]["clk"]["bits"])
    rst_q = net(top, "rst_q", 1)
    c_dst = net(top, "c_dst", 36)
    grp_v = net(top, "grp_v", 30)
    require(len(clk) == 1, f"{TOP}.clk: expected one bit")

    for kind, count, module_type in (("counter", 3, "md2_counter"),
                                     ("shifter", 2, "md2_shifter"),
                                     ("lfsr", 2, "md2_lfsr")):
        found = instances(top, module_type)
        require(len(found) == count,
                f"{kind}: expected {count} {module_type} instances, got {len(found)}")
        for index, (name, cell) in enumerate(found):
            pins = cell["connections"]
            where = f"{TOP}.{name}"
            bus_equals(pins, "clk", clk, where)
            bus_equals(pins, "rst_n", rst_q, where)

    counters = instances(top, "md2_counter")
    for k, (name, cell) in enumerate(counters):
        pins = cell["connections"]
        w = net(top, f"g_cn[{k}].w", 15)
        where = f"{TOP}.{name}"
        bus_equals(pins, "d", w[:8], where)
        bus_equals(pins, "we", w[14:], where)
        require(tuple(pins["sel"]) == net(top, f"g_cn[{k}].sel", 2), f"{where}.sel: not g_cn sel net")

    shifters = instances(top, "md2_shifter")
    for k, (name, cell) in enumerate(shifters):
        pins = cell["connections"]
        w = net(top, f"g_sh[{k}].w", 15)
        c = net(top, f"g_sh[{k}].c", 15)
        where = f"{TOP}.{name}"
        bus_equals(pins, "d", w[:8], where)
        bus_equals(pins, "we", w[14:], where)
        bus_equals(pins, "cfg_d", c[:5], where)
        bus_equals(pins, "cfg_we", c[14:], where)
        require(len(pins["sel"]) == 1, f"{where}.sel: expected one bit")

    lfsrs = instances(top, "md2_lfsr")
    cfg = net(top, "cfg", len(top["netnames"]["cfg"]["bits"]))
    for k, (name, cell) in enumerate(lfsrs):
        pins = cell["connections"]
        w = net(top, f"g_lf[{k}].w", 15)
        where = f"{TOP}.{name}"
        bus_equals(pins, "d", w[:8], where)
        bus_equals(pins, "we", w[14:], where)
        require(tuple(pins["sel"]) == net(top, f"g_lf[{k}].sel", 3), f"{where}.sel: not g_lf sel net")
        poly = tuple(pins["poly"])
        require(len(poly) == 32 and
                any(cfg[offset:offset + 32] == poly for offset in range(len(cfg) - 31)),
                f"{where}.poly: not a contiguous slice of cfg")

    acc = [cell for name, cell in top["cells"].items() if ACC_MODULE_HINT in cell["type"]]
    require(len(acc) == 1, f"{TOP}: expected one accumulator instance")
    acc_cell = acc[0]
    require(acc_cell["type"] in modules, "accumulator: missing specialized module")
    acc_module = modules[acc_cell["type"]]
    params = acc_module.get("parameter_default_values", {})
    require(int(params.get("NM", "0"), 2) == 6, "accumulator: NM is not 6")
    require(int(params.get("NR", "0"), 2) == 4, "accumulator: NR is not 4")
    pins = acc_cell["connections"]
    for pin, width, where in (("hit", 6, "acc_hit"), ("sel", 18, "acc_sel6"),
                              ("d", 48, "c_dat"), ("r_we", 4, "r_we"),
                              ("r_d", 32, "r_d")):
        bus_equals(pins, pin, net(top, where, width), f"{TOP}.{ACC_MODULE_HINT}")
    bus_equals(pins, "clk", clk, f"{TOP}.{ACC_MODULE_HINT}")
    bus_equals(pins, "rst_n", rst_q, f"{TOP}.{ACC_MODULE_HINT}")

    # Destination constants inside the decoded op strobes.  `LO` and `HI` have
    # their own strobe; `DEC` is the port-code fallback and has none.
    for k in range(3):
        for op, leaf in (("LO", "op_lo"), ("HI", "op_hi")):
            entry = top["netnames"].get(f"g_cn[{k}].{leaf}")
            require(entry is not None, f"{TOP}.g_cn[{k}].{leaf}: missing net")
            cells = cone_cells(top, tuple(entry["bits"]))
            require_decode(cells, c_dst, 6, consts[f"D_CNT{k}_{op}"], f"CNT{k}.{op}")
            require_decode(cells, grp_v, 5, consts[f"DG_CNT{k}"], f"CNT{k}.{op} group")

    for k, (name, cell) in enumerate(instances(top, "md2_shifter")):
        cells = cone_cells(top, tuple(cell["connections"]["sel"]))
        require_decode(cells, c_dst, 6, consts[f"D_SH{k}_SH"], f"SH{k}")
        require_decode(cells, grp_v, 5, consts[f"DG_SH{k}"], f"SH{k} group")

    for k in range(2):
        for op in ("ST", "B0", "B1", "B2"):
            name = f"g_lf[{k}].op_{op.lower()}"
            bits = top["netnames"].get(name)
            require(bits is not None, f"{TOP}.{name}: missing net")
            cells = cone_cells(top, tuple(bits["bits"]))
            require_decode(cells, c_dst, 6, consts[f"D_LF{k}_{op}"], f"LF{k}.{op}")
            require_decode(cells, grp_v, 5, consts[f"DG_LF{k}"], f"LF{k}.{op} group")

    r_we = net(top, "r_we", 4)
    for k in range(4):
        cells = cone_cells(top, r_we[k:k + 1])
        require_decode(cells, grp_v, 5, consts[f"DG_R{k}"], f"R{k} group")

    cells = cone_cells(top, net(top, "acc_hit", 6))
    require_decode(cells, grp_v, 5, consts["DG_ACC"], "acc_hit group")
    cells = cone_cells(top, net(top, "acc_sel6", 18))
    allowed = {consts[name] for name in ("D_ACC_LD", "D_ACC_ADD", "D_ACC_SUB",
                                         "D_ACC_AND", "D_ACC_OR", "D_ACC_XOR",
                                         "D_ACC_CMP")}
    found = compares_against(cells, c_dst, 6)
    require(found and all(values <= allowed for values in found.values()),
            f"acc_sel6: destination comparators are "
            f"{sorted({v for values in found.values() for v in values})}, "
            "outside the seven ACC codes")

    return {"counters": len(counters), "shifters": len(shifters),
            "lfsrs": len(lfsrs), "accumulator": acc_cell["type"]}


def _registers(module, spec):
    """Bind unit registers and return the next-state input buses."""
    cone = UnitCone("rtl", module)
    for name, width, value in spec["inputs"]:
        cone.input(name, width, as_bitvec1(value) if width == 1 else value)
    next_bits = {}
    for name, width, current in spec["registers"]:
        next_bits[name] = cone.register(
            name, width, as_bitvec1(current) if width == 1 else current)
    return cone, next_bits


def extract_counter(module):
    """Extract the counter `V` next state and the `Z` output."""
    require(len(module["ports"]["v"]["bits"]) == 16, "md2_counter: V is not 16 bits")
    cone, next_bits = _registers(module, {
        "inputs": [("rst_n", 1, "input.resetN"), ("we", 1, "input.we"),
                   ("sel", 2, "input.sel"), ("d", 8, "input.d")],
        "registers": [("v", 16, "state.v")],
    })
    fields = {name: cone.expression(bits) for name, bits in next_bits.items()}
    zcone = UnitCone("rtlz", module)
    zcone.register("v", 16, "state.v")
    zbits = tuple(module["ports"]["z"]["bits"])
    require(len(zbits) == 1, "md2_counter.z: expected one bit")
    z = f"({zcone.expression(zbits)} != 0)"
    return {"lets": "\n".join(cone.lines), "v": fields["v"],
            "z_lets": "\n".join(zcone.lines), "z": z, "registers": 1}


def extract_shifter(module):
    """Extract the shifter `D`/`CNT`/`LEN`/`MSB` next state and outputs."""
    cone, next_bits = _registers(module, {
        "inputs": [("rst_n", 1, "input.resetN"), ("we", 1, "input.we"),
                   ("sel", 1, "input.sel"), ("d", 8, "input.d"),
                   ("cfg_we", 1, "input.cfgWe"), ("cfg_d", 5, "input.cfgD")],
        "registers": [("dr", 8, "state.dr"), ("cnt", 4, "state.cnt"),
                      ("len", 4, "state.len"), ("msb", 1, "state.msb")],
    })
    fields = {name: cone.expression(bits) for name, bits in next_bits.items()}
    out = {}
    for output in ("o", "done"):
        ocone = UnitCone(f"rtl{output}", module)
        for name, width, current in (("dr", 8, "state.dr"), ("cnt", 4, "state.cnt"),
                                     ("len", 4, "state.len"), ("msb", 1, "state.msb")):
            ocone.register(name, width,
                           as_bitvec1(current) if width == 1 else current)
        bits = tuple(module["ports"][output]["bits"])
        require(len(bits) == 1, f"md2_shifter.{output}: expected one bit")
        value = f"({ocone.expression(bits)} != 0)"
        out[f"{output}_lets"] = "\n".join(ocone.lines)
        out[output] = value
    return {"lets": "\n".join(cone.lines), "dr": fields["dr"], "cnt": fields["cnt"],
            "len": fields["len"], "msb": fields["msb"], "registers": 4, **out}


def extract_lfsr(module):
    """Extract the LFSR `S` next state (the `O` bit is `S[0]`)."""
    cone, next_bits = _registers(module, {
        "inputs": [("rst_n", 1, "input.resetN"), ("we", 1, "input.we"),
                   ("sel", 3, "input.sel"), ("d", 8, "input.d"),
                   ("poly", 32, "input.poly")],
        "registers": [("s", 32, "state.s")],
    })
    fields = {name: cone.expression(bits) for name, bits in next_bits.items()}
    require(list(module["ports"]) == ["clk", "rst_n", "we", "sel", "d", "poly", "s"],
            "md2_lfsr: unexpected port list")
    return {"lets": "\n".join(cone.lines), "s": fields["s"], "registers": 1}


def extract_acc(module):
    """Extract the accumulator `A`/`Z`/`C`/`N`/`R` next state."""
    params = module.get("parameter_default_values", {})
    require(int(params.get("NM", "0"), 2) == 6, "md2_acc: NM is not 6")
    require(int(params.get("NR", "0"), 2) == 4, "md2_acc: NR is not 4")
    cone, next_bits = _registers(module, {
        "inputs": [("rst_n", 1, "input.resetN"), ("hit", 6, "input.hit"),
                   ("sel", 18, "input.sel"), ("d", 48, "input.d"),
                   ("r_we", 4, "input.rWe"), ("r_d", 32, "input.rD")],
        "registers": [("a", 8, "state.a"), ("z", 1, "state.z"),
                      ("c", 1, "state.c"), ("n", 1, "state.n"),
                      ("r", 32, "state.r")],
    })
    fields = {name: cone.expression(bits) for name, bits in next_bits.items()}
    return {"lets": "\n".join(cone.lines),
            "a": fields["a"], "z": f"({fields['z']} != 0)",
            "c": f"({fields['c']} != 0)", "n": f"({fields['n']} != 0)",
            "r": fields["r"], "registers": 5}


def extract_sel(modules, kind, index):
    """Extract the elaborated port-code decode of one unit.

    Counter: the two-bit `sel` from `op_lo`/`op_hi`.  LFSR: the three-bit `sel`
    from the four op strobes.  Accumulator: each three-bit `sel` slice as a
    function of the full 36-bit destination bus.  The shifter's one-bit `sel`
    is the group pick itself and is checked structurally instead.
    """
    top = modules[TOP]
    if kind == "counter":
        names = (f"g_cn[{index}].op_lo", f"g_cn[{index}].op_hi")
        leaves = ("opLo", "opHi")
        width = 2
    elif kind == "lfsr":
        names = tuple(f"g_lf[{index}].op_{op}" for op in ("st", "b0", "b1", "b2"))
        leaves = ("opSt", "opB0", "opB1", "opB2")
        width = 3
    else:
        raise UnsupportedRTL(f"{kind}: no extracted code decode")
    cone = UnitCone(f"sel_{kind}{index}", top)
    for name, value in zip(names, leaves):
        cone.leaf(name, 1, as_bitvec1(value))
    expr = cone.expression(net(top, f"g_{'cn' if kind == 'counter' else 'lf'}[{index}].sel",
                               width))
    return "\n".join(cone.lines), expr


def extract_acc_sel(modules, slot):
    """Extract slot `slot`'s three-bit op code as a function of `c_dst`."""
    top = modules[TOP]
    cone = UnitCone(f"accsel{slot}", top)
    cone.leaf("c_dst", 36, "cDst")
    bits = net(top, "acc_sel6", 18)[3 * slot:3 * slot + 3]
    expr = cone.expression(bits)
    return "\n".join(cone.lines), expr


def as_bitvec1(value):
    """A one-bit bus value from a Lean `Bool` (the units' scalar inputs)."""
    return f"(if {value} then (1 : BitVec 1) else 0)"


def indent(text, prefix="  "):
    return "\n".join(prefix + line for line in text.splitlines())


def lean_units(info, fingerprint):
    """Emit the extracted unit transitions and the code decodes as Lean."""
    c, s, l, a = (info["counter"], info["shifter"], info["lfsr"], info["acc"])
    counters = "\n".join(
        f"""
def rtlSel{index} (opLo opHi : Bool) : BitVec 2 :=
{indent(lets) if lets else ""}
  {expr}
""" for index, (lets, expr) in enumerate(info["counter_sel"]))
    lfsrs = "\n".join(
        f"""
def rtlSel{index} (opSt opB0 opB1 opB2 : Bool) : BitVec 3 :=
{indent(lets) if lets else ""}
  {expr}
""" for index, (lets, expr) in enumerate(info["lfsr_sel"]))
    acc_sels = "\n".join(
        f"""
def rtlSel{slot} (cDst : BitVec 36) : BitVec 3 :=
{indent(lets) if lets else ""}
  {expr}
""" for slot, (lets, expr) in enumerate(info["acc_sel"]))
    return f"""import Metronome.Units

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {fingerprint}
-- Units: the `md2_counter`, `md2_shifter`, `md2_lfsr` and `md2_acc` instances
-- of {TOP}.  Every register of every unit is sampled; the thirteen register
-- values are symbolic, as are the move, configuration and reset inputs.

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Metronome.Units.Counter

/-- The elaborated counter transition (`V`). -/
def rtlStep (state : State) (input : Input) : State :=
{c['lets']}
  ⟨{c['v']}⟩

/-- The elaborated `Z` output. -/
def rtlZ (state : State) : Bool :=
{c['z_lets']}
  {c['z']}

end Metronome.Units.Counter

namespace Metronome.Units.Shifter

/-- The elaborated shifter transition (`D`, `CNT`, `LEN`, `MSB`). -/
def rtlStep (state : State) (input : Input) : State :=
{s['lets']}
  ⟨{s['dr']}, {s['cnt']}, {s['len']}, ({s['msb']} != 0)⟩

/-- The elaborated `O` output. -/
def rtlO (state : State) : Bool :=
{s['o_lets']}
  {s['o']}

/-- The elaborated `DONE` output. -/
def rtlDone (state : State) : Bool :=
{s['done_lets']}
  {s['done']}

end Metronome.Units.Shifter

namespace Metronome.Units.Lfsr

/-- The elaborated LFSR transition (`S`). -/
def rtlStep (state : State) (input : Input) : State :=
{l['lets']}
  ⟨{l['s']}⟩

end Metronome.Units.Lfsr

namespace Metronome.Units.Acc

/-- The elaborated accumulator transition (`A`, `Z`, `C`, `N`, `R0..R3`). -/
def rtlStep (state : State) (input : Input) : State :=
{a['lets']}
  ⟨{a['a']}, {a['z']}, {a['c']}, {a['n']}, {a['r']}⟩

end Metronome.Units.Acc

namespace Metronome.Units.Counter

{counters}
end Metronome.Units.Counter

namespace Metronome.Units.Lfsr

{lfsrs}
end Metronome.Units.Lfsr

namespace Metronome.Units.Acc

{acc_sels}
end Metronome.Units.Acc

"""


def axiom_audit(text):
    """Collect the `#print axioms` records from a Lean run."""
    found = {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
             for name, axioms in AXIOM_LINE.findall(text)}
    for name in NO_AXIOM_LINE.findall(text):
        found[name] = []
    return found


def run_lean(source, filename, artifact, lake, work, evidence, timeout=900):
    """Write and check one generated Lean file, keeping the log.

    A tool-level crash (an exit code other than 0 = rejected or 1 = Lean
    reported errors) is retried once: Windows cold starts and concurrent Lean
    runs have produced races with no output at all.  A retry that still crashes
    is recorded with its own exit code and rejects the case.
    """
    path = Path(work) / filename
    path.write_text(source, encoding="utf-8")
    if evidence is not None:
        (Path(evidence) / artifact).write_text(source, encoding="utf-8")
    result = None
    for _ in range(2):
        result = run([lake, "env", "lean", "-j1", "-DwarningAsError=true", str(path)],
                     HERE, timeout=timeout)
        if result.returncode in (0, 1):
            break
    return result


def check_units(src_dir_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the four elaborated data units and their generated Lean proofs.

    `src_dir_or_json` is a Verilog source directory, a parsed Yosys design or a
    path to `design.json`.  Evidence is written to `out_dir` as
    `<case>.units.lean` and `<case>.log`.  A rejected cut raises
    `UnitsRejected` (proof or audit) or `UnsupportedRTL` (structure or wiring).
    """
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-units-{case}-") as tmp:
        work = Path(tmp)
        is_json = isinstance(src_dir_or_json, dict) or (
            isinstance(src_dir_or_json, (str, Path)) and
            Path(src_dir_or_json).suffix == ".json")
        if is_json:
            modules = load_modules(src_dir_or_json)
            fingerprint = "not recorded: parsed design JSON"
            consts = {}
        else:
            snapshot = snapshot_of(src_dir_or_json)
            modules, fingerprint, commands, yosys_log = elaborate(
                snapshot, work / "rtl", yosys)
            log.append(f"RTL snapshot SHA-256: {fingerprint}\n")
            log.append(f"Yosys command: {commands}\n")
            log.append(yosys_log)
            consts = header_constants(snapshot)

        try:
            wiring = check_units_top(modules, consts) if consts else {}
            counter = extract_counter(modules["md2_counter"])
            shifter = extract_shifter(modules["md2_shifter"])
            lfsr = extract_lfsr(modules["md2_lfsr"])
            acc_module = next(module for name, module in modules.items()
                              if ACC_MODULE_HINT in name and "paramod" in name)
            acc = extract_acc(acc_module)
            info = {
                "counter": counter, "shifter": shifter, "lfsr": lfsr, "acc": acc,
                "counter_sel": [extract_sel(modules, "counter", k) for k in range(3)],
                "lfsr_sel": [extract_sel(modules, "lfsr", k) for k in range(2)],
                "acc_sel": [extract_acc_sel(modules, slot) for slot in range(6)],
                "wiring": wiring,
            }
            log.append(f"Top wiring: {wiring}\n")
            registers = sum(info[unit]["registers"] for unit in
                            ("counter", "shifter", "lfsr", "acc"))
            log.append(f"Unit cut: {registers} registers extracted "
                       f"(counter 1, shifter 4, LFSR 1, accumulator 5)\n")
            source = lean_units(info, fingerprint)
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the structural unit check: {exc}\n")
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise
        source += TEMPLATE.read_text(encoding="utf-8")
        result = run_lean(source, "UnitsProof.lean", f"{case}.units.lean",
                          lake, work, out_dir)
        log.append(result.stdout)
        axioms = axiom_audit(result.stdout)
        if result.returncode != 0:
            outcome = f"rejected by Lean (exit {result.returncode})"
        elif "sorryAx" in result.stdout:
            outcome = "rejected: the proof used sorryAx"
        else:
            outcome = "accepted"
        log.append(f"-- {case}: {outcome}\n")
        (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
        (out_dir / f"{case}.axioms.txt").write_text(
            "".join(f"{name}: {', '.join(found)}\n" for name, found in axioms.items()),
            encoding="utf-8")
        report = {
            "case": case,
            "ok": outcome == "accepted",
            "outcome": outcome,
            "exit": result.returncode,
            "registers": registers,
            "wiring": wiring,
            "fingerprint": fingerprint,
            "source": out_dir / f"{case}.units.lean",
            "log": out_dir / f"{case}.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            first = next((line.strip() for line in result.stdout.splitlines()
                          if "error:" in line), outcome)
            first = first.split("UnitsProof.lean:", 1)[-1]
            raise UnitsRejected(f"{case}: {outcome}\n" + "".join(log),
                                reason=f"{outcome}: {first[:150]}",
                                code=result.returncode)
    return report


def units_mutations():
    """The planted data-unit regressions, as snapshot transformers."""
    def replace(name, before, after):
        def apply(snapshot):
            require(name in snapshot, f"mutation: missing {name}")
            data = snapshot[name]
            require(data.count(before.encode()) == 1,
                    f"mutation: anchor changed in {name}: {before}")
            return {**snapshot, name: data.replace(before.encode(), after.encode(), 1)}
        return apply

    return [
        # The counter wraps at zero instead of saturating (SPEC v1 §6.1 DEC).
        ("unit_counter_wrap", replace(
            "md2_counter.v",
            "v <= (v != 16'd0) ? v - 16'd1 : 16'd0;",
            "v <= v - 16'd1;")),
        # LO writes the high byte and HI the low byte.
        ("unit_counter_bytes_swap", replace(
            "md2_counter.v",
            "if (sel == 2'd0) v[7:0]  <= d;\n            if (sel == 2'd1) v[15:8] <= d;",
            "if (sel == 2'd0) v[15:8] <= d;\n            if (sel == 2'd1) v[7:0]  <= d;")),
        # LEN = 0 loads a count of zero instead of eight.
        ("unit_shifter_len_zero", replace(
            "md2_shifter.v",
            "cnt <= (len != 4'd0) ? len : 4'd8;",
            "cnt <= len;")),
        # The LFSR feeds back d[1] instead of d[0].
        ("unit_lfsr_feedback_bit", replace(
            "md2_lfsr.v",
            "3'd0: s <= d[0] ? st_d1 : st_d0;",
            "3'd0: s <= d[1] ? st_d1 : st_d0;")),
        # SUB reports a borrow at equality: C = (A > v) instead of (A >= v).
        ("unit_acc_sub_carry", replace(
            "md2_acc.v",
            "3'd2: begin res = a_i - dv; cy = (a_i >= dv); wc = 1'b1; end",
            "3'd2: begin res = a_i - dv; cy = (a_i > dv); wc = 1'b1; end")),
        # CMP writes A (it must leave the accumulator unchanged).
        ("unit_acc_cmp_writes_a", replace(
            "md2_acc.v",
            "3'd6: begin res = a_i - dv; cy = (a_i >= dv); wc = 1'b1; wa = 1'b0; end",
            "3'd6: begin res = a_i - dv; cy = (a_i >= dv); wc = 1'b1; wa = 1'b1; end")),
    ]


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted data-unit regression is rejected."""
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-units-mutants-") as tmp:
        for case, transform in units_mutations():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_units(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"structural check: {exc}", 0))
                continue
            except UnitsRejected as exc:
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
                        help="also check the planted data-unit regressions")
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
            raise UnitsRejected("tool version query failed")

        build = run([lake, "build", "Metronome.Units"], HERE, timeout=900)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise UnitsRejected("lake build Metronome.Units failed")

        snapshot = snapshot_of(ROOT / "src")
        report = check_units(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        emit(f"baseline: {report['outcome']} ({report['registers']} registers)")
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
        raise SystemExit(f"Unit check failed: {exc}") from exc

