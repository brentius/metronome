"""Check the elaborated core-control cones: the `CW` pick, freeze and `CTRL.STICKY`.

The core-queue cut (`Metronome.CoreQueue`) takes the picked `CW` write group
`w_cw`, the freeze flag `frz`, the arbiter's `cfg_core_issue`, the core decode
leaf `cw_is_cfg` and the `CTRL.STICKY` clear leaf `c_wr_stk & h_wd[2]` as free
per-cycle inputs.  This module closes three of those leaves on the elaborated
netlist, against the independent specification in `Metronome/CoreCtl.lean`:

1. **The `CW` pick.**  `w_cw = `PICKG(DG_CW)` is extracted from the `hits` and
   `pick` cone as a function of `mv_en`, the six `grp` buses, `c_dst` and
   `c_dat`, and proved to be the specification's priority chain: `we` is set
   exactly when some enabled move's destination is in group `DG_CW`, and the
   destination and data fields are the first such move's.  With exactly one
   contender the word is that move's `{1, dst, data}` (six index theorems); with
   none it is zero.  More than one contender is not forbidden: SPEC_V2 §6 says
   the lowest `(core, move index)` takes effect and sticky `CONFLICT` is set,
   and the assembler rejects two same-group moves only inside one instruction
   (`code/host2/metronome2_tools/asm.py`), so two cores can still collide.
2. **The freeze registers.**  `frz`, `freeze` and `frzd` are extracted and
   proved to follow SPEC_V2 §12.3 at every state and input, and the trace lift
   shows `frz` is low from reset until the first `DBG` write that sets its
   freeze bit, and that a STEP write runs exactly one cycle.
3. **The host strobes.**  `c_wr_stk` and `d_wr_dbg` are extracted as functions
   of `h_wr` and `ha` and proved equal to "host write to `CTRL.STICKY`" and
   "host write to `DBG.DBG`", so the clear leaf is a host write of that byte
   with bit 2 set.

The generated Lean then instantiates the queue's own theorems with these
definitions, so the queue's `CW.D` / `CW.AL` / `CW.AH` decode becomes a
statement about the winning move's destination and its `CWOVR` clear becomes a
statement about the `CTRL.STICKY` write.

The host-map constants (`DG_CW`, `D_CW_*`, `HA_CTRL_BASE`, `HO_CTRL_STICKY`,
...) are read from the generated headers `src/md2_map.vh` and `src/md2_defs.vh`,
and every constant found in the elaborated cells is checked against them, so a
drifted offset or group fails rather than redefining the specification.

Run it from the repository root:

    python lean/corectl_check.py
    python lean/corectl_check.py --mutations

`run_mutations()` plants the regressions on temporary copies of `src/` (never
the repository): a pick that ignores the move enable, a pick that reads the
wrong write group's winner, a freeze register with the wrong reset value, a
freeze register that never clears, a `CTRL.STICKY` decode at the wrong offset
and a `CTRL.STICKY` decode in the wrong block.
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

from rtlil import DffCone, UnsupportedRTL, require
from verify import HERE, ROOT, TOP, run, run_lean


DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_corectl_v4_20261120"
TEMPLATE = HERE / "CoreCtlEquivalence.lean.in"
AXIOM_LINE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)
NO_AXIOM_LINE = re.compile(r"^'([^']+)' does not depend on any axioms$", re.MULTILINE)

# The free input bundles of the three cones: (net name, width, Lean value).
PICK_FREE = (("mv_en", 6, "en"), ("grp_v", 30, "grp"),
             ("c_dst", 36, "dst"), ("c_dat", 48, "dat"))
FREEZE_FREE = (("rst_q", 1, "input.resetN"), ("d_wr_dbg", 1, "input.dbgWrite"),
               ("h_wd", 8, "input.data"))

# Host-map and definition constants the extracted cells must agree with.
HEADER_PARAMS = (
    ("dg_cw", r"localparam \[4:0\] DG_CW = 5'd(\d+);", 10),
    ("d_cw_al", r"localparam \[5:0\] D_CW_AL = 6'd(\d+);", 10),
    ("d_cw_ah", r"localparam \[5:0\] D_CW_AH = 6'd(\d+);", 10),
    ("d_cw_d", r"localparam \[5:0\] D_CW_D = 6'd(\d+);", 10),
    ("ctrl_base", r"localparam \[15:0\] HA_CTRL_BASE = 16'h([0-9A-Fa-f]+);", 16),
    ("ctrl_span", r"localparam \[15:0\] HSPAN_CTRL = 16'h([0-9A-Fa-f]+);", 16),
    ("ctrl_offset", r"localparam integer HO_CTRL_STICKY = (\d+);", 10),
    ("dbg_base", r"localparam \[15:0\] HA_DBG_BASE = 16'h([0-9A-Fa-f]+);", 16),
    ("dbg_span", r"localparam \[15:0\] HSPAN_DBG = 16'h([0-9A-Fa-f]+);", 16),
    ("dbg_offset", r"localparam integer HO_DBG_DBG = (\d+);", 10),
)


class CoreCtlRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated cones."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


class VectorCone(DffCone):
    """A `DffCone` that also decodes the vector cells these cones use.

    Yosys lowers `~|v` to `$reduce_or` (or to `$logic_not` of a one-bit mask),
    `~x[0]` to `$logic_not`, and the 15-bit `pick` select to a `$and` of a
    broadcast hit bit with `{1'b1, dst, data}` and an `$or` tree.  The shared
    adapter only indexes scalar logic, so those shapes are added here.
    Everything else is inherited, including the fail-closed behaviour for
    unsupported cells, missing drivers and unresolvable buses.
    """

    EXTRA = ("$reduce_or", "$reduce_bool", "$logic_not")

    def __init__(self, name, module):
        super().__init__(name, module)
        for cell_name, cell in module["cells"].items():
            if cell["type"] not in self.EXTRA:
                continue
            pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
            where = f"{name}.{cell_name} ({cell['type']})"
            require(set(pins) == {"A", "Y"} and len(pins["Y"]) == 1,
                    f"{where}: expected one scalar result")
            require(int(cell["parameters"]["Y_WIDTH"], 2) == 1,
                    f"{where}: expected a one-bit result")
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = (cell["type"], pins, cell["parameters"], where)

    def _bind(self, bits, expression):
        wire = f"{self.name}{len(self.lines)}"
        self.lines.append(f"  let {wire} := {expression}")
        self.bound[bits] = wire
        return wire

    def _nameable(self, run):
        """True if `run` can be named as one Lean expression.

        A run is nameable when it is a whole bound bus, a driven cell output, or
        a contiguous slice of a bound bus.  Single bits are excluded: they are
        bound as `Bool` scalars and assembled through `_bit_bool`.
        """
        if len(run) < 2:
            return False
        if run in self.bound or run in self.drivers:
            return True
        for key in self.bound:
            if len(run) < len(key):
                for offset in range(len(key) - len(run) + 1):
                    if key[offset:offset + len(run)] == run:
                        return True
        return False

    def _assemble(self, bits):
        """Assemble a bus from contiguous, nameable runs and constants.

        The shared adapter assembles bit by bit.  A run that is a whole bound
        bus, a driven cell output or a contiguous slice of a bound bus is named
        once and shifted into place, which keeps the generated term (and the
        bit-blasted circuit) small.  Everything else falls back to a single-bit
        assembly, so a bus outside the supported shapes still fails closed.
        """
        width = len(bits)
        covered = [False] * width
        terms, literal = [], 0
        for index in range(width):
            if covered[index]:
                continue
            run = None
            for end in range(width, index + 1, -1):
                if self._nameable(bits[index:end]):
                    run = bits[index:end]
                    break
            covered[index] = True
            if run is None:
                if bits[index] == "1":
                    literal |= 1 << index
                elif bits[index] != "0":
                    value = self._bit_bool(bits[index])
                    terms.append(f"(if {value} then "
                                 f"(BitVec.shiftLeft (1 : BitVec {width}) {index}) "
                                 f"else (0 : BitVec {width}))")
                continue
            value = self.expression(run)
            sized = f"(BitVec.setWidth {width} {value})"
            terms.append(sized if index == 0 else f"(BitVec.shiftLeft {sized} {index})")
            for offset in range(index, index + len(run)):
                covered[offset] = True
        if literal:
            terms.append(f"({literal} : BitVec {width})")
        require(terms, f"{self.name}: empty bus assembly")
        return "(" + " ||| ".join(terms) + ")"

    def _bit_bool(self, bit):
        """A one-bit net as a Lean `Bool`, including one-bit muxes."""
        for output, (kind, _, _, _) in self.drivers.items():
            if len(output) == 1 and output[0] == bit and (
                    kind == "$mux" or kind in self.EXTRA):
                return self.expression(output)
        return super()._bit_bool(bit)

    def overwrite(self, name, width, value):
        """Bind a driven bus as a free input, dropping cells inside it.

        `grp_v` is the concatenation of the six `grp` lookups, so the shared
        adapter indexed each five-bit lookup as its own driver.  Binding the
        whole bus makes those cells unreachable; any other cell that overlaps
        the bus partially still fails the extraction.
        """
        net = self.module["netnames"].get(name)
        require(net is not None, f"{self.name}.{name}: missing net")
        bits = set(tuple(net["bits"]))
        require(len(bits) == width, f"{self.name}.{name}: expected {width} bits")
        for key in list(self.drivers):
            overlap = bits & set(key)
            require(not overlap or set(key) <= bits,
                    f"{self.name}.{name}: partially overlaps the driver bus {key}")
            if overlap:
                del self.drivers[key]
        self.claimed -= bits
        return self.leaf(name, width, value)

    def expression(self, bits):
        driver = self.drivers.get(bits)
        if driver is None:
            return super().expression(bits)
        kind, pins, params, where = driver
        if kind in self.EXTRA:
            require(bits not in self.resolving, f"{where}: combinational loop")
            self.resolving.add(bits)
            require(len(bits) == 1, f"{where}: expected a one-bit result")
            source = pins["A"]
            require(len(source) == int(params["A_WIDTH"], 2) and len(source) > 0,
                    f"{where}: unexpected operand width")
            if kind in ("$reduce_or", "$reduce_bool"):
                expression = "(" + " || ".join(
                    f"({self._bit_bool(bit)})" for bit in source) + ")"
            elif len(source) == 1:
                expression = f"(!{self._bit_bool(source[0])})"
            else:
                expression = f"({self.expression(source)} == (0 : BitVec {len(source)}))"
            self.resolving.remove(bits)
            return self._bind(bits, expression)
        if kind not in ("$and", "$or") or len(bits) == 1:
            if kind == "$mux" and len(bits) == 1:
                # A one-bit mux is a Lean `Bool` here, like every other scalar net.
                require(bits not in self.resolving, f"{where}: combinational loop")
                self.resolving.add(bits)
                select = pins["S"]
                require(len(select) == 1 and len(pins["A"]) == 1 and len(pins["B"]) == 1,
                        f"{where}: expected a one-bit mux")
                expression = (f"(if {self._bit_bool(select[0])} then "
                              f"{self._bit_bool(pins['B'][0])} else "
                              f"{self._bit_bool(pins['A'][0])})")
                self.resolving.remove(bits)
                return self._bind(bits, expression)
            return super().expression(bits)
        # A wide bitwise AND/OR, including the broadcast shape of `{15{hit}} & w`.
        require(bits not in self.resolving, f"{where}: combinational loop")
        self.resolving.add(bits)
        width = len(bits)
        left, right = pins["A"], pins["B"]
        require(len(left) == int(params["A_WIDTH"], 2) and
                len(right) == int(params["B_WIDTH"], 2) and
                int(params["Y_WIDTH"], 2) == width and
                len(left) == len(right) == width,
                f"{where}: expected an equal-width bitwise cell")
        if len(set(left)) == 1 and len(set(right)) == 1:
            expression = (f"(if {self._bit_bool(left[0])} && {self._bit_bool(right[0])} "
                          f"then BitVec.allOnes {width} else (0 : BitVec {width}))")
        elif len(set(left)) == 1:
            inner = self.expression(right)
            bit = self._bit_bool(left[0])
            expression = (f"(if {bit} then {inner} else (0 : BitVec {width}))"
                          if kind == "$and" else
                          f"(if {bit} then BitVec.allOnes {width} else {inner})")
        elif len(set(right)) == 1:
            inner = self.expression(left)
            bit = self._bit_bool(right[0])
            expression = (f"(if {bit} then {inner} else (0 : BitVec {width}))"
                          if kind == "$and" else
                          f"(if {bit} then BitVec.allOnes {width} else {inner})")
        else:
            operator = "&&&" if kind == "$and" else "|||"
            expression = f"({self.expression(left)} {operator} {self.expression(right)})"
        self.resolving.remove(bits)
        return self._bind(bits, expression)


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
    result = run([yosys, "-Q", "-q", "-p", commands], work, timeout=600)
    if result.returncode != 0:
        raise CoreCtlRejected(f"Yosys elaboration failed: {result.stdout.strip()}")
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


def header_params(snapshot):
    """Read the documented host-map and destination constants from the headers."""
    text = "".join(snapshot[name].decode("latin-1") for name in sorted(snapshot)
                   if name.endswith(".vh"))
    values = {}
    for name, pattern, base in HEADER_PARAMS:
        match = re.search(pattern, text)
        require(match is not None, f"{name}: constant pattern changed in the headers")
        values[name] = int(match.group(1), base)
    require(values["ctrl_offset"] < values["ctrl_span"],
            "HO_CTRL_STICKY is outside the CTRL window")
    require(values["dbg_offset"] < values["dbg_span"],
            "HO_DBG_DBG is outside the DBG window")
    return values


def net(top, name, width):
    """The bits of a named top-level net."""
    entry = top["netnames"].get(name)
    require(entry is not None, f"{TOP}.{name}: missing net")
    bits = tuple(entry["bits"])
    require(len(bits) == width, f"{TOP}.{name}: expected {width} bits, got {len(bits)}")
    return bits


def drivers(top):
    """One driver per net bit, with a fail-closed double-driver check."""
    found = {}
    for name, cell in top["cells"].items():
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] not in ("output", "inout"):
                continue
            for bit in bits:
                require(bit not in found, f"{TOP}: bit {bit} has two drivers")
                found[bit] = (name, pin)
    return found


def cell_value(bits):
    """A constant bus (little-endian) as an integer, or `None` if not constant."""
    if not bits or not all(bit in ("0", "1") for bit in bits):
        return None
    return int("".join(reversed(bits)), 2)


def eq_constants(top, operand):
    """Every `$eq` constant compared with the given operand bus.

    A comparison against another bus (the RTL's `same_key` compares two group
    codes with each other) is not a decode constant and is skipped.
    """
    operand = tuple(operand)
    values = set()
    for cell in top["cells"].values():
        if cell["type"] != "$eq":
            continue
        if tuple(cell["connections"]["A"]) != operand:
            continue
        require(int(cell["parameters"]["B_WIDTH"], 2) == len(operand),
                "$eq operand widths disagree")
        value = cell_value(cell["connections"]["B"])
        if value is not None:
            values.add(value)
    return values


REGISTERS = ("$dff", "$adff", "$sdff", "$dffe", "$adffe", "$sr")


def is_cell_leaf(modules, cell):
    """True if the cell is a module instance or a register, not builtin logic."""
    kind = cell["type"]
    return (kind in modules or "\\" in kind or kind in REGISTERS or
            not kind.startswith("$"))


def cone_of(modules, top, roots):
    """Every combinational builtin cell reachable from these net bits.

    Module instances, parameterized instances and registers are boundaries: a
    bit they drive is a leaf, so the walk stops at the cut's inputs instead of
    descending into other blocks.
    """
    index = drivers(top)
    seen, stack, cells = set(), list(roots), []
    walked = set()
    while stack:
        bit = stack.pop()
        if bit in seen or bit in ("0", "1"):
            continue
        seen.add(bit)
        owner = index.get(bit)
        if owner is None:
            continue
        cell = top["cells"][owner[0]]
        if is_cell_leaf(modules, cell) or id(cell) in walked:
            continue
        walked.add(id(cell))
        cells.append(cell)
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] == "input":
                stack.extend(bits)
    return cells


def extract_pick(modules, params):
    """Extract `w_cw` as a function of the move bus and check its group decode."""
    top = modules[TOP]
    pick_cells = cone_of(modules, top, net(top, "w_cw", 15))
    group_bus = net(top, "grp_v", 30)
    for k in range(6):
        operand = group_bus[5 * k:5 * k + 5]
        found = {cell_value(cell["connections"]["B"]) for cell in pick_cells
                 if cell["type"] == "$eq" and tuple(cell["connections"]["A"]) == operand}
        found.discard(None)
        require(found == {params["dg_cw"]},
                f"w_cw: group comparator {k} compares with {sorted(found)}, "
                f"not DG_CW = {params['dg_cw']}")
    code = net(top, "w_cw", 15)[8:14]
    found = eq_constants(top, code)
    expected = {params["d_cw_al"], params["d_cw_ah"], params["d_cw_d"]}
    require(found == expected,
            f"w_cw: destination codes are {sorted(found)}, not {sorted(expected)}")
    write_data = cone_of(modules, top, net(top, "cw_write_data", 1))
    compared = {cell_value(cell["connections"]["B"]) for cell in write_data
                if cell["type"] == "$eq" and tuple(cell["connections"]["A"]) == code}
    compared.discard(None)
    require(compared == {params["d_cw_d"]},
            f"cw_write_data: compares with {sorted(compared)}, "
            f"not D_CW_D = {params['d_cw_d']}")

    cone = VectorCone("wcw", top)
    for name, width, value in PICK_FREE:
        cone.overwrite(name, width, value)
    expression = cone.expression(net(top, "w_cw", 15))
    return {"lines": list(cone.lines), "expression": expression}


def extract_freeze(modules):
    """Extract the three freeze registers' next-state cone."""
    top = modules[TOP]
    cone = VectorCone("frz", top)
    for name, width, value in FREEZE_FREE:
        cone.overwrite(name, width, value)
    freeze_d = cone.register("freeze", 1, "state.freeze")
    frz_d = cone.register("frz", 1, "state.frz")
    frzd_d = cone.register("frzd", 1, "state.frzd")
    freeze = cone.expression(freeze_d)
    frz = cone.expression(frz_d)
    frzd = cone.expression(frzd_d)
    return {"lines": list(cone.lines), "freeze": freeze, "frz": frz, "frzd": frzd}


def extract_strobe(modules, name, params, base_key, span_key, offset_key):
    """Extract `wr & (addr - base < span) & (addr - base == offset)`.

    The three constants must be the documented ones, the span comparison must be
    on the subtracted offset and the offset comparison on its zero extension, so
    a drifted decode fails here rather than redefining the specification.
    """
    top = modules[TOP]
    address = net(top, "ha", 16)
    probe = net(top, name, 1)
    cells = cone_of(modules, top, probe)
    kinds = {}
    for cell in cells:
        kinds.setdefault(cell["type"], []).append(cell)
        require(cell["type"] in ("$and", "$logic_and", "$or", "$logic_or", "$not",
                                 "$logic_not", "$reduce_or", "$reduce_bool",
                                 "$eq", "$lt", "$sub"),
                f"{name}: unexpected {cell['type']} in the address strobe cone")
    tests = kinds.get("$eq", []) + kinds.get("$logic_not", [])
    require(len(kinds.get("$sub", [])) == 1 and len(kinds.get("$lt", [])) == 1 and
            len(tests) == 1,
            f"{name}: expected one subtraction, one span comparison and one offset "
            f"comparison, found {sorted(kinds)}")
    sub, lt, test = kinds["$sub"][0], kinds["$lt"][0], tests[0]
    require(tuple(sub["connections"]["A"]) == address,
            f"{name}: the base subtraction does not read the host address")
    offset = tuple(sub["connections"]["Y"])
    require(tuple(lt["connections"]["A"]) == offset,
            f"{name}: the span comparison is not on the offset")
    width = len(test["connections"]["A"])
    require(tuple(test["connections"]["A"]) == offset + ("0",) * (width - len(offset)),
            f"{name}: the offset comparison is not the zero-extended offset")
    # `offset == 0` lowers to `$logic_not(offset)`; any other offset is an `$eq`.
    off = 0 if test["type"] == "$logic_not" else cell_value(test["connections"]["B"])
    base = cell_value(sub["connections"]["B"])
    span = cell_value(lt["connections"]["B"])
    require(base is not None and span is not None and off is not None,
            f"{name}: the address strobe's operands are not constants")
    require(base == params[base_key], f"{name}: base 0x{base:04X} is not the host map's")
    require(span == params[span_key], f"{name}: span {span} is not the host map's")
    require(off == params[offset_key], f"{name}: offset {off} is not the host map's")

    cone = VectorCone(name, top)
    cone.overwrite("h_wr", 1, "wr")
    cone.overwrite("ha", 16, "ha")
    expression = cone.expression(probe)
    return {"lines": list(cone.lines), "expression": expression,
            "base": base, "span": span, "offset": off,
            "address": (base + off) & 0xFFFF}


def extract_sticky_bit(modules):
    """The `h_wd` bit the `CWOVR` clear term uses, read from the next state.

    The clear term is `c_wr_stk & h_wd[k]` inside `cw_overrun`'s next state.  The
    queue cut takes that whole term as its leaf, so this read ties the
    *documented* bit 2 (SPEC_V2 §13.1) to the elaborated net: a clear that
    selects another bit fails the generated `stickyBit = 2`.
    """
    top = modules[TOP]
    overrun = net(top, "cw_overrun", 1)
    matches = [cell for cell in top["cells"].values()
               if cell["type"] == "$dff" and tuple(cell["connections"]["Q"]) == overrun]
    require(len(matches) == 1, "cw_overrun: expected exactly one register")
    cells = cone_of(modules, top, matches[0]["connections"]["D"])
    sticky = net(top, "c_wr_stk", 1)
    data = net(top, "h_wd", 8)
    found = set()
    for cell in cells:
        if cell["type"] not in ("$and", "$logic_and"):
            continue
        left = tuple(cell["connections"]["A"])
        right = tuple(cell["connections"]["B"])
        for near, far in ((left, right), (right, left)):
            if near == sticky and len(far) == 1 and far[0] in data:
                found.add(data.index(far[0]))
    require(len(found) == 1,
            "cw_overrun: expected one c_wr_stk & h_wd[k] clear term, "
            f"found bits {sorted(found)}")
    return found.pop()


def lean_corectl(info, fingerprint):
    """Emit the Lean module for the extracted cones and the composition."""
    template = TEMPLATE.read_text(encoding="utf-8")
    values = {
        "TOP": TOP,
        "FINGERPRINT": fingerprint,
        "DG_CW": info["params"]["dg_cw"],
        "D_CW_AL": info["params"]["d_cw_al"],
        "D_CW_AH": info["params"]["d_cw_ah"],
        "D_CW_D": info["params"]["d_cw_d"],
        "STICKY_ADDR": f"0x{info['sticky']['address']:04X}",
        "CTRL_BASE": info["sticky"]["base"],
        "CTRL_SPAN": info["sticky"]["span"],
        "CTRL_OFFSET": info["sticky"]["offset"],
        "DBG_ADDR": f"0x{info['dbg']['address']:04X}",
        "DBG_BASE": info["dbg"]["base"],
        "DBG_SPAN": info["dbg"]["span"],
        "DBG_OFFSET": info["dbg"]["offset"],
        "WCW_LINES": "\n".join(info["pick"]["lines"]),
        "WCW_EXPR": info["pick"]["expression"],
        "FRZ_LINES": "\n".join(info["freeze"]["lines"]),
        "FREEZE_EXPR": info["freeze"]["freeze"],
        "FRZ_EXPR": info["freeze"]["frz"],
        "FRZD_EXPR": info["freeze"]["frzd"],
        "STICKY_LINES": "\n".join(info["sticky"]["lines"]),
        "STICKY_EXPR": info["sticky"]["expression"],
        "STICKY_BIT": info["sticky_bit"],
        "DBG_LINES": "\n".join(info["dbg"]["lines"]),
        "DBG_EXPR": info["dbg"]["expression"],
    }
    for name, value in values.items():
        require("{{" + name + "}}" in template,
                f"CoreCtlEquivalence.lean.in: missing {{{{{name}}}}} placeholder")
        template = template.replace("{{" + name + "}}", str(value))
    require("{{" not in template, "CoreCtlEquivalence.lean.in: unsubstituted placeholder")
    return template


def axiom_audit(text):
    """Collect the `#print axioms` records from a Lean run."""
    found = {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
             for name, axioms in AXIOM_LINE.findall(text)}
    for name in NO_AXIOM_LINE.findall(text):
        found.setdefault(name, [])
    return found


def check_corectl(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the elaborated control cones and their generated Lean proofs.

    `rtlil_or_json` is a parsed Yosys design, a path to `design.json`, or a
    Verilog source directory to elaborate.  Evidence is written to `out_dir` as
    `<case>.corectl.lean` and `<case>.log`.  Returns a result dictionary; a
    rejected cone raises `CoreCtlRejected` (proof or audit) or `UnsupportedRTL`
    (extraction).
    """
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-corectl-{case}-") as tmp:
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
            params = header_params(snapshot)
            info = {"params": params,
                    "pick": extract_pick(modules, params),
                    "freeze": extract_freeze(modules),
                    "sticky": extract_strobe(modules, "c_wr_stk", params,
                                             "ctrl_base", "ctrl_span", "ctrl_offset"),
                    "sticky_bit": extract_sticky_bit(modules),
                    "dbg": extract_strobe(modules, "d_wr_dbg", params,
                                          "dbg_base", "dbg_span", "dbg_offset")}
            log.append(f"Pick: DG_CW = {params['dg_cw']}, "
                       f"{len(info['pick']['lines'])} intermediate signals\n")
            log.append(f"CTRL.STICKY at 0x{info['sticky']['address']:04X} "
                       f"(clear bit {info['sticky_bit']}), "
                       f"DBG.DBG at 0x{info['dbg']['address']:04X}\n")
            source = lean_corectl(info, fingerprint)
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the extraction: {exc}\n")
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise
        result = run_lean(source, "CoreCtlProof.lean", f"{case}.corectl.lean",
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
            "signals": len(info["pick"]["lines"]),
            "sticky_addr": info["sticky"]["address"],
            "sticky_bit": info["sticky_bit"],
            "dbg_addr": info["dbg"]["address"],
            "fingerprint": fingerprint,
            "source": out_dir / f"{case}.corectl.lean",
            "log": out_dir / f"{case}.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            first = next((line.strip() for line in result.stdout.splitlines()
                          if "error:" in line), outcome)
            first = first.split("CoreCtlProof.lean:", 1)[-1]
            raise CoreCtlRejected(f"{case}: {outcome}\n" + "".join(log),
                                  reason=f"{outcome}: {first[:200]}",
                                  code=result.returncode)
    return report


def corectl_mutations():
    """The planted regressions, as snapshot transformers."""
    def replace(name, before, after):
        def apply(snapshot):
            require(name in snapshot, f"mutation: missing {name}")
            data = snapshot[name]
            require(data.count(before.encode()) == 1,
                    f"mutation: anchor changed in {name}: {before}")
            return {**snapshot, name: data.replace(before.encode(), after.encode(), 1)}
        return apply

    return OrderedDict((
        # The pick's hit bit ignores `mv_en`: a disabled move wins its group, so
        # `w_cw` claims a `CW.D` that never issued.
        ("pick_ignores_we", replace(
            "project.v",
            "for (q = 0; q < 6; q = q + 1) v[q] = en[q] & (g[5*q +: 5] == want);",
            "for (q = 0; q < 6; q = q + 1) v[q] = (g[5*q +: 5] == want);")),
        # The `CW` group word is the FLAGS group's winner: the destination, data
        # and `we` bit all belong to the wrong group.
        ("pick_wrong_group", replace(
            "project.v",
            "wire [14:0] w_cw = `PICKG(DG_CW);",
            "wire [14:0] w_cw = `PICKG(DG_FLAGS);")),
        # The freeze register resets set instead of clear.
        ("frz_wrong_reset", replace(
            "project.v",
            "freeze <= 1'b0; frz <= 1'b0; frzd <= 1'b0;",
            "freeze <= 1'b0; frz <= 1'b1; frzd <= 1'b0;")),
        # The freeze register never releases without a reset.
        ("frz_never_clears", replace(
            "project.v",
            "else          frz <= freeze;",
            "else          frz <= frz | freeze;")),
        # The STICKY decode compares with the next offset.
        ("sticky_wrong_offset", replace(
            "project.v",
            "wire c_wr_stk   = w_ctl & (o_ctl == HO_CTRL_STICKY);",
            "wire c_wr_stk   = w_ctl & (o_ctl == HO_CTRL_STICKY + 1);")),
        # The STICKY decode watches the DBG block instead of CTRL.
        ("sticky_wrong_block", replace(
            "project.v",
            "wire c_wr_stk   = w_ctl & (o_ctl == HO_CTRL_STICKY);",
            "wire c_wr_stk   = w_dbg & (o_ctl == HO_CTRL_STICKY);")),
        # The STICKY strobe no longer requires a host write: the address alone
        # clears CWOVR.  The three address cells keep their documented constants,
        # so only the Boolean equivalence catches this one.
        ("sticky_no_write", replace(
            "project.v",
            "wire c_wr_stk   = w_ctl & (o_ctl == HO_CTRL_STICKY);",
            "wire c_wr_stk   = w_ctl | (o_ctl == HO_CTRL_STICKY);")),
        # The CWOVR clear selects h_wd[3] instead of the documented STICKY bit 2.
        ("sticky_wrong_bit", replace(
            "project.v",
            "(cw_overrun & ~(c_wr_stk & h_wd[2]))",
            "(cw_overrun & ~(c_wr_stk & h_wd[3]))")),
    ))


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted core-control regression is rejected.

    Returns one `(case, rejected, stage, exit)` record per mutation and raises
    `UnsupportedRTL` if any mutant is accepted.
    """
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-corectl-mutants-") as tmp:
        for case, transform in corectl_mutations().items():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_corectl(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"extraction: {exc}", 1))
                continue
            except CoreCtlRejected as exc:
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
                        help="also check the planted core-control regressions")
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
            raise CoreCtlRejected("tool version query failed")

        build = run([lake, "build", "Metronome.CoreCtl"], HERE)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise CoreCtlRejected("lake build Metronome.CoreCtl failed")

        snapshot = snapshot_of(ROOT / "src")
        try:
            report = check_corectl(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        except CoreCtlRejected as exc:
            emit(f"baseline: {exc.reason}")
            records.append(("baseline", exc.reason, exc.code, False))
            return 1
        emit(f"baseline: {report['outcome']} ({report['signals']} pick signals, "
             f"CTRL.STICKY at 0x{report['sticky_addr']:04X} bit {report['sticky_bit']}, "
             f"DBG.DBG at 0x{report['dbg_addr']:04X})")
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
        raise SystemExit(f"Core-control check failed: {exc}") from exc
