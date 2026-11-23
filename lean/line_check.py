"""Check the Metronome line cut (SPEC_V2 section 3) against the elaborated RTL.

The line `l = 0..3` is `src/md2_line.v`, one module instantiated four times by
`g_ln` in `src/project.v`.  This cut takes the line's configuration window
(`cfg`), the winning moves (`ctl_*`, `sym_*`), the host-write enables and data
(`h_*`), the synchronised pins (`lvl`, `rise`, `fall`) and the freeze flag
(`frz`) as inputs, cuts the next-state cones of the module's fifteen registers
and its combinational outputs out of the elaborated design, and proves them
equal to `Metronome.Line`'s independent statement of SPEC_V2 section 3
(sections 3.1-3.6, 12.1 and 12.3), register by register.

The chip-top check ties each instance to its window slice, clock, reset, freeze
net, pin vectors and output nets, and requires each host-write enable to be
exactly `w_lrt & i_lrt == k & o_lrt == offset`.  The move pick (`pick(...)`) is
not in this cut: `ctl_we`/`ctl_d`/`sym_*` are module inputs here.

Run it from the repository root:

    python lean/line_check.py
    python lean/line_check.py --mutations

`check_line(src_dir_or_json, out_dir, *, lake, yosys, case="baseline")` returns
the report dictionary and raises `LineRejected` on a rejected cut;
`run_mutations(snapshot, out_dir, lake, yosys)` plants regressions on temporary
copies of `src/` (never the repository).
"""

import argparse
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile

from rtlil import DffCone, UnsupportedRTL, require
from verify import HERE, ROOT, TOP, constant_value, run


LINE_MODULE = "md2_line"
DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_line_v4_20261121"
TEMPLATE = HERE / "LineEquivalence.lean.in"
AXIOM_LINE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)

# The specification's line window: (Lean field, elaborated net, width, host byte
# offset) from machine.LINE_REGS (`code/md2/machine.json`) and the `HO_LINE_*`
# constants of src/md2_map.vh.  `check_header()` checks the header against it, so
# a moved window fails closed instead of redefining the specification.
LINE_FIELDS = (
    ("inc", "c_inc", 16, 0),
    ("mod", "c_mod", 16, 2),
    ("t0", "c_t0", 16, 4),
    ("t1", "c_t1", 16, 6),
    ("t2", "c_t2", 16, 8),
    ("pre", "c_pre", 16, 10),
    ("wlo", "c_wlo", 16, 12),
    ("whi", "c_whi", 16, 14),
    ("edge", "c_edge", 8, 16),
    ("t0edge", "c_t0e", 8, 17),
    ("pins", "c_pins", 8, 18),
    ("snap", "c_snap", 2, 19),
    ("lut0", "c_lut0", 32, 20),
    ("lut1", "c_lut1", 32, 24),
    ("hold", "c_hold", 8, 28),
)

HEADER_OFFSETS = {
    "inc": "HO_LINE_INC", "mod": "HO_LINE_MOD", "t0": "HO_LINE_T0",
    "t1": "HO_LINE_T1", "t2": "HO_LINE_T2", "pre": "HO_LINE_PRE",
    "wlo": "HO_LINE_WLO", "whi": "HO_LINE_WHI", "edge": "HO_LINE_EDGE",
    "t0edge": "HO_LINE_T0EDGE", "pins": "HO_LINE_PINS", "snap": "HO_LINE_SNAP",
    "lut0": "HO_LINE_LUT0", "lut1": "HO_LINE_LUT1", "hold": "HO_LINE_HOLD",
}

# Registers: (Lean field, elaborated net, width).
STATE_REGISTERS = (
    ("ph", "ph", 16), ("run", "run", 1), ("arm", "arm", 1), ("ren", "ren", 1),
    ("held", "held", 1), ("first", "first", 1), ("sc", "sc", 1), ("sp", "sp", 1),
    ("fired", "fired", 3), ("w", "w", 4), ("sn", "sn", 4), ("rem", "rem", 1),
    ("staged", "staged", 4), ("committed", "committed", 4),
    ("tapmiss", "tapmiss", 1),
)

# Intermediate nets of the elaborated line, in dependency order:
# (Lean name, net, width, specification expression).  Each is extracted from
# its own cone with every earlier net bound to its specification expression, so
# the proof of one layer is a shallow equation.  The final transition binds all
# of them and the register equations become definitional.
LAYERS = (
    ("rtlEdg", "edg", 1, "edge state input"),
    ("rtlE0", "e0", 1, "e0 state input"),
    ("rtlRuna", "runa", 1, "runa state input"),
    ("rtlInwin", "inwin", 1, "inwin state input"),
    ("rtlStart", "start", 1, "start state input"),
    ("rtlAccept", "accept", 1, "accept state input"),
    ("rtlN", "n", 17, "sum17 state input"),
    ("rtlOver", "over", 1, "over state input"),
    ("rtlNxw", "nxw", 17, "nxw state input"),
    ("rtlNx", "nx", 16, "nx state input"),
    ("rtlTh", "th", 16, "holdTap input"),
    ("rtlHTok", "h_tok", 1, "holdTok state input"),
    ("rtlHold", "hold", 1, "hold state input"),
    ("rtlAdv", "adv", 1, "adv state input"),
    ("rtlWrap", "wrap", 1, "wrap state input"),
    ("rtlBeatOut", "beat", 1, "beat state input"),
    ("rtlMissEv", "miss_ev", 1, "missEv state input"),
    ("rtlFiredNext", "fired_next", 3, "firedNext state input"),
    ("rtlSnap", "snap", 1, "snap state input"),
    ("rtlPhC", "ph_c", 16, "phC state input"),
    ("rtlPhF", "ph_f", 16, "phF state input"),
    ("rtlRunC", "run_c", 1, "runC state input"),
    ("rtlArmC", "arm_c", 1, "armC state input"),
    ("rtlRenC", "ren_c", 1, "renC state input"),
    ("rtlRunF", "run_f", 1, "runF state input"),
    ("rtlStarting", "starting", 1, "starting state input"),
    ("rtlStagedN", "staged_n", 4, "stagedNext state input"),
    ("rtlSegValue", "seg", 2, "seg state"),
    ("rtlPinaIn", "pina", 1, "pina input"),
    ("rtlPinbIn", "pinb", 1, "pinb input"),
    ("rtlPinaRiseIn", "pina_rise", 1, "pinaRise input"),
    ("rtlPinaFallIn", "pina_fall", 1, "pinaFall input"),
)

# Outputs that are not a single net: `tap` is a concat of three tap bits,
# `in_sym` of two LUT bits and `cap` of `{REM, SN}`.
FINAL_OUTPUTS = (
    ("rtlTapOut", "tap", 3, "tap state input"),
    ("rtlInSymOut", "in_sym", 2, "inSym state input"),
    ("rtlCapValue", "cap", 5, "cap state"),
)

# Specification definitions (not layers) that a cone's expression may contain.
SPEC_DEFS = (
    "esel", "crossing", "tlt0", "tlt1", "tlt2", "tapCross0", "tapCross1",
    "tapCross2", "cross0", "next0", "next1", "next2", "cur0", "cur1", "cur2",
    "crossBits", "nextBits", "curBits", "tap0", "tap1", "tap2", "enBits",
    "missOk", "missBits", "wNext", "tap", "cap", "inSym", "committedNext",
    "startBits", "scNext", "spNext", "armF", "renF", "pack3", "pack4", "slice",
    "bitAt", "sel", "ite_ite_zero", "ite_ite_false", "Config.edgePin", "Config.edgePol", "Config.wen",
    "Config.follow", "Config.t0Pin", "Config.t0Pol", "Config.t0src",
    "Config.pinaSel", "Config.pinbSel", "Config.hpin", "Config.hlvl",
    "Config.htap", "Config.hen",
)
LAYER_HEADS = tuple(spec.split()[0] for _n, _net, _w, spec in LAYERS)
AUX_DEFS = [name for name in SPEC_DEFS if name not in LAYER_HEADS]

# Chip-top nets the four line instances must be wired to:
# (instance port, top net, width, stride between instances).
TOP_OUTPUTS = (
    ("beat", "l_beat", 1, 1), ("tap", "l_tap", 3, 3), ("in_sym", "l_in", 2, 2),
    ("cap", "l_cap", 5, 5), ("sp", "l_sp", 1, 1), ("ph", "l_ph", 16, 16),
    ("run", "l_run", 1, 1), ("arm", "l_arm", 1, 1), ("ren", "l_ren", 1, 1),
    ("fired", "l_fired", 3, 3), ("held", "l_held", 1, 1),
    ("staged", "l_staged", 4, 4), ("committed", "l_comm", 4, 4),
    ("tapmiss", "l_tapmiss", 1, 1), ("seg", "l_seg", 2, 2),
    ("pina", "l_pina", 1, 1), ("pinb", "l_pinb", 1, 1),
    ("pina_rise", "l_parise", 1, 1), ("pina_fall", "l_pafall", 1, 1),
)


class LineRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated line cut."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


class LineCone(DffCone):
    """A `DffCone` with the cell shapes `md2_line`'s cones need.

    Added locally (the shared `rtlil.py` is unchanged): `$pmux` (the `case`
    muxes of `esel` and the symbol write), `$logic_not`, `$reduce_or`/
    `$reduce_bool`, `$gt`, `$le` (also shared), `$xor` (the `L.XOR` write) and
    multi-bit `$and`/`$or`/`$not` (the tap-bit vectors).  A one-bit bus is
    always expressed as a Lean `Bool` and a wider bus as a `BitVec`, so the
    specification's `Bool`/`BitVec` split is the cone's.  Every shape stays
    fail-closed: an unexpected width, a non-exclusive `$pmux` select, an
    unsupported cell or an unresolvable bus raises `UnsupportedRTL`.
    """

    EXTRA = ("$pmux", "$logic_not", "$reduce_or", "$reduce_bool", "$xor", "$gt", "$le")

    def __init__(self, name, module):
        super().__init__(name, module)
        self.used = set()
        for cell_name, cell in module["cells"].items():
            kind = cell["type"]
            if kind not in self.EXTRA:
                continue
            pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
            params = cell["parameters"]
            where = f"{name}.{cell_name} ({kind})"
            if kind == "$pmux":
                width = int(params["WIDTH"], 2)
                selects = int(params["S_WIDTH"], 2)
                require(len(pins["Y"]) == width and len(pins["A"]) == width and
                        len(pins["B"]) == width * selects and len(pins["S"]) == selects,
                        f"{where}: unexpected pmux widths")
                exclusive_selects(module, pins["S"], where)
            elif kind == "$logic_not":
                require(set(pins) == {"A", "Y"} and len(pins["Y"]) == 1 and
                        len(pins["A"]) == int(params["A_WIDTH"], 2),
                        f"{where}: expected one scalar result")
            elif kind in ("$reduce_or", "$reduce_bool"):
                require(len(pins["Y"]) == 1 and
                        len(pins["A"]) == int(params["A_WIDTH"], 2),
                        f"{where}: expected one scalar reduction")
            elif kind == "$xor":
                require(len(pins["Y"]) == len(pins["A"]) == len(pins["B"]) and
                        int(params["A_WIDTH"], 2) == len(pins["A"]) and
                        int(params["B_WIDTH"], 2) == len(pins["B"]),
                        f"{where}: expected an equal-width xor")
            else:
                require(len(pins["Y"]) == 1 and len(pins["A"]) == len(pins["B"]) and
                        int(params["A_WIDTH"], 2) == len(pins["A"]) and
                        int(params["B_WIDTH"], 2) == len(pins["B"]),
                        f"{where}: expected a scalar equal-width comparison")
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = (kind, pins, params, where)

    def expression(self, bits):
        if bits in self.bound:
            return self.bound[bits]
        if all(bit in ("0", "1") for bit in bits):
            if len(bits) == 1:
                return "true" if bits == ("1",) else "false"
            value = int("".join(reversed(bits)), 2)
            return f"({value} : BitVec {len(bits)})"
        slices = []
        for key, value in self.bound.items():
            if len(bits) < len(key):
                for offset in range(len(key) - len(bits) + 1):
                    if key[offset:offset + len(bits)] == bits:
                        slices.append((key, value, offset))
        if slices:
            require(len(slices) == 1, f"{self.name}: ambiguous sliced bus {bits}")
            _, value, offset = slices[0]
            if len(bits) == 1:
                return (f"((BitVec.truncate 1 (BitVec.ushiftRight ({value}) "
                        f"{offset})) != 0)")
            return (f"(BitVec.truncate {len(bits)} "
                    f"(BitVec.ushiftRight ({value}) {offset}))")
        if len(bits) == 1:
            return self._bool_cell(bits)
        driver = self.drivers.get(bits)
        if driver is None:
            return assemble(self, bits)
        return self._vec_cell(bits, driver)

    def _fresh(self, expr):
        wire = f"{self.name}{len(self.lines)}"
        self.lines.append(f"  let {wire} := {expr}")
        return wire

    def _vec_cell(self, bits, driver):
        kind, pins, params, where = driver
        self.used.add(where)
        require(bits not in self.resolving, f"{self.name}: combinational loop at {bits}")
        self.resolving.add(bits)
        width = len(bits)
        if kind == "$mux":
            require(len(pins["A"]) == len(pins["B"]) == width and len(pins["S"]) == 1,
                    f"{where}: inconsistent mux widths")
            expr = (f"(if {self._bit_bool(pins['S'][0])} then {self.expression(pins['B'])} "
                    f"else {self.expression(pins['A'])})")
        elif kind == "$pmux":
            expr = self._pmux(pins, params, width)
        elif kind in ("$and", "$or"):
            require(len(pins["A"]) == len(pins["B"]) == width,
                    f"{where}: expected an equal-width bitwise cell")
            operator = "&&&" if kind == "$and" else "|||"
            expr = "(" + f" {operator} ".join(
                self._vec_terms(bits, kind, width)) + ")"
        elif kind == "$xor":
            expr = f"({self.expression(pins['A'])} ^^^ {self.expression(pins['B'])})"
        elif kind == "$not":
            require(len(pins["A"]) == width, f"{where}: expected an equal-width complement")
            expr = f"(~~~{self.expression(pins['A'])})"
        elif kind in ("$add", "$sub"):
            require(len(pins["A"]) == len(pins["B"]) == width,
                    f"{where}: expected an equal-width arithmetic cell")
            operator = "+" if kind == "$add" else "-"
            expr = f"({self.expression(pins['A'])} {operator} {self.expression(pins['B'])})"
        else:
            raise UnsupportedRTL(f"{where}: unsupported multi-bit cell")
        wire = self._fresh(expr)
        self.bound[bits] = wire
        self.resolving.remove(bits)
        return wire

    def _pmux(self, pins, params, width):
        selects = int(params["S_WIDTH"], 2)
        expr = self.expression(pins["A"])
        for index in reversed(range(selects)):
            branch = self.expression(tuple(pins["B"][index * width:(index + 1) * width]))
            expr = f"(if {self._bit_bool(pins['S'][index])} then {branch} else {expr})"
        return expr

    def _vec_terms(self, bits, kind, width):
        """The flattened operands of a multi-bit `$and`/`$or` tree, in order."""
        driver = self.drivers.get(bits)
        if driver is not None:
            k, pins, params, where = driver
            if k == kind and len(pins["Y"]) == width:
                return (self._vec_terms(tuple(pins["A"]), kind, width) +
                        self._vec_terms(tuple(pins["B"]), kind, width))
        return [self.expression(bits)]

    def _bool_cell(self, bits):
        require(len(bits) == 1, f"{self.name}: expected a scalar result bus")
        driver = self.drivers.get(bits)
        require(driver is not None, f"{self.name}: undriven net bit {bits[0]}")
        kind, pins, params, where = driver
        self.used.add(where)
        require(bits not in self.resolving, f"{self.name}: combinational loop at {bits}")
        self.resolving.add(bits)
        a = pins.get("A")
        if kind == "$mux":
            require(len(pins["B"]) == 1 and len(pins["S"]) == 1,
                    f"{where}: inconsistent mux widths")
            expr = (f"(if {self._bit_bool(pins['S'][0])} then "
                    f"{self._bit_bool(pins['B'][0])} else {self._bit_bool(pins['A'][0])})")
        elif kind == "$pmux":
            expr = self._pmux_bool(pins, params)
        elif kind in ("$eq", "$ne"):
            if len(pins["A"]) == 1:
                operator = "==" if kind == "$eq" else "!="
                expr = (f"({self._bit_bool(pins['A'][0])} {operator} "
                        f"{self._bit_bool(pins['B'][0])})")
            else:
                require(len(pins["A"]) == len(pins["B"]),
                        f"{where}: expected an equal-width comparison")
                operator = "==" if kind == "$eq" else "!="
                expr = (f"({self.expression(pins['A'])} {operator} "
                        f"{self.expression(pins['B'])})")
        elif kind in ("$lt", "$le", "$gt", "$ge"):
            require(len(pins["A"]) > 1 and len(pins["A"]) == len(pins["B"]),
                    f"{where}: expected an equal-width comparison")
            operator = {"$lt": "<", "$le": "<=", "$gt": ">", "$ge": ">="}[kind]
            expr = (f"decide ({self.expression(pins['A'])} {operator} "
                    f"{self.expression(pins['B'])})")
        elif kind in ("$and", "$logic_and"):
            expr = "(" + " && ".join(self._bool_terms(bits, "$and")) + ")"
        elif kind in ("$or", "$logic_or"):
            expr = "(" + " || ".join(self._bool_terms(bits, "$or")) + ")"
        elif kind == "$not":
            expr = f"(!{self._bit_bool(pins['A'][0])})"
        elif kind == "$logic_not":
            width = int(params["A_WIDTH"], 2)
            expr = f"({self.expression(pins['A'])} == (0 : BitVec {width}))"
        elif kind in ("$reduce_or", "$reduce_bool"):
            expr = f"({self.expression(pins['A'])} != 0)"
        elif kind == "$shiftx":
            source_width = int(params["A_WIDTH"], 2)
            require(int(params["Y_WIDTH"], 2) == 1 or len(bits) == 1,
                    f"{where}: expected a scalar indexed shift")
            expr = (f"(((BitVec.ushiftRight ({self.expression(pins['A'])}) "
                    f"({self.expression(pins['B'])}).toNat) &&& "
                    f"(1 : BitVec {source_width})) != 0)")
        elif kind == "$xor":
            expr = f"({self._bit_bool(pins['A'][0])} != {self._bit_bool(pins['B'][0])})"
        else:
            raise UnsupportedRTL(f"{where}: unsupported one-bit cell")
        wire = self._fresh(expr)
        self.bound[bits] = wire
        self.resolving.remove(bits)
        return wire

    def _pmux_bool(self, pins, params):
        selects = int(params["S_WIDTH"], 2)
        expr = self._bit_bool(pins["A"][0])
        for index in reversed(range(selects)):
            branch = self._bit_bool(pins["B"][index])
            expr = f"(if {self._bit_bool(pins['S'][index])} then {branch} else {expr})"
        return expr

    def _bool_terms(self, bits, group):
        """The flattened operands of a one-bit `$and`/`$or` tree, in order."""
        kinds = ("$and", "$logic_and") if group == "$and" else ("$or", "$logic_or")
        driver = self.drivers.get(bits)
        if driver is not None:
            kind, pins, params, where = driver
            if kind in kinds and len(bits) == 1:
                return (self._bool_terms(tuple(pins["A"]), group) +
                        self._bool_terms(tuple(pins["B"]), group))
        return [self._bit_bool(bits[0])]

    def _bit_bool(self, bit):
        if bit == "0":
            return "false"
        if bit == "1":
            return "true"
        if bit == "x":
            raise UnsupportedRTL(f"{self.name}: unexpected x bit")
        for key, value in self.bound.items():
            if bit in key:
                if len(key) == 1:
                    return value
                return (f"((BitVec.truncate 1 (BitVec.ushiftRight ({value}) "
                        f"{key.index(bit)})) != 0)")
        if (bit,) in self.drivers:
            return self._bool_cell((bit,))
        found = None
        for key in self.drivers:
            if len(key) > 1 and bit in key:
                found = key
                break
        require(found is not None, f"{self.name}: undriven net bit {bit}")
        value = self.expression(found)
        return (f"((BitVec.truncate 1 (BitVec.ushiftRight ({value}) "
                f"{found.index(bit)})) != 0)")


def _field_of(cone, bit):
    """Where one bit of an assembled bus comes from."""
    if bit in ("0", "1", "x"):
        return ("const", "0" if bit == "x" else bit, 0)
    slot = cone.bound.get((bit,))
    if slot is not None:
        return ("bool", slot, 0)
    best = None
    for key in cone.bound:
        if len(key) > 1 and bit in key and (best is None or len(key) > len(best[0])):
            best = (key, key.index(bit))
    if best is not None:
        return ("bus", best[0], best[1])
    for key in cone.drivers:
        if len(key) > 1 and bit in key and (best is None or len(key) > len(best[0])):
            best = (key, key.index(bit))
    if best is not None:
        return ("bus", best[0], best[1])
    return ("bool", cone._bit_bool(bit), 0)


def _continues(previous, field):
    """Whether `field` extends the run `previous`."""
    if previous[0] != field[0]:
        return False
    if previous[0] == "const":
        return previous[1] == field[1]
    if previous[0] == "bool":
        return False
    return previous[1] == field[1] and previous[2] + 1 == field[2]


def assemble(cone, bits):
    """Assemble a bus that is a concatenation of fields.

    Yosys writes a Verilog concatenation as a bus of bits with no single
    driver.  Reading it back field by field (a run of one bound bus, a run of
    one cell output, a constant field, a single Boolean) keeps the shape of the
    specification's `++`, which is what the proof compares against.  A run of
    `k` bits of one bus becomes one `slice`, so `{1'b0, PH}` is
    `0 ++ slice 0 16 PH`.
    """
    fields = [_field_of(cone, bit) for bit in bits]
    runs = []            # (start, count, first field, last field)
    for index, field in enumerate(fields):
        if runs and _continues(runs[-1][3], field):
            start, count, first, _ = runs[-1]
            runs[-1] = (start, count + 1, first, field)
        else:
            runs.append((index, 1, field, field))
    pieces = []
    for start, count, first, _last in reversed(runs):
        kind = first[0]
        if kind == "const":
            value = 2 ** count - 1 if first[1] == "1" else 0
            pieces.append(f"({value} : BitVec {count})")
        elif kind == "bool":
            require(count == 1, f"{cone.name}: unexpected Boolean run of {count} bits")
            pieces.append(f"(if {first[1]} then (1 : BitVec 1) else 0)")
        else:
            _, key, offset = first
            value = cone.expression(key)
            pieces.append(f"(BitVec.truncate {count} (BitVec.ushiftRight ({value}) {offset}))")
    expr = pieces[0]
    for piece in pieces[1:]:
        expr = f"({expr} ++ {piece})"
    return expr


def exclusive_selects(module, selects, where):
    """Require every `$pmux` select to be a distinct test of one shared bus."""
    constants = []
    shared = None
    for bit in selects:
        owners = [cell for cell in module["cells"].values()
                  if cell["port_directions"].get("Y", "") in ("output", "inout")
                  and tuple(cell["connections"]["Y"]) == (bit,)]
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


def elaborate(snapshot, work, yosys):
    """Elaborate a source snapshot with the same recipe as `verify.py`."""
    import hostcmd_check
    return hostcmd_check.elaborate(snapshot, work, yosys)


def snapshot_of(directory):
    import hostcmd_check
    return hostcmd_check.snapshot_of(directory)


def load_modules(rtlil_or_json):
    import hostcmd_check
    return hostcmd_check.load_modules(rtlil_or_json)


def net_bits(module, name, width, where=None):
    """The ordered bits of a named net, requiring its width."""
    net = module["netnames"].get(name)
    require(net is not None, f"{where or LINE_MODULE}.{name}: missing net")
    require("init" not in net["attributes"],
            f"{where or LINE_MODULE}.{name}: unexpected initial value")
    bits = tuple(net["bits"])
    require(len(bits) == width, f"{where or LINE_MODULE}.{name}: expected {width} bits")
    return bits


def module_header(path=ROOT / "src" / "md2_map.vh"):
    """Read the line window and host-map constants of the generated header."""
    text = path.read_text(encoding="utf-8")

    def value(name):
        match = re.search(rf"localparam (?:\[[^\]]*\]|integer) {name} = "
                          rf"(?:(?:\d+)'h([0-9A-Fa-f]+)|(\d+));", text)
        require(match is not None, f"md2_map.vh: missing {name}")
        return int(match.group(1), 16) if match.group(1) else int(match.group(2))

    header = {name: value(name) for name in
              ("HAI_LINE_BASE", "CFG_LO_I", "HS_LINE", "HA_LRT_BASE", "HSPAN_LRT",
               "HO_LRT_PHASE", "HO_LRT_CTL", "HO_LRT_STAT")}
    header.update({name: value(name) for name in HEADER_OFFSETS.values()})
    return header


def check_header(header):
    """The specification's literals must be the generated header's."""
    require(header["HAI_LINE_BASE"] == 0x2000 and header["CFG_LO_I"] == 0x2000,
            "the line window is not the configuration window")
    require(header["HS_LINE"] == 32, f"line window stride changed: {header['HS_LINE']}")
    require(header["HA_LRT_BASE"] == 0x2410 and header["HSPAN_LRT"] == 0x20,
            "the runtime line block moved")
    require((header["HO_LRT_PHASE"], header["HO_LRT_CTL"], header["HO_LRT_STAT"]) ==
            (0, 2, 5), "the LRT runtime register offsets moved")
    for field, net, width, offset in LINE_FIELDS:
        require(header[HEADER_OFFSETS[field]] == offset,
                f"md2_map.vh: {HEADER_OFFSETS[field]} is "
                f"{header[HEADER_OFFSETS[field]]}, expected {offset}")
    return header


def line_module(modules, header):
    """The specialized `md2_line` module the four instances share."""
    top = modules[TOP]
    names = [f"g_ln[{k}].u" for k in range(4)]
    for name in names:
        require(name in top["cells"], f"{TOP}.{name}: missing line instance")
    types = {top["cells"][name]["type"] for name in names}
    require(len(types) == 1, "the four line instances are not one specialized module")
    kind = types.pop()
    require(kind in modules, f"{kind}: missing specialized module")
    module = modules[kind]
    require(module["attributes"].get("hdlname") == LINE_MODULE,
            f"{kind}: unexpected line module")
    require(len(module["ports"]["cfg"]["bits"]) == 8 * header["HS_LINE"],
            "line window width is not 8 * HS_LINE")
    return module, kind


def drivers_of(top):
    drivers = {}
    for name, port in top["ports"].items():
        if port["direction"] in ("input", "inout"):
            for bit in port["bits"]:
                drivers[bit] = ("<port>", name)
    for name, cell in top["cells"].items():
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] in ("output", "inout"):
                for bit in bits:
                    drivers[bit] = (name, pin)
    return drivers


def _and_leaves(top, drivers, bit, leaves, tests, seen, stops):
    """Expand scalar AND gates; collect `$eq` leaves and other leaves."""
    require(bit not in seen, "host enable cone has a combinational loop")
    seen.add(bit)
    if bit in stops:
        leaves.append(bit)
        return
    owner = drivers.get(bit)
    require(owner is not None, f"host enable bit {bit} has no driver")
    name, pin = owner
    cell = top["cells"].get(name)
    if cell is None:
        leaves.append(bit)
        return
    if (cell["type"] in ("$and", "$logic_and") and pin == "Y" and
            len(cell["connections"]["Y"]) == 1):
        _and_leaves(top, drivers, cell["connections"]["A"][0], leaves, tests, seen, stops)
        _and_leaves(top, drivers, cell["connections"]["B"][0], leaves, tests, seen, stops)
        return
    if cell["type"] == "$eq" and pin == "Y" and len(cell["connections"]["Y"]) == 1:
        tests.append((tuple(cell["connections"]["A"]),
                      constant_value(tuple(cell["connections"]["B"]), "host enable")))
        return
    if cell["type"] == "$logic_not" and pin == "Y" and len(cell["connections"]["Y"]) == 1:
        tests.append((tuple(cell["connections"]["A"]), 0))
        return
    leaves.append(bit)


def check_enable(top, drivers, bit, index, offset, what):
    """Require one write enable to be `w_lrt & i_lrt == index & o_lrt == offset`."""
    w_lrt = net_bits(top, "w_lrt", 1, TOP)
    i_lrt = net_bits(top, "i_lrt", 16, TOP)
    o_lrt = net_bits(top, "o_lrt", 32, TOP)
    leaves, tests, seen = [], [], set()
    _and_leaves(top, drivers, bit, leaves, tests, seen, set(w_lrt))
    require(sorted(leaves) == list(w_lrt),
            f"{what}: enable cone is not ANDed with w_lrt (leaves {leaves})")
    require(len(tests) == 2, f"{what}: expected two comparisons, got {tests}")
    by_bus = {}
    for bus, value in tests:
        by_bus.setdefault(bus, []).append(value)
    require(list(by_bus.get(i_lrt, [])) == [index],
            f"{what}: i_lrt comparison is not == {index}")
    require(list(by_bus.get(o_lrt, [])) == [offset],
            f"{what}: o_lrt comparison is not == {offset}")
    require(len(by_bus) == 2, f"{what}: unexpected comparison operands")


def check_line_top(modules, header):
    """Check the four instances' wiring, window slices and host enables."""
    top = modules[TOP]
    cfg_bits = tuple(top["netnames"]["cfg"]["bits"])
    drivers = drivers_of(top)
    offsets = {"h_ph_we": (header["HO_LRT_PHASE"], header["HO_LRT_PHASE"] + 1),
               "h_ctl_we": (header["HO_LRT_CTL"],),
               "h_stat_we": (header["HO_LRT_STAT"],)}
    for k in range(4):
        cell_name = f"g_ln[{k}].u"
        cell = top["cells"][cell_name]
        pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
        require(pins["clk"] == tuple(top["ports"]["clk"]["bits"]),
                f"{cell_name}: unexpected clock")
        require(pins["rst_n"] == net_bits(top, "rst_q", 1, TOP),
                f"{cell_name}: reset is not rst_q")
        require(pins["frz"] == net_bits(top, "frz", 1, TOP),
                f"{cell_name}: freeze is not the frz net")
        for port, net in (("lvl", "lvl"), ("rise", "rise"), ("fall", "fall")):
            require(pins[port] == net_bits(top, net, 16, TOP),
                    f"{cell_name}.{port}: unexpected pin vector")
        lb = header["HAI_LINE_BASE"] - header["CFG_LO_I"] + header["HS_LINE"] * k
        window = cfg_bits[8 * lb:8 * lb + 8 * header["HS_LINE"]]
        require(pins["cfg"] == window,
                f"{cell_name}.cfg: not window bytes {lb}..{lb + header['HS_LINE'] - 1}")
        for port, net, width, stride in TOP_OUTPUTS:
            expect = net_bits(top, net, width * 4, TOP)[stride * k:stride * k + width]
            require(pins[port] == expect,
                    f"{cell_name}.{port}: not {net}[{stride * k} +: {width}]")
        for port, offsets_k in offsets.items():
            for bit_index, offset in enumerate(offsets_k):
                check_enable(top, drivers, pins[port][bit_index], k, offset,
                             f"{cell_name}.{port}[{bit_index}]")


def line_cone(module, header):
    """A `LineCone` with the module inputs, config fields and registers bound.

    Returns the cone, the checked window slices and the register D buses.
    """
    cfg_bits = tuple(module["ports"]["cfg"]["bits"])
    require(len(cfg_bits) == 8 * header["HS_LINE"], "md2_line.cfg: unexpected width")
    cone = LineCone("rtl", module)
    for name, width, value in (
        ("rst_n", 1, "input.resetN"), ("frz", 1, "input.frz"),
        ("lvl", 16, "input.lvl"), ("rise", 16, "input.rise"),
        ("fall", 16, "input.fall"), ("ctl_we", 1, "input.ctlWe"),
        ("ctl_d", 3, "input.ctlD"), ("sym_we", 1, "input.symWe"),
        ("sym_op", 2, "input.symOp"), ("sym_d", 4, "input.symD"),
        ("h_ph_we", 2, "input.phWe"), ("h_ctl_we", 1, "input.hCtlWe"),
        ("h_stat_we", 1, "input.hStatWe"), ("h_d", 8, "input.hD"),
    ):
        cone.input(name, width, value)
    slices = []
    for field, net, width, offset in LINE_FIELDS:
        bits = net_bits(module, net, width)
        expect = cfg_bits[8 * offset:8 * offset + width]
        require(bits == expect,
                f"md2_line.{net}: not window bytes {offset}+ (field {field})")
        cone.leaf(net, width, f"input.cfg.{field}")
        slices.append((field, net, offset, width))
    data = {}
    for field, net, width in STATE_REGISTERS:
        data[field] = cone.register(net, width, f"state.{field}")
    require(not cone.registers,
            f"md2_line: unmodelled register state {sorted(cone.registers)}")
    return cone, slices, data


def extract_line(modules, header, module):
    """Extract the layered transition and outputs from the elaborated module.

    Each layer gets its own cone with every earlier layer bound to its
    specification expression, so a layer proof is a shallow equation.  The
    final transition binds all layers, so its register equations are
    definitional.
    """
    layers = []
    for index, (name, net, width, spec) in enumerate(LAYERS):
        cone, _, _ = line_cone(module, header)
        for prior, pnet, pwidth, pspec in LAYERS[:index]:
            cone.leaf(pnet, pwidth, pspec)
        expr = cone.expression(net_bits(module, net, width))
        lets = "\n".join(cone.lines)
        body = lets + "\n" + expr
        used = [(pspec, pwidth == 1) for _, _, pwidth, pspec in LAYERS[:index]
                if re.search(r"\b" + re.escape(pspec) + r"\b", body)]
        layers.append(_render_layer(name, width, spec, lets, expr, used))
    finals = []
    for name, port, width, spec in FINAL_OUTPUTS:
        cone, _, _ = line_cone(module, header)
        for prior, pnet, pwidth, pspec in LAYERS:
            cone.leaf(pnet, pwidth, pspec)
        bits = tuple(module["ports"][port]["bits"])
        require(len(bits) == width, f"md2_line.{port}: expected {width} bits")
        expr = cone.expression(bits)
        lets = "\n".join(cone.lines)
        body = lets + "\n" + expr
        used = [(pspec, pwidth == 1) for _, _, pwidth, pspec in LAYERS
                if re.search(r"\b" + re.escape(pspec) + r"\b", body)]
        finals.append(_render_layer(name, width, spec, lets, expr, used))
    cone, slices, data = line_cone(module, header)
    for name, net, width, spec in LAYERS:
        cone.leaf(net, width, spec)
    fields = {field: cone.expression(bits) for field, bits in data.items()}
    return {"layers": layers, "finals": finals, "lets": "\n".join(cone.lines),
            "fields": fields, "slices": slices, "registers": len(fields)}


def _used(body, name):
    return re.search(rf"\b{name}\b", body) is not None


# Register fields in state order: (field, theorem name).
REGISTER_FIELDS = (
    ("ph", "rtlPh"), ("run", "rtlRun"), ("arm", "rtlArm"), ("ren", "rtlRen"),
    ("held", "rtlHeld"), ("first", "rtlFirst"), ("sc", "rtlSc"), ("sp", "rtlSp"),
    ("fired", "rtlFired"), ("w", "rtlW"), ("sn", "rtlSn"), ("rem", "rtlRem"),
    ("staged", "rtlStaged"), ("committed", "rtlCommitted"),
    ("tapmiss", "rtlTapmiss"),
)


def _layer_proof(unfolded, used, body):
    """The tactic script for one equation.

    The cone emits the RTL's `$and`/`$or` trees flattened in source operand
    order, which is the order the specification's chains are written in, so the
    two sides are the same term and `rfl` closes them.
    """
    return f"  simp only [{unfolded}] <;> rfl"


def _render_layer(name, width, spec, lets, expr, prior):
    """One emitted definition and its parametric-equation theorem."""
    body = lets + "\n" + expr
    claim = body + "\n" + spec
    def_state, def_input = _used(body, "state"), _used(body, "input")
    use_state, use_input = _used(claim, "state"), _used(claim, "input")

    def signature(use_s, use_i):
        params, args = [], []
        if use_s:
            params.append("(state : State)")
            args.append("state")
        if use_i:
            params.append("(input : Input)")
            args.append("input")
        return " ".join(params), " ".join(args)

    def_params, def_args = signature(def_state, def_input)
    thm_params, _ = signature(use_state, use_input)
    typ = "Bool" if width == 1 else f"BitVec {width}"
    unfolded = ", ".join([name, spec.split()[0]] + AUX_DEFS)
    script = _layer_proof(unfolded, prior, body)
    return {"name": name, "width": width, "spec": spec, "type": typ,
            "params": thm_params, "args": def_args,
            "def": f"def {name} {def_params} : {typ} :=\n{lets}\n  {expr}\n",
            "theorem": (f"theorem {name}_eq {thm_params} : "
                        f"{name} {(def_args + ' ') if def_args else ''}= {spec} := by\n"
                        + script + "\n")}


def lean_line(info, fingerprint):
    """Emit the extracted definitions and their layer theorems."""
    fields = info["fields"]
    parts = [f"""import Metronome.Line

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {fingerprint}
-- Line: the `{LINE_MODULE}` module of the four `g_ln` instances.  `cfg` is the
-- line's window; the adapter checked that every `c_*` field net is the window
-- byte slice of the specification before emitting this file.
--
-- The transition is emitted in layers (see `LAYERS` in `line_check.py`): each
-- intermediate net is a definition whose cone binds the earlier layers to their
-- specification expressions, and `rtlStep` binds all of them, so the register
-- equations are definitional.

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Metronome.Line

"""]
    for layer in info["layers"]:
        parts.append(f"/-- The elaborated `{layer['name'][3:].lower()}` cone. -/\n"
                     + layer["def"] + "\n")
    for layer in info["finals"]:
        parts.append(f"/-- The elaborated `{layer['name'][3:].lower()}` output cone. -/\n"
                     + layer["def"] + "\n")
    parts.append(f"""/-- The elaborated line transition.  `state` holds the fifteen registers of
`md2_line.v`; `input` holds the sampled pins, moves, host writes and freeze. -/
def rtlStep (state : State) (input : Input) : State :=
{info['lets']}
  {{ ph := {fields['ph']}, run := {fields['run']}, arm := {fields['arm']},
    ren := {fields['ren']}, held := {fields['held']}, first := {fields['first']},
    sc := {fields['sc']}, sp := {fields['sp']}, fired := {fields['fired']},
    w := {fields['w']}, sn := {fields['sn']}, rem := {fields['rem']},
    staged := {fields['staged']}, committed := {fields['committed']},
    tapmiss := {fields['tapmiss']} }}

/-! ## Layer equations

Each intermediate net of `src/md2_line.v` is its specification sub-function.
`line_check.py` emits one theorem per layer, in dependency order. -/

""")
    for layer in info["layers"]:
        parts.append(layer["theorem"] + "\n")
    for layer in info["finals"]:
        parts.append(layer["theorem"] + "\n")
    parts.append("""
/-! ## The extracted transition is the specification

The transition binds every intermediate net to its specification sub-function,
so each register equation is the same formula on both sides. -/

""")
    for field, tname in REGISTER_FIELDS:
        expr = fields[field]
        body = info["lets"] + "\n" + expr
        used = [(pspec, pwidth == 1) for _, _, pwidth, pspec in LAYERS]
        unfolded = ", ".join(["rtlStep", "step"] + AUX_DEFS)
        script = _layer_proof(unfolded, used, body)
        parts.append(f"/-- The extracted `{field.upper()}` next state is the "
                     f"specification's. -/\n"
                     f"theorem {tname} (state : State) (input : Input) :\n"
                     f"    (rtlStep state input).{field} = (step state input).{field} := by\n"
                     + script + "\n")
    parts.append("""
/-- The elaborated line transition matches the independent SPEC_V2 §3
specification for every state and input: all fifteen register values and the
combinational outputs (their layer equations above). -/
theorem rtlStep_eq_step (state : State) (input : Input) :
    rtlStep state input = step state input := by
  simp only [rtlStep, step] <;> rfl
""")
    return "".join(parts)


def audit_block(info):
    """The `#print axioms` list for every emitted theorem."""
    names = [f"{layer['name']}_eq" for layer in info["layers"] + info["finals"]]
    names += ["rtlStep_eq_step", "rtlStateAt_eq", "rtl_trace_reset",
              "rtl_trace_frz_holds"]
    names += [f"rtl{t.capitalize()}" for t in
              ("ph", "run", "arm", "ren", "held", "first", "sc", "sp", "fired",
               "w", "sn", "rem", "staged", "committed", "tapmiss")]
    preferred = ["rtlStep_eq_step", "rtlStateAt_eq", "rtl_trace_frz_holds"]
    ordered = preferred + [name for name in names if name not in preferred]
    return "\n/-! ## Axiom audit\n\n`line_check.py` records these records and rejects `sorryAx`. -/\n\n" + \
        "".join(f"#print axioms {name}\n" for name in ordered)


def lean_run(source, filename, artifact, lake, work, evidence, timeout=900):
    path = work / filename
    path.write_text(source, encoding="utf-8")
    if evidence is not None:
        (evidence / artifact).write_text(source, encoding="utf-8")
    return run([lake, "env", "lean", "-j1", "-DwarningAsError=true", str(path)],
               HERE, timeout=timeout)


def axiom_audit(text):
    return {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
            for name, axioms in AXIOM_LINE.findall(text)}


def check_line(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the elaborated line cut and its generated Lean proofs."""
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-line-{case}-") as tmp:
        work = Path(tmp)
        is_json = isinstance(rtlil_or_json, dict) or (
            isinstance(rtlil_or_json, (str, Path)) and Path(rtlil_or_json).suffix == ".json")
        if is_json:
            modules = load_modules(rtlil_or_json)
            fingerprint = "not recorded: parsed design JSON"
        else:
            snapshot = snapshot_of(rtlil_or_json)
            modules, fingerprint, commands, yosys_log = elaborate(
                snapshot, work / "rtl", yosys)
            log.append(f"RTL snapshot SHA-256: {fingerprint}\n")
            log.append(f"Yosys command: {commands}\n")
            log.append(yosys_log)

        build = run([lake, "build", "Metronome.Line"], HERE)
        log.append(build.stdout)
        if build.returncode != 0:
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise LineRejected(f"{case}: lake build Metronome.Line failed\n" + "".join(log))
        try:
            header = check_header(module_header())
            check_line_top(modules, header)
            module, kind = line_module(modules, header)
            info = extract_line(modules, header, module)
            log.append(f"Line cut: {info['registers']} registers, "
                       f"{len(info['slices'])} checked window fields, module {kind}\n")
            log.append("Window fields:\n")
            for field, net, offset, width in info["slices"]:
                log.append(f"  {field}: {net} = window bytes {offset}.."
                           f"{offset + (width + 7) // 8 - 1}\n")
            source = lean_line(info, fingerprint)
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the structural line check: {exc}\n")
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise
        source += TEMPLATE.read_text(encoding="utf-8")
        source += audit_block(info)
        result = lean_run(source, "LineProof.lean", f"{case}.line.lean",
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
            "registers": info["registers"],
            "fields": len(info["slices"]),
            "fingerprint": fingerprint,
            "source": out_dir / f"{case}.line.lean",
            "log": out_dir / f"{case}.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            first = next((line.strip() for line in result.stdout.splitlines()
                          if "error:" in line), outcome)
            first = first.split("LineProof.lean:", 1)[-1]
            raise LineRejected(f"{case}: {outcome}\n" + "".join(log),
                               reason=f"{outcome}: {first[:200]}",
                               code=result.returncode)
    return report


def line_mutations():
    """The planted line regressions, as snapshot transformers."""
    def replace(before, after, filename="md2_line.v", count=1):
        def apply(snapshot):
            require(filename in snapshot, f"mutation: missing {filename}")
            data = snapshot[filename]
            require(data.count(before.encode()) == count,
                    f"mutation: anchor changed in {filename}: {before}")
            return {**snapshot, filename: data.replace(before.encode(), after.encode(), count)}
        return apply

    return [
        # The freeze no longer holds HELD (SPEC 12.3).
        ("line_frz_held", replace(
            "            if (!frz) held <= hold;", "            held <= hold;")),
        # A move to Lk.CTL beats the host CTL write (wrong precedence).
        ("line_host_ctl_loses", replace(
            "wire        run_f = h_ctl_we ? h_d[0] : run_c;",
            "wire        run_f = run_c;")),
        # TAPMISS is no longer sticky: a miss sets it for one cycle only.
        ("line_tapmiss_not_sticky", replace(
            "tapmiss <= miss_ev | (tapmiss & ~(h_stat_we & h_d[0]));",
            "tapmiss <= miss_ev;")),
        # The commit takes the previous STAGED instead of this cycle's write.
        ("line_commit_staged", replace(
            "if (beat | starting) committed <= staged_n;",
            "if (beat | starting) committed <= staged;")),
        # Tap 0's phase crossing compares against T1 instead of T0.
        ("line_tap0_cross", replace(
            "wire ph_cross = adv & tlt[0] & crossing(c_t0, ph, nx, over);",
            "wire ph_cross = adv & tlt[0] & crossing(c_t1, ph, nx, over);")),
        # The line reads its T1 field from the T2 window bytes.
        ("line_cfg_offset", replace(
            "wire [15:0] c_t1  = cfg[8*HO_LINE_T1  +: 16];",
            "wire [15:0] c_t1  = cfg[8*HO_LINE_T2  +: 16];")),
        # Line 2's window slice is one byte high.
        ("line2_cfg_slice", replace(
            "localparam integer LB = HAI_LINE_BASE - CFG_LO_I + HS_LINE * k;",
            "localparam integer LB = HAI_LINE_BASE - CFG_LO_I + HS_LINE * k + (k == 2);",
            filename="project.v")),
    ]


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted line regression is rejected."""
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-line-mutants-") as tmp:
        for case, transform in line_mutations():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_line(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"structural check: {exc}", 0))
                continue
            except LineRejected as exc:
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
                        help="also check the planted line regressions")
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
            raise LineRejected("tool version query failed")

        build = run([lake, "build", "Metronome.Line"], HERE)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise LineRejected("lake build Metronome.Line failed")

        snapshot = snapshot_of(ROOT / "src")
        report = check_line(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        emit(f"baseline: {report['outcome']} ({report['registers']} registers, "
             f"{report['fields']} checked window fields)")
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
        raise SystemExit(f"Line check failed: {exc}") from exc
