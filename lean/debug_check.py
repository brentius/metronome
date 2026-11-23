"""Check the chip-top debug, pin-replay, program-memory and reset logic in Lean.

This cut closes the logic of `src/project.v` that the other Lean cuts leave
outside their boundaries:

* (a) the pin level and edge vectors `pins_level`, `pins_prev`, `lvl`, `rise`,
  `fall` under the v4 replay mask (SPEC_V2 §2, §13.2);
* (b) the v3/v4 debug registers of the control block: the execution digest
  (`MCTL`/`MISR`, SPEC_V2 §12.2) and the edge-capture/replay registers
  (`ECTL`, `EMASK`, `RLV`, `DC`, `cev`, SPEC_V2 §12.4, §13.1, §13.2);
* (c) the host/fetch port muxing of the two program memories (SPEC_V2 §5, §9,
  9a.8), with the SRAM macro as a black box whose read is registered;
* (d) the reset synchroniser `rst_m`/`rst_q` (SPEC_V2 §1).

The check re-elaborates the current `src/` with `verify.py`'s Yosys recipe (plus
`-D USE_IHP_SRAM`, like `mem_check.py`, so the program-memory macro instance is
visible), extracts the cones fail-closed, emits Lean and proves each extracted
definition equal to `Metronome.Debug`, which is written from the specification
text.  Three trace lifts then carry the statements to every cycle.

Run it from the repository root:

    python lean/debug_check.py
    python lean/debug_check.py --mutations

`run_mutations` plants eight regressions on temporary copies of `src/` (never
the repository): a wrong MISR polynomial, a digest that advances while frozen, a
replay mask that ignores `EMASK`, a core write that beats a host write to
`ECTL`, an `ECTL` write that does not clear `DC`, pins 13..15 that read the
synchroniser bits, a program byte lane off by one, and a one-stage reset
synchroniser.  Every one must be rejected.
"""

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from rtlil import DffCone, UnsupportedRTL, require
from verify import HERE, ROOT, TOP, run

DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_debug_v4_20261121"
TEMPLATE = HERE / "DebugEquivalence.lean.in"
AXIOM_LINE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)
ERROR_LINE = re.compile(r"DebugProof\.lean:(\d+):\d+: error:")
DECL_LINE = re.compile(r"^(?:private |protected )?(?:theorem|def|lemma) ([A-Za-z0-9_.']+)")

PINS_LEAVES = (("s2", 16, "s2"), ("sp", 16, "sp"), ("rlv", 13, "rlv"),
               ("rlv_prev", 13, "rlvPrev"), ("emask", 13, "emask"),
               ("replay", 1, "replay"))
PINS2_LEAVES = (("pins_level", 13, "pl"), ("pins_prev", 13, "pp"))
DIGEST_LEAVES = (("rst_q", 1, "i.resetN"), ("d_wr_mctl", 1, "i.dWrMctl"),
                 ("h_wd", 8, "i.hWd"), ("frz", 1, "i.frz"),
                 ("o_oe", 8, "i.oEe"), ("o_out", 14, "i.oOut"))
CTRL1_LEAVES = (("dc", 19, "dc"), ("replay", 1, "replay"), ("cen", 1, "cen"),
                ("emask", 13, "emask"), ("rlv", 13, "rlv"), ("frz", 1, "frz"),
                ("s_replay_valid", 2, "rv"), ("s_replay_word", 64, "rw"))
CTRL_REG_LEAVES = (("rst_q", 1, "i.resetN"), ("d_wr_ectl", 1, "i.dWrEctl"),
                   ("h_ectl", 1, "i.hEctl"), ("d_wr_em0", 1, "i.dWrEm0"),
                   ("h_em0", 1, "i.hEm0"), ("d_wr_em1", 1, "i.dWrEm1"),
                   ("h_em1", 1, "i.hEm1"), ("d_wr_rlv0", 1, "i.dWrRlv0"),
                   ("h_rlv0", 1, "i.hRlv0"), ("d_wr_rlv1", 1, "i.dWrRlv1"),
                   ("h_rlv1", 1, "i.hRlv1"), ("h_wd", 8, "i.hWd"),
                   ("cw_pending_data", 8, "i.cwData"), ("frz", 1, "i.frz"))
PMEM_LEAVES = (("h_wr", 1, "hWr"), ("in_prg", 1, "inPrg"),
               ("a_prg", 16, "a"), ("fadr", 16, "fadr"))
PMEM_ADDR_LEAVES = (("pm_we0", 1, "we0"), ("pm_we1", 1, "we1"),
                    ("a_prg", 16, "a"), ("fadr", 16, "fadr"))
RESET_LEAVES = (("rst_m", 1, "s.rstM"),)

LET_LINE = re.compile(r"^  let ([A-Za-z0-9_']+) := (.*)$")


def _trim(cone, expr):
    """A definition body: the `let` chain the expression needs, then the expression."""
    bodies = {}
    for line in cone.lines:
        match = LET_LINE.match(line)
        if match:
            bodies[match.group(1)] = match.group(2)
    used = set()
    stack = [expr]
    while stack:
        text = stack.pop()
        for name, body in bodies.items():
            if name not in used and re.search(r"\b" + re.escape(name) + r"\b", text):
                used.add(name)
                stack.append(body)
    kept = [line for line in cone.lines
            if (match := LET_LINE.match(line)) and match.group(1) in used]
    return "\n".join(kept + ["  " + expr])


def _def(name, params, expr, cone):
    """One generated definition with its own trimmed `let` chain."""
    return (name, params, _trim(cone, expr))


class DebugRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated cut."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


def elaborate(snapshot, work, yosys):
    """Elaborate a source snapshot with `verify.py`'s recipe and the SRAM macro."""
    work = Path(work)
    src = work / "src"
    src.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256()
    for name, content in sorted(snapshot.items()):
        (src / name).write_bytes(content)
        digest.update(name.encode() + b"\0" + hashlib.sha256(content).digest())
    files = " ".join(f"src/{path.name}" for path in sorted(src.glob("*.v")))
    commands = (f"read_verilog -I src -D USE_IHP_SRAM {files}; "
                f"hierarchy -check -top {TOP}; proc; opt_clean; write_json design.json")
    result = run([yosys, "-Q", "-q", "-p", commands], work)
    if result.returncode != 0:
        raise DebugRejected(f"Yosys elaboration failed: {result.stdout.strip()}")
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


def net_bits(module, name, width):
    """The ordered bits of a named net, requiring its width and no init value."""
    net = module["netnames"].get(name)
    require(net is not None, f"{TOP}.{name}: missing net")
    require("init" not in net["attributes"], f"{TOP}.{name}: unexpected initial value")
    bits = tuple(net["bits"])
    require(len(bits) == width, f"{TOP}.{name}: expected {width} bits, got {len(bits)}")
    return bits


class DbgCone(DffCone):
    """A `DffCone` with the cell shapes this cut's cones need.

    Added locally (the shared `rtlil.py` is unchanged): `$logic_not`,
    `$reduce_or`/`$reduce_bool`, `$xor`, `$gt`/`$le`, `$shl`, and multi-bit
    `$and`/`$or`/`$not`.  A one-bit bus is a Lean `Bool` and a wider bus a
    `BitVec`, as elsewhere in the suite.  Every shape stays fail-closed: an
    unexpected width, an unsupported cell, an unbound or multiply driven net
    raises `UnsupportedRTL`.
    """

    EXTRA = ("$logic_not", "$reduce_or", "$reduce_bool", "$xor", "$gt", "$le", "$shl")

    def __init__(self, name, module):
        super().__init__(name, module)
        for cell_name, cell in module["cells"].items():
            kind = cell["type"]
            if kind not in self.EXTRA:
                continue
            pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
            params = cell["parameters"]
            where = f"{name}.{cell_name} ({kind})"
            if kind == "$logic_not":
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
            elif kind == "$shl":
                require(len(pins["Y"]) == int(params["Y_WIDTH"], 2) and
                        len(pins["A"]) == int(params["A_WIDTH"], 2) and
                        len(pins["B"]) == int(params["B_WIDTH"], 2),
                        f"{where}: unexpected shift widths")
            else:
                require(len(pins["Y"]) == 1 and len(pins["A"]) == len(pins["B"]) and
                        int(params["A_WIDTH"], 2) == len(pins["A"]) and
                        int(params["B_WIDTH"], 2) == len(pins["B"]) and
                        len(pins["A"]) > 1,
                        f"{where}: expected a scalar equal-width comparison")
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = (kind, pins, params, where)

    def leaf_bits(self, bits, value):
        """Bind an unnamed bit bus (such as a net's low slice) as a leaf."""
        bits = tuple(bits)
        require(bits and all(isinstance(bit, int) for bit in bits),
                f"{self.name}: invalid leaf bus {bits}")
        require(bits not in self.bound, f"{self.name}: already bound")
        if bits in self.drivers:
            del self.drivers[bits]
        for output in tuple(self.drivers) + tuple(self.registers) + tuple(self.bound):
            require(not (set(output) & set(bits)),
                    f"{self.name}: {bits} overlaps the bound bus {output}")
        require(set(bits) <= self.claimed or set(bits).isdisjoint(self.claimed),
                f"{self.name}: partially claimed net {bits}")
        self.claimed.difference_update(bits)
        self.bound[bits] = value
        return bits

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
            return self._assemble(bits)
        return self._vec_cell(bits, driver)

    def _fresh(self, expr):
        wire = f"{self.name}{len(self.lines)}"
        self.lines.append(f"  let {wire} := {expr}")
        return wire

    def _vec_cell(self, bits, driver):
        kind, pins, params, where = driver
        require(bits not in self.resolving, f"{self.name}: combinational loop at {bits}")
        self.resolving.add(bits)
        width = len(bits)
        if kind == "$mux":
            require(len(pins["A"]) == len(pins["B"]) == width and len(pins["S"]) == 1,
                    f"{where}: inconsistent mux widths")
            expr = (f"(if {self._bit_bool(pins['S'][0])} then {self.expression(pins['B'])} "
                    f"else {self.expression(pins['A'])})")
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
        elif kind == "$shl":
            require(len(pins["A"]) == width and len(pins["B"]) == 3,
                    f"{where}: expected an 8-bit shift by three bits")
            expr = f"(BitVec.shiftLeft {self.expression(pins['A'])} ({self.expression(pins['B'])}).toNat)"
        else:
            raise UnsupportedRTL(f"{where}: unsupported multi-bit cell")
        wire = self._fresh(expr)
        self.bound[bits] = wire
        self.resolving.remove(bits)
        return wire

    def _vec_terms(self, bits, kind, width):
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
        require(bits not in self.resolving, f"{self.name}: combinational loop at {bits}")
        self.resolving.add(bits)
        a = pins.get("A")
        if kind == "$mux":
            require(len(pins["B"]) == 1 and len(pins["S"]) == 1,
                    f"{where}: inconsistent mux widths")
            expr = (f"(if {self._bit_bool(pins['S'][0])} then "
                    f"{self._bit_bool(pins['B'][0])} else {self._bit_bool(pins['A'][0])})")
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

    def _bool_terms(self, bits, group):
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
        return (f"((BitVec.truncate 1 (BitVec.ushiftRight "
                f"({self.expression(found)}) {found.index(bit)})) != 0)")

    def _assemble(self, bits):
        """Assemble a bus from exact runs of bound buses and constants."""
        width = len(bits)
        pieces = []
        index = 0
        while index < width:
            bit = bits[index]
            if bit == "0":
                index += 1
                continue
            if bit == "1":
                pieces.append(f"(BitVec.shiftLeft (1 : BitVec {width}) {index})")
                index += 1
                continue
            match = None
            for key, value in self.bound.items():
                if len(key) > 1 and index + len(key) <= width and \
                        bits[index:index + len(key)] == key:
                    match = (len(key), value)
                    break
            if match is not None:
                size, value = match
                pieces.append(f"(BitVec.shiftLeft ((BitVec.setWidth {width}) ({value})) {index})")
                index += size
                continue
            value = self._bit_bool(bit)
            pieces.append(
                f"(if {value} then (BitVec.shiftLeft (1 : BitVec {width}) {index}) "
                f"else (0 : BitVec {width}))")
            index += 1
        require(pieces, f"{self.name}: empty assembly")
        return "(" + " ||| ".join(pieces) + ")"


def _bind(cone, leaves):
    """Bind the named nets as free per-cycle leaves."""
    for name, width, value in leaves:
        cone.leaf(name, width, value)
    return dict((value, name) for name, _, value in leaves)


def extract_pins(modules):
    """(a) The pin level, previous level, `lvl`, `rise` and `fall` cones."""
    top = modules[TOP]
    first = DbgCone("pins", top)
    _bind(first, PINS_LEAVES)
    level = first.expression(net_bits(top, "pins_level", 13))
    previous = first.expression(net_bits(top, "pins_prev", 13))
    for value in ("s2", "rlv", "emask", "replay"):
        require(value in level or any(value in line for line in first.lines),
                f"pins_level: the bound leaf `{value}` is not used")
    for value in ("sp", "rlvPrev", "emask", "replay"):
        require(value in previous or any(value in line for line in first.lines),
                f"pins_prev: the bound leaf `{value}` is not used")

    second = DbgCone("pins2", top)
    _bind(second, PINS2_LEAVES)

    def low13(net):
        """The low 13 bits of a 16-bit pin vector; the high bits must be tied 0."""
        bits = net_bits(top, net, 16)
        require(bits[13:] == ("0", "0", "0"),
                f"{TOP}.{net}: bits 13..15 are not tied to 0 (SPEC_V2 §2)")
        return bits[:13]

    lvl = "(0 : BitVec 3) ++ " + second.expression(low13("lvl"))
    rise = "(0 : BitVec 3) ++ " + second.expression(low13("rise"))
    fall = "(0 : BitVec 3) ++ " + second.expression(low13("fall"))
    require("pl" in lvl, "lvl: the pin level leaf is not used (pins 13..15 unpinned?)")
    for value in ("pl", "pp"):
        require(value in rise or any(value in line for line in second.lines),
                f"rise: the bound leaf `{value}` is not used")
        require(value in fall or any(value in line for line in second.lines),
                f"fall: the bound leaf `{value}` is not used")
    return {
        "defs": [
            _def("rtlPinsLevel", "(s2 : BitVec 16) (rlv emask : BitVec 13) (replay : Bool) : BitVec 13", level, first),
            _def("rtlPinsPrev", "(sp : BitVec 16) (rlvPrev emask : BitVec 13) (replay : Bool) : BitVec 13", previous, first),
            _def("rtlLvl", "(pl : BitVec 13) : BitVec 16", lvl, second),
            _def("rtlRise", "(pl pp : BitVec 13) : BitVec 16", rise, second),
            _def("rtlFall", "(pl pp : BitVec 13) : BitVec 16", fall, second),
        ],
        "count": 5,
    }


def extract_digest(modules):
    """(b1) The `MEN` and `MISR` next-state cones (SPEC_V2 §12.2)."""
    top = modules[TOP]
    cone = DbgCone("digest", top)
    _bind(cone, DIGEST_LEAVES)
    men = cone.register("men", 1, "s.men")
    misr = cone.register("misr", 32, "s.misr")
    men_expr = cone.expression(men)
    misr_expr = cone.expression(misr)
    for value in ("i.dWrMctl", "i.hWd"):
        require(value in men_expr or any(value in line for line in cone.lines),
                f"men: the bound leaf `{value}` is not used")
    for value in ("i.hWd", "i.frz", "i.oEe", "i.oOut"):
        require(value in misr_expr or any(value in line for line in cone.lines),
                f"misr: the bound leaf `{value}` is not used")
    return {
        "defs": [
            _def("rtlMen", "(s : State) (i : Input) : Bool", men_expr, cone),
            _def("rtlMisr", "(s : State) (i : Input) : BitVec 32", misr_expr, cone),
        ],
        "step": "⟨rtlMen s i, rtlMisr s i⟩",
        "count": 2,
    }


def extract_ctrl(modules):
    """(b2) The replay timer, `cev`, the level shift and the six registers."""
    top = modules[TOP]
    comb = DbgCone("ctrlcomb", top)
    _bind(comb, CTRL1_LEAVES)
    for name in ("rise", "fall"):
        bits = net_bits(top, name, 16)
        require(bits[13:] == ("0", "0", "0"),
                f"{TOP}.{name}: bits 13..15 are not tied to 0")
        comb.leaf_bits(bits[:13], f"(BitVec.truncate 13 {name})")
    tick = comb.expression(net_bits(top, "replay_tick", 20))
    interval = comb.expression(net_bits(top, "replay_interval", 20))
    apply = comb.expression(net_bits(top, "replay_apply", 1))
    late = comb.expression(net_bits(top, "replay_late", 1))
    cev = comb.expression(net_bits(top, "cev", 1))
    for value in ("dc",):
        require(value in tick or any(value in line for line in comb.lines),
                "replay_tick: the DC leaf is not used")
    for value in ("rw",):
        require(value in interval or any(value in line for line in comb.lines),
                "replay_interval: the record leaf is not used")
    for value in ("replay", "frz", "rv", "dc", "rw"):
        require(value in apply or any(value in line for line in comb.lines),
                f"replay_apply: the bound leaf `{value}` is not used")
    for value in ("cen", "replay", "frz", "rise", "fall", "emask"):
        require(value in cev or any(value in line for line in comb.lines),
                f"cev: the bound leaf `{value}` is not used")

    levels_cone = DbgCone("ctrllevels", top)
    for name, width, value in (("rlv", 13, "rlv"), ("emask", 13, "emask"),
                               ("replay_apply", 1, "ap"), ("s_replay_word", 64, "rw")):
        levels_cone.leaf(name, width, value)
    levels = levels_cone.expression(net_bits(top, "replay_levels", 13))
    for value in ("rlv", "emask", "ap", "rw"):
        require(value in levels or any(value in line for line in levels_cone.lines),
                f"replay_levels: the bound leaf `{value}` is not used")

    regs = DbgCone("ctrlregs", top)
    data = {
        "replay": regs.register("replay", 1, "s.replay"),
        "cen": regs.register("cen", 1, "s.cen"),
        "emask": regs.register("emask", 13, "s.emask"),
        "rlv": regs.register("rlv", 13, "s.rlv"),
        "rlvPrev": regs.register("rlv_prev", 13, "s.rlvPrev"),
        "dc": regs.register("dc", 19, "s.dc"),
    }
    _bind(regs, CTRL_REG_LEAVES)
    apply_call = "apply s.replay i.frz (bitAt i.replayValid 0) s.dc i.replayWord"
    regs.leaf("replay_apply", 1, f"({apply_call})")
    regs.leaf("replay_levels", 13,
              f"(replayLevels s.rlv s.emask ({apply_call}) i.replayWord)")
    regs.leaf("cev", 1, "(cev s.cen s.replay i.frz i.rise i.fall s.emask)")
    fields = {
        "replay": regs.expression(data["replay"]),
        "cen": regs.expression(data["cen"]),
        "emask": regs.expression(data["emask"]),
        "rlv": regs.expression(data["rlv"]),
        "rlvPrev": regs.expression(data["rlvPrev"]),
        "dc": regs.expression(data["dc"]),
    }
    required = {
        "replay": ("i.dWrEctl", "i.hEctl", "i.hWd", "i.cwData", "s.replay"),
        "cen": ("i.dWrEctl", "i.hEctl", "i.hWd", "i.cwData", "s.cen"),
        "emask": ("i.dWrEm0", "i.hEm0", "i.dWrEm1", "i.hEm1", "s.emask"),
        "rlv": ("i.dWrRlv0", "i.hRlv0", "i.dWrRlv1", "i.hRlv1", "replayLevels"),
        "rlvPrev": ("i.frz", "s.rlv", "s.rlvPrev"),
        "dc": ("i.dWrEctl", "i.frz", "i.replayWord", "apply", "cev", "s.dc"),
    }
    for name, expr in fields.items():
        text = expr + "".join(regs.lines)
        for value in required[name]:
            require(value in text, f"{name}: the bound leaf `{value}` is not used")
    return {
        "defs": [
            _def("rtlTick", "(dc : BitVec 19) : BitVec 20", tick, comb),
            _def("rtlInterval", "(rw : BitVec 32) : BitVec 20", interval, comb),
            _def("rtlApply", "(replay frz : Bool) (rv : BitVec 2) (dc : BitVec 19) (rw : BitVec 32) : Bool", apply, comb),
            _def("rtlLate", "(replay frz : Bool) (rv : BitVec 2) (dc : BitVec 19) (rw : BitVec 32) : Bool", late, comb),
            _def("rtlReplayLevels", "(rlv emask : BitVec 13) (ap : Bool) (rw : BitVec 32) : BitVec 13", levels, levels_cone),
            _def("rtlCev", "(cen replay frz : Bool) (rise fall : BitVec 16) (emask : BitVec 13) : Bool", cev, comb),
            _def("rtlReplay", "(s : State) (i : Input) : Bool", fields["replay"], regs),
            _def("rtlCen", "(s : State) (i : Input) : Bool", fields["cen"], regs),
            _def("rtlEmask", "(s : State) (i : Input) : BitVec 13", fields["emask"], regs),
            _def("rtlRlv", "(s : State) (i : Input) : BitVec 13", fields["rlv"], regs),
            _def("rtlRlvPrev", "(s : State) (i : Input) : BitVec 13", fields["rlvPrev"], regs),
            _def("rtlDc", "(s : State) (i : Input) : BitVec 19", fields["dc"], regs),
        ],
        "step": ("⟨rtlReplay s i, rtlCen s i, rtlEmask s i, rtlRlv s i, "
                 "rtlRlvPrev s i, rtlDc s i⟩"),
        "count": 12,
    }


def _pm_macro_check(modules, cell):
    """Check one `md2_pmem` instance against the SRAM macro contract."""
    module = modules[cell["type"]]
    port = {name: tuple(module["ports"][name]["bits"]) for name in module["ports"]}
    sram = module["cells"].get("u_sram")
    require(sram is not None, f"{cell['type']}: no SRAM macro instance (USE_IHP_SRAM?)")
    require(sram["type"] == "RM_IHPSG13_1P_256x64_c2_bm_bist",
            f"{cell['type']}.u_sram: unexpected macro")
    pins = {pin: tuple(bits) for pin, bits in sram["connections"].items()}
    require(pins["A_CLK"] == port["clk"], "u_sram.A_CLK is not the module clock")
    require(pins["A_ADDR"] == port["addr"], "u_sram.A_ADDR is not the port address")
    require(pins["A_DOUT"] == port["rd"], "u_sram.A_DOUT is not the read port")
    require(pins["A_WEN"] == port["we"], "u_sram.A_WEN is not the write enable")
    require(len(pins["A_DIN"]) == 64, "u_sram.A_DIN: expected 64 bits")
    for lane in range(8):
        chunk = pins["A_DIN"][8 * lane:8 * lane + 8]
        require(chunk == port["wd"], f"u_sram.A_DIN lane {lane} is not the write byte")
    # A_MEN = ren | we and A_REN = ren & ~we, exactly as md2_pmem writes them.
    men = pins["A_MEN"]
    ren = pins["A_REN"]
    require(len(men) == 1 and len(ren) == 1, "u_sram: unexpected mask widths")
    # The two gate nets are named in md2_pmem; check them through their cells.
    require(_gate(module, men, port, "or"), "u_sram.A_MEN is not (ren | we)")
    require(_gate(module, ren, port, "and"), "u_sram.A_REN is not (ren & ~we)")
    require(len(pins["A_BM"]) == 64, "u_sram.A_BM: expected 64 bits")
    for lane in range(8):
        chunk = pins["A_BM"][8 * lane:8 * lane + 8]
        require(chunk == tuple(port["be"][lane] for _ in range(8)),
                f"u_sram.A_BM lane {lane} is not be[{lane}]")
    require(pins["A_DLY"] == ("1",), "u_sram.A_DLY is not 1 (registered read)")
    for name in ("A_BIST_CLK", "A_BIST_EN", "A_BIST_MEN", "A_BIST_WEN", "A_BIST_REN"):
        require(pins[name] == ("0",), f"u_sram.{name} is not tied to 0")
    for name in ("A_BIST_ADDR", "A_BIST_BM", "A_BIST_DIN"):
        require(set(pins[name]) == {"0"}, f"u_sram.{name} is not tied to 0")


def _gate(module, output, port, kind):
    """Is `output` the `kind` gate over the module ports `we`/`ren`?"""
    drivers = [cell for cell in module["cells"].values()
               if tuple(cell["connections"].get("Y", ())) == output]
    require(len(drivers) == 1, f"u_sram: no unique driver for the {kind} gate")
    cell = drivers[0]
    operands = [tuple(cell["connections"][pin]) for pin in ("A", "B")]
    we = tuple(port["we"])
    ren = tuple(port["ren"])
    if kind == "or":
        require(cell["type"] == "$or", "u_sram.A_MEN driver is not an OR")
        return set(operands) == {we, ren}
    require(cell["type"] == "$and", "u_sram.A_REN driver is not an AND")
    nots = [other for other in module["cells"].values()
            if other["type"] == "$not" and
            tuple(other["connections"]["A"]) == we]
    require(len(nots) == 1, "u_sram.A_REN: no unique complement of we")
    return set(operands) == {ren, tuple(nots[0]["connections"]["Y"])}


def extract_pmem(modules):
    """(c) The host/fetch port muxing of the two program memories."""
    top = modules[TOP]
    for cell in ("u_pmem0", "u_pmem1"):
        require(cell in top["cells"], f"{TOP}.{cell}: missing program memory")
        require(top["cells"][cell]["type"] == "md2_pmem",
                f"{TOP}.{cell}: unexpected module")
    for cell, index in (("u_pmem0", 0), ("u_pmem1", 1)):
        _pm_macro_check(modules, top["cells"][cell])

    we0 = net_bits(top, "pm_we0", 1)
    we1 = net_bits(top, "pm_we1", 1)
    be = net_bits(top, "pm_be", 8)
    hwd = net_bits(top, "h_wd", 8)
    fen = net_bits(top, "fen", 2)
    for cell, index in (("u_pmem0", 0), ("u_pmem1", 1)):
        pins = {pin: tuple(bits) for pin, bits in top["cells"][cell]["connections"].items()}
        require(pins["we"] == (we0[0],) if index == 0 else pins["we"] == (we1[0],),
                f"{cell}.we is not pm_we{index}")
        require(pins["be"] == be, f"{cell}.be is not pm_be")
        require(pins["wd"] == hwd, f"{cell}.wd is not h_wd")
        require(pins["ren"] == (fen[index],), f"{cell}.ren is not fen[{index}]")
        require(pins["clk"] == tuple(top["ports"]["clk"]["bits"]), f"{cell}.clk is not clk")

    first = DbgCone("pmem", top)
    _bind(first, PMEM_LEAVES)
    we0_expr = first.expression(we0)
    we1_expr = first.expression(we1)
    be_expr = first.expression(be)
    for value in ("hWr", "inPrg", "a"):
        require(value in we0_expr or any(value in line for line in first.lines),
                f"pm_we0: the bound leaf `{value}` is not used")
    for value in ("hWr", "inPrg", "a"):
        require(value in we1_expr or any(value in line for line in first.lines),
                f"pm_we1: the bound leaf `{value}` is not used")
    require("a" in be_expr or any("a" in line for line in first.lines),
            "pm_be: the address leaf is not used")

    second = DbgCone("pmaddr", top)
    _bind(second, PMEM_ADDR_LEAVES)
    addr0 = second.expression(tuple(top["cells"]["u_pmem0"]["connections"]["addr"]))
    addr1 = second.expression(tuple(top["cells"]["u_pmem1"]["connections"]["addr"]))
    for name, expr, index in (("pm_addr0", addr0, 0), ("pm_addr1", addr1, 1)):
        text = expr + "".join(second.lines)
        for value in (f"we{index}", "a", "fadr"):
            require(value in text, f"{name}: the bound leaf `{value}` is not used")
    return {
        "defs": [
            _def("rtlPmWe0", "(hWr inPrg : Bool) (a : BitVec 16) : Bool", we0_expr, first),
            _def("rtlPmWe1", "(hWr inPrg : Bool) (a : BitVec 16) : Bool", we1_expr, first),
            _def("rtlPmBe", "(a : BitVec 16) : BitVec 8", be_expr, first),
            _def("rtlPmAddr0", "(we0 : Bool) (a fadr : BitVec 16) : BitVec 8", addr0, second),
            _def("rtlPmAddr1", "(we1 : Bool) (a fadr : BitVec 16) : BitVec 8", addr1, second),
        ],
        "count": 5,
    }


def _adff(module, name, width):
    """The D bus of one active-low asynchronously cleared flop from `rst_n`."""
    bits = net_bits(module, name, width)
    rst_n = tuple(module["ports"]["rst_n"]["bits"])
    matches = [cell for cell in module["cells"].values()
               if cell["type"] in ("$dff", "$adff") and
               tuple(cell["connections"]["Q"]) == bits]
    require(len(matches) == 1, f"{TOP}.{name}: expected exactly one register driver")
    cell = matches[0]
    require(cell["type"] == "$adff", f"{TOP}.{name}: expected an asynchronous clear")
    require(tuple(cell["connections"]["ARST"]) == rst_n and
            int(cell["parameters"]["ARST_POLARITY"], 2) == 0 and
            int(cell["parameters"]["ARST_VALUE"], 2) == 0,
            f"{TOP}.{name}: the clear is not rst_n's active-low assertion")
    require(tuple(cell["connections"]["CLK"]) == tuple(module["ports"]["clk"]["bits"]) and
            int(cell["parameters"]["CLK_POLARITY"], 2) == 1,
            f"{TOP}.{name}: expected posedge clk")
    return tuple(cell["connections"]["D"])


def extract_reset(modules):
    """(d) The two-flop reset synchroniser."""
    top = modules[TOP]
    first_d = _adff(top, "rst_m", 1)
    second_d = _adff(top, "rst_q", 1)
    cone = DbgCone("reset", top)
    _bind(cone, RESET_LEAVES)
    m_expr = cone.expression(first_d)
    q_expr = cone.expression(second_d)
    require(q_expr.strip() == "s.rstM",
            f"rst_q: the second stage does not sample rst_m (got {q_expr})")
    require(m_expr.strip() == "true", f"rst_m: the first stage is not tied high ({m_expr})")
    return {
        "defs": [
            _def("rtlRstM", "(i : Input) : Bool", f"(if i.rstN then {m_expr} else false)", cone),
            _def("rtlRstQ", "(s : State) (i : Input) : Bool", f"(if i.rstN then {q_expr} else false)", cone),
        ],
        "step": "⟨rtlRstM i, rtlRstQ s i⟩",
        "count": 2,
    }


def lean_defs(namespace, defs, step=None, step_type=None):
    """Emit the extracted definitions of one sub-cut."""
    lines = [f"namespace {namespace}", ""]
    for name, signature, expr in defs:
        lines.append(f"/-- The elaborated `{name}` cone. -/")
        lines.append(f"def {name} {signature} :=")
        lines.append(expr)
        lines.append("")
    if step is not None:
        lines.append("/-- The elaborated whole transition. -/")
        lines.append(f"def rtlStep {step_type} :=")
        lines.append(f"  {step}")
        lines.append("")
    lines.append(f"end {namespace}")
    lines.append("")
    return "\n".join(lines)


def lean_source(info, fingerprint):
    """Emit the extracted definitions; the proof template is appended by the caller."""
    parts = [f"""import Metronome.Debug

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {fingerprint}
-- Elaboration: read_verilog -I src -D USE_IHP_SRAM; hierarchy -check; proc;
-- opt_clean.  Every cone below is the elaborated netlist, not the specification.

set_option autoImplicit false
set_option maxHeartbeats 8000000
-- A mutant may legitimately disconnect a bound leaf; the extraction's leaf-use
-- checks catch that, and the equivalence theorem then fails on the real cone.
set_option linter.unusedVariables false

namespace Metronome.Debug
"""]
    parts.append(lean_defs("Pins", info["pins"]["defs"]))
    parts.append(lean_defs("Digest", info["digest"]["defs"], info["digest"]["step"],
                           "(s : State) (i : Input) : State"))
    parts.append(lean_defs("Ctrl", info["ctrl"]["defs"], info["ctrl"]["step"],
                           "(s : State) (i : Input) : State"))
    parts.append(lean_defs("Pmem", info["pmem"]["defs"]))
    parts.append(lean_defs("Reset", info["reset"]["defs"], info["reset"]["step"],
                           "(s : State) (i : Input) : State"))
    parts.append("end Metronome.Debug\n")
    return "\n".join(parts)


def extract_all(modules):
    return {
        "pins": extract_pins(modules),
        "digest": extract_digest(modules),
        "ctrl": extract_ctrl(modules),
        "pmem": extract_pmem(modules),
        "reset": extract_reset(modules),
    }


def axiom_audit(text):
    """Collect the `#print axioms` records from a Lean run."""
    return {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
            for name, axioms in AXIOM_LINE.findall(text)}


def declarations(source):
    """Map line numbers to the declaration they belong to."""
    owner = {}
    current = None
    for number, line in enumerate(source.splitlines(), start=1):
        match = DECL_LINE.match(line)
        if match:
            current = match.group(1)
        owner[number] = current
    return owner


def failed_declaration(source, output):
    """The first declaration Lean reports an error in, if any."""
    owner = declarations(source)
    for number in ERROR_LINE.findall(output):
        name = owner.get(int(number))
        if name:
            return name
    first = next((line.strip() for line in output.splitlines() if "error:" in line), None)
    return first


def run_lean(source, filename, artifact, lake, work, evidence):
    """Run the generated proof with the suite's flags and a 900 s timeout."""
    path = Path(work) / filename
    path.write_text(source, encoding="utf-8")
    if evidence:
        (Path(evidence) / artifact).write_text(source, encoding="utf-8")
    for attempt in range(2):
        try:
            return run([lake, "env", "lean", "-j1", "-DwarningAsError=true", str(path)],
                       HERE, timeout=900)
        except subprocess.TimeoutExpired:
            if attempt:
                raise
    raise AssertionError("unreachable")


def check_debug(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the elaborated debug/pin/program/reset cut and its Lean proofs.

    `rtlil_or_json` is a parsed Yosys design, a path to `design.json`, or a
    Verilog source directory to elaborate.  Evidence is written to `out_dir` as
    `<case>.debug.lean`, `<case>.log` and `<case>.axioms.txt`.  Returns a result
    dictionary; a rejected cut raises `DebugRejected` (proof or audit) or
    `UnsupportedRTL` (structure or wiring).
    """
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-debug-{case}-") as tmp:
        work = Path(tmp)
        is_json = isinstance(rtlil_or_json, dict) or (
            isinstance(rtlil_or_json, (str, Path)) and Path(rtlil_or_json).suffix == ".json")
        if is_json:
            modules = load_modules(rtlil_or_json)
            fingerprint = "not recorded: parsed design JSON"
        else:
            snapshot = snapshot_of(rtlil_or_json)
            modules, fingerprint, commands, yosys_log = elaborate(snapshot, work / "rtl", yosys)
            log.append(f"RTL snapshot SHA-256: {fingerprint}\n")
            log.append(f"Yosys command: {commands}\n")
            log.append(yosys_log)
        try:
            info = extract_all(modules)
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the structural cut: {exc}\n")
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise
        log.append("Extracted: {} pin, {} digest, {} control, {} program and "
                   "{} reset definitions\n".format(
                       info["pins"]["count"], info["digest"]["count"], info["ctrl"]["count"],
                       info["pmem"]["count"], info["reset"]["count"]))
        source = lean_source(info, fingerprint) + "\n" + TEMPLATE.read_text(encoding="utf-8")
        result = run_lean(source, "DebugProof.lean", f"{case}.debug.lean",
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
            "fingerprint": fingerprint,
            "source": out_dir / f"{case}.debug.lean",
            "log": out_dir / f"{case}.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            stage = failed_declaration(source, result.stdout)
            raise DebugRejected(f"{case}: {outcome}\n" + "".join(log),
                                reason=f"{outcome}: {stage}",
                                code=result.returncode)
    return report


def debug_mutations():
    """The planted regressions, as snapshot transformers."""
    def replace(before, after):
        def apply(snapshot):
            require("project.v" in snapshot, "mutation: missing project.v")
            data = snapshot["project.v"]
            require(data.count(before) == 1,
                    f"mutation: anchor changed in project.v: {before!r}")
            snapshot = dict(snapshot)
            snapshot["project.v"] = data.replace(before, after, 1)
            return snapshot
        return apply

    return (
        # The digest polynomial loses its low bit.
        ("misr_poly", replace(b"32'h04C11DB7", b"32'h04C11DB6")),
        # The digest advances in a frozen cycle.
        ("misr_frozen", replace(b"else if (men & ~frz)     misr <=",
                                b"else if (men)     misr <=")),
        # The replay mask ignores EMASK: every pin is replayed.
        ("replay_mask_ignores_emask",
         replace(b"wire [12:0] replay_mask = emask & {13{replay}};",
                 b"wire [12:0] replay_mask = {13{replay}};")),
        # A drained core write beats a host write to ECTL.
        ("ectl_core_beats_host",
         replace(b"if (d_wr_ectl) {replay, cen} <= h_ectl ? h_wd[1:0] : cw_pending_data[1:0];",
                 b"if (d_wr_ectl) {replay, cen} <= cw_pending_data[1:0];")),
        # An ECTL write no longer restarts DC.
        ("dc_not_cleared",
         replace(b"if (d_wr_ectl) dc <= 19'd0;", b"if (1'b0) dc <= 19'd0;")),
        # Pins 13..15 read the synchroniser bits instead of constant 0.
        ("pins_high_s2",
         replace(b"wire [15:0] lvl  = {3'd0, pins_level};",
                 b"wire [15:0] lvl  = {s2[15:13], pins_level};")),
        # The program byte lane is off by one.
        ("pm_be_shift_one",
         replace(b"wire [7:0]   pm_be = 8'd1 << a_prg[2:0];",
                 b"wire [7:0]   pm_be = 8'd1 << (a_prg[2:0] + 3'd1);")),
        # The reset synchroniser releases after one edge.
        ("rstq_one_stage",
         replace(b"rst_m <= 1'b1; rst_q <= rst_m;", b"rst_m <= 1'b1; rst_q <= 1'b1;")),
    )


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted regression is rejected.

    Returns one `(case, rejected, stage, exit)` record per mutation and raises
    `DebugRejected` if any mutant is accepted.  `exit` is the case's own
    verification exit code: the Lean exit code when the generated proof rejects
    the mutant, 0 when only the structural check ran.
    """
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-debug-mutants-") as tmp:
        for case, transform in debug_mutations():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_debug(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"structural check: {exc}", 0))
                continue
            except DebugRejected as exc:
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
                        help="also check the planted debug/pin/program/reset regressions")
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
            raise DebugRejected("tool version query failed")

        build = run([lake, "build", "Metronome.Debug"], HERE, timeout=900)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise DebugRejected("lake build Metronome.Debug failed")

        snapshot = snapshot_of(ROOT / "src")
        report = check_debug(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        emit(f"baseline: {report['outcome']}")
        records.append(("baseline", report["outcome"], report["exit"], report["ok"]))
        if not report["ok"]:
            code = 1

        if args.mutations and code == 0:
            for case, rejected, stage, case_exit in run_mutations(snapshot, artifacts, lake, yosys):
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
    except (OSError, KeyError, RuntimeError, ValueError, subprocess.TimeoutExpired,
            UnsupportedRTL) as exc:
        raise SystemExit(f"debug check failed: {exc}") from exc
