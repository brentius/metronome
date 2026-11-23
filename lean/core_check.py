"""Check the two elaborated `md2_core` instances against `Metronome.Core`.

`Metronome/Core.lean` is an independent statement of SPEC_V2 §5 (state,
`XV/RV/FPC/XT/XL/RR/IR`, the `C`/`JC` guards, the per-move enables,
`taken`/`npc`, `jmp`/`pse`/`load`/`free`, the `RR` circular dispatch and the
watchers), §6 (the 8-bit move bus and its source vector), §7 (guard and jump
conditions, `JUMP_GUARDS`) and §12.3 (the frozen cycle).  This module
re-elaborates the chip top with `verify.py`'s Yosys recipe, takes the two
specialised `md2_core` modules (`C = 0` and `C = 1`, `NT = 6`), extracts every
register input and every combinational output from their cells, and emits Lean
that proves, register by register and output by output, that the elaborated
transition is the specification's, then lifts the equality to traces.

The cut is fail-closed.  A Yosys cell shape the translator cannot express, an
undriven or sliced net, a second driver or a register inside a combinational
cone raises `UnsupportedRTL`.  The shapes this core needs beyond `rtlil.py` are
added here (not in the shared adapter): `$mul` (the `8 * i_s` source index),
wide `$shiftx` (the 512-bit source-vector read and the 20-bit `l_cap` read),
`$reduce_or`/`$reduce_bool` (`|cand`), `$logic_not` (`g == 0` comparisons),
`$pmux`, wide `$and`/`$or` (the broadcast masks of the thread selectors and the
source vector), and a one-bit `$mux` as a Lean `Bool`.

Run it from the repository root:

    python lean/core_check.py
    python lean/core_check.py --mutations

`run_mutations()` plants the regressions on temporary copies of `src/` (never
the repository) and requires every one to be rejected.
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
from verify import HERE, ROOT, TOP, run


DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_core_v4_20261121"
TEMPLATE = HERE / "CoreEquivalence.lean.in"
CORE_MODULE = "md2_core"
CORE_CELLS = ("g_core[0].u_core", "g_core[1].u_core")
AXIOM_LINE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)
NO_AXIOM_LINE = re.compile(r"^'([^']+)' does not depend on any axioms$", re.MULTILINE)

# Instruction fields of `wiki/ISA_TABLES_V2.md` (the numbers `md2_defs.vh`
# also carries): (decode net, width, IR low bit).  A drift fails here.
IR_FIELDS = (
    ("i_pause", 1, 0),
    ("i_jmode", 2, 1),
    ("i_imm", 8, 3),
    ("i_cond", 6, 11),
    ("i_jcond", 5, 59),
)
MOVE_FIELDS = ("i_g", "i_s", "i_d")
MOVE_LSB = {"i_g": 17, "i_s": 19, "i_d": 25}

# `JUMP_GUARDS` of `wiki/ISA_TABLES_V2.md` (§7), entry `j` = guard index.
JG_TABLE = (0, 1, 2, 3, 4, 5, 6, 7, 8, 17, 18, 21, 22, 23, 24, 25, 26, 27, 28,
            29, 30, 34, 35, 36, 37, 39, 41, 43, 38, 40, 42, 44)

# Core module ports: (port, width, Lean input field).
INPUTS = (
    ("rst_n", 1, "input.resetN"),
    ("frz", 1, "input.frz"),
    ("run_g", 1, "input.runG"),
    ("rdata", 64, "input.rdata"),
    ("t_ready", 6, "input.tReady"),
    ("t_core", 6, "input.tCore"),
    ("t_line", 12, "input.tLine"),
    ("t_pc", 48, "input.tPc"),
    ("t_w0c", 36, "input.tW0c"),
    ("t_w1c", 36, "input.tW1c"),
    ("t_w0h", 48, "input.tW0h"),
    ("t_w1h", 48, "input.tW1h"),
    ("guards", 64, "input.guards"),
    ("g_line", 20, "input.gLine"),
    ("srcs", 512, "input.srcs"),
    ("l_in", 8, "input.lIn"),
    ("l_cap", 20, "input.lCap"),
)

# Registers: (net, width, Lean state field).
REGISTERS = (
    ("xv", 1, "state.xv"),
    ("rv", 1, "state.rv"),
    ("fpc", 8, "state.fpc"),
    ("xt", 3, "state.xt"),
    ("xl", 2, "state.xl"),
    ("rr", 3, "state.rr"),
    ("ir", 64, "state.ir"),
)

# Combinational outputs: (port, width, Lean `Out` field).
OUTPUTS = (
    ("fetch_en", 1, "fetchEn"),
    ("fetch_addr", 8, "fetchAddr"),
    ("pause_o", 1, "pauseO"),
    ("npc_o", 8, "npcO"),
    ("disp_o", 1, "dispO"),
    ("disp_e", 3, "dispE"),
    ("xt_o", 3, "xtO"),
    ("xl_o", 2, "xlO"),
    ("mv_en", 3, "mvEn"),
    ("mv_src", 18, "mvSrc"),
    ("mv_dst", 18, "mvDst"),
    ("mv_data", 24, "mvData"),
    ("dbg_xv", 1, "dbgXv"),
    ("dbg_rv", 1, "dbgRv"),
    ("dbg_fpc", 8, "dbgFpc"),
)

# Chip-top wires the two instances must be wired to (SPEC §2/§5/§12.3).
TOP_WIRING = {
    "clk": "clk",
    "rst_n": "rst_q",
    "frz": "frz",
    "run_g": "run_g",
}


class CoreRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated core cut."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


class CoreCone(DffCone):
    """A `DffCone` that also decodes the vector cells `md2_core` lowers to.

    The shared adapter only indexes scalar logic; the core's cones use wide
    bitwise `$and`/`$or` (broadcast masks and the source vector), `$reduce_or`
    and `$logic_not` (`|cand`, `code == 0`), `$mul` (`8 * i_s`), wide `$shiftx`
    (indexed part selects of the 512-bit source vector, `l_in` and `l_cap`) and
    one-bit muxes as Lean `Bool`.  `$pmux` is accepted with the same
    mutually-exclusive-select proof the host cut uses.  Every extension stays
    fail-closed: an unknown cell, an unresolvable bus or a partial overlap still
    raises `UnsupportedRTL`.
    """

    EXTRA = ("$reduce_or", "$reduce_bool", "$logic_not", "$mul")

    def __init__(self, name, module):
        super().__init__(name, module)
        for cell_name, cell in module["cells"].items():
            kind = cell["type"]
            if kind not in self.EXTRA + ("$pmux",):
                continue
            pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
            params = cell["parameters"]
            where = f"{name}.{cell_name} ({kind})"
            require(pins.get("Y") is not None, f"{where}: missing output")
            if kind == "$pmux":
                width = int(params["WIDTH"], 2)
                selects = int(params["S_WIDTH"], 2)
                require(len(pins["Y"]) == width and len(pins["A"]) == width and
                        len(pins["B"]) == width * selects and len(pins["S"]) == selects,
                        f"{where}: unexpected pmux widths")
                pmux_selects_exclusive(module, pins["S"], where)
            elif kind == "$mul":
                require(len(pins["Y"]) == int(params["Y_WIDTH"], 2) and
                        len(pins["A"]) == int(params["A_WIDTH"], 2) and
                        len(pins["B"]) == int(params["B_WIDTH"], 2) and
                        int(params["A_SIGNED"], 2) == 0 and
                        int(params["B_SIGNED"], 2) == 0,
                        f"{where}: unexpected unsigned multiply")
            elif kind == "$shiftx":
                require(len(pins["Y"]) == int(params["Y_WIDTH"], 2) and
                        len(pins["A"]) == int(params["A_WIDTH"], 2) and
                        len(pins["B"]) == int(params["B_WIDTH"], 2),
                        f"{where}: unexpected indexed shift")
            else:
                require(len(pins["Y"]) == 1 and int(params["Y_WIDTH"], 2) == 1,
                        f"{where}: expected a one-bit result")
                require(len(pins["A"]) == int(params["A_WIDTH"], 2),
                        f"{where}: unexpected operand width")
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = (kind, pins, params, where)

    def _bind(self, bits, expression):
        wire = f"{self.name}{len(self.lines)}"
        self.lines.append(f"  let {wire} := {expression}")
        self.bound[bits] = wire
        return wire

    def _nameable(self, run):
        """True if `run` can be named as one Lean expression."""
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
        """Assemble a bus from contiguous, nameable runs and constants."""
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
                    kind in ("$mux",) or kind in self.EXTRA):
                return self.expression(output)
        return super()._bit_bool(bit)

    def expression(self, bits):
        driver = self.drivers.get(bits)
        if driver is None:
            return super().expression(bits)
        kind, pins, params, where = driver
        require(bits not in self.resolving, f"{where}: combinational loop")
        if kind == "$mul":
            width = len(bits)
            require(width == int(params["Y_WIDTH"], 2), f"{where}: unexpected result bus")
            self.resolving.add(bits)
            a = f"(BitVec.setWidth {width} {self.expression(pins['A'])})"
            b = f"(BitVec.setWidth {width} {self.expression(pins['B'])})"
            self.resolving.remove(bits)
            return self._bind(bits, f"({a} * {b})")
        if kind == "$shiftx":
            width = len(bits)
            self.resolving.add(bits)
            source = self.expression(pins["A"])
            shift = self.expression(pins["B"])
            self.resolving.remove(bits)
            if width == 1:
                # A scalar bit select is a Lean `Bool`, like every other scalar net.
                return self._bind(bits, f"((BitVec.truncate 1 (BitVec.ushiftRight "
                                        f"{source} (BitVec.toNat {shift}))) != 0)")
            return self._bind(bits, f"(BitVec.truncate {width} "
                                    f"(BitVec.ushiftRight {source} "
                                    f"(BitVec.toNat {shift})))")
        if kind == "$pmux":
            width = int(params["WIDTH"], 2)
            selects = int(params["S_WIDTH"], 2)
            require(len(bits) == width, f"{where}: unexpected result bus")
            self.resolving.add(bits)
            expr = self.expression(pins["A"])
            for index in reversed(range(selects)):
                branch = self.expression(tuple(pins["B"][index * width:(index + 1) * width]))
                expr = f"(if {self._bit_bool(pins['S'][index])} then {branch} else {expr})"
            self.resolving.remove(bits)
            return self._bind(bits, expr)
        if kind in ("$reduce_or", "$reduce_bool"):
            require(len(bits) == 1, f"{where}: expected a one-bit result")
            self.resolving.add(bits)
            expression = "(" + " || ".join(
                f"({self._bit_bool(bit)})" for bit in pins["A"]) + ")"
            self.resolving.remove(bits)
            return self._bind(bits, expression)
        if kind == "$logic_not":
            require(len(bits) == 1, f"{where}: expected a one-bit result")
            self.resolving.add(bits)
            source = pins["A"]
            if len(source) == 1:
                expression = f"(!{self._bit_bool(source[0])})"
            else:
                expression = f"({self.expression(source)} == (0 : BitVec {len(source)}))"
            self.resolving.remove(bits)
            return self._bind(bits, expression)
        if kind == "$mux" and len(bits) == 1:
            select = pins["S"]
            require(len(select) == 1 and len(pins["A"]) == 1 and len(pins["B"]) == 1,
                    f"{where}: expected a one-bit mux")
            self.resolving.add(bits)
            expression = (f"(if {self._bit_bool(select[0])} then "
                          f"{self._bit_bool(pins['B'][0])} else "
                          f"{self._bit_bool(pins['A'][0])})")
            self.resolving.remove(bits)
            return self._bind(bits, expression)
        if kind not in ("$and", "$or", "$not") or len(bits) == 1:
            return super().expression(bits)
        if kind == "$not":
            require(len(pins["A"]) == len(bits) == int(params["A_WIDTH"], 2) ==
                    int(params["Y_WIDTH"], 2),
                    f"{where}: expected an equal-width bitwise not")
            self.resolving.add(bits)
            expression = f"(~~~{self.expression(pins['A'])})"
            self.resolving.remove(bits)
            return self._bind(bits, expression)
        # A wide bitwise AND/OR, including the broadcast shape of `{8{hit}} & v`.
        width = len(bits)
        left, right = pins["A"], pins["B"]
        require(len(left) == int(params["A_WIDTH"], 2) and
                len(right) == int(params["B_WIDTH"], 2) and
                int(params["Y_WIDTH"], 2) == width and
                len(left) == len(right) == width,
                f"{where}: expected an equal-width bitwise cell")
        self.resolving.add(bits)
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
    result = run([yosys, "-Q", "-q", "-p", commands], work, timeout=600)
    if result.returncode != 0:
        raise CoreRejected(f"Yosys elaboration failed: {result.stdout.strip()}")
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
    require(net is not None, f"{CORE_MODULE}.{name}: missing net")
    require("init" not in net["attributes"],
            f"{CORE_MODULE}.{name}: unexpected initial value")
    bits = tuple(net["bits"])
    require(len(bits) == width,
            f"{CORE_MODULE}.{name}: expected {width} bits, got {len(bits)}")
    return bits


def core_modules(modules):
    """The two specialised `md2_core` modules, keyed by their `C` parameter."""
    found = {}
    for name, module in modules.items():
        if module.get("attributes", {}).get("hdlname") != CORE_MODULE:
            continue
        params = module.get("parameter_default_values", {})
        require("C" in params and "NT" in params,
                f"{name}: missing C/NT parameter defaults")
        c = int(params["C"], 2)
        nt = int(params["NT"], 2)
        require(nt == 6, f"{name}: NT = {nt}, the spec has 6 threads")
        require(c in (0, 1) and c not in found, f"{name}: unexpected duplicate C = {c}")
        found[c] = (name, module)
    require(set(found) == {0, 1},
            f"expected the two core variants, found C = {sorted(found)}")
    return found


def check_core_top(modules):
    """Check the two chip-top instances and record how they are wired.

    Returns, per core index, the top-level nets its ports are connected to.  A
    changed parameter, clock, reset, freeze or program-memory connection fails
    closed instead of probing the wrong instance.
    """
    top = modules[TOP]
    variants = core_modules(modules)
    wiring = {}
    for c in (0, 1):
        name, module = variants[c]
        cell_name = CORE_CELLS[c]
        require(cell_name in top["cells"], f"{TOP}.{cell_name}: missing instance")
        cell = top["cells"][cell_name]
        require(cell["type"] == name,
                f"{cell_name}: is {cell['type']}, not the C = {c} module {name}")
        require(sorted(module["ports"]) == sorted(
            {port for port, _, _ in INPUTS} | {port for port, _, _ in OUTPUTS} | {"clk"}),
            f"{name}: unexpected port list")
        for port, width, _ in INPUTS + (("clk", 1, ""),):
            require(len(module["ports"][port]["bits"]) == width and
                    module["ports"][port]["direction"] == "input",
                    f"{name}.{port}: expected a {width}-bit input")
        for port, width, _ in OUTPUTS:
            require(len(module["ports"][port]["bits"]) == width and
                    module["ports"][port]["direction"] == "output",
                    f"{name}.{port}: expected a {width}-bit output")
        for port, net in TOP_WIRING.items():
            expect = tuple(top["netnames"][net]["bits"])
            require(tuple(cell["connections"][port]) == expect,
                    f"{cell_name}.{port}: not connected to {net}")
        # rdata is the core's own program memory read port, fetch_addr/en the
        # write side of that memory; both must be the matching slice.
        rd = tuple(top["netnames"][f"pm_rd[{c}]"]["bits"])
        require(len(rd) == 64, f"pm_rd[{c}]: expected 64 bits")
        require(tuple(cell["connections"]["rdata"]) == rd,
                f"{cell_name}.rdata: not connected to pm_rd[{c}]")
        fen = tuple(top["netnames"]["fen"]["bits"])[c:c + 1]
        require(tuple(cell["connections"]["fetch_en"]) == fen,
                f"{cell_name}.fetch_en: not connected to fen[{c}]")
        fadr = tuple(top["netnames"]["fadr"]["bits"])[8 * c:8 * c + 8]
        require(tuple(cell["connections"]["fetch_addr"]) == fadr,
                f"{cell_name}.fetch_addr: not connected to fadr[{8 * c}:{8 * c + 8}]")
        dsp = tuple(top["netnames"]["dsp"]["bits"])[c:c + 1]
        require(tuple(cell["connections"]["disp_o"]) == dsp,
                f"{cell_name}.disp_o: not connected to dsp[{c}]")
        wiring[c] = {
            "cell": cell_name,
            "module": name,
            "rdata": f"pm_rd[{c}]",
            "fetch_en": f"fen[{c}]",
            "fetch_addr": f"fadr[{8 * c}:{8 * c + 8}]",
            "disp_o": f"dsp[{c}]",
        }
    return wiring


def check_fields(module):
    """The decode nets are the documented instruction fields of the IR."""
    ir = net_bits(module, "ir", 64)
    for name, width, lsb in IR_FIELDS:
        require(net_bits(module, name, width) == ir[lsb:lsb + width],
                f"{CORE_MODULE}.{name}: not IR[{lsb + width - 1}:{lsb}]")
    for m in range(3):
        for name in MOVE_FIELDS:
            lsb = MOVE_LSB[name] + 14 * m
            require(net_bits(module, f"{name}[{m}]", 6 if name != "i_g" else 2) ==
                    ir[lsb:lsb + (6 if name != "i_g" else 2)],
                    f"{CORE_MODULE}.{name}[{m}]: not IR[{lsb + 5}:{lsb}]")
    require(net_bits(module, "i_imm", 8) == ir[3:11], "i_imm: not IR[10:3]")


def check_jg(module):
    """The `jg` assembly is `JUMP_GUARDS` (SPEC §7) read off the guard vector."""
    grd = net_bits(module, "grd", 64)
    jg = net_bits(module, "jg", 32)
    for j, guard in enumerate(JG_TABLE):
        require(jg[j] == grd[guard],
                f"{CORE_MODULE}.jg[{j}]: not guard {guard} of JUMP_GUARDS")


def extract_core(module, c):
    """Extract every register input and every output of one core variant."""
    cone = CoreCone(f"core{c}", module)
    for port, width, value in INPUTS:
        cone.input(port, width, value)
    next_bits = {}
    for name, width, current in REGISTERS:
        next_bits[name] = cone.register(name, width, current)
    fields = {name: cone.expression(bits) for name, bits in next_bits.items()}
    outs = {}
    for port, width, field in OUTPUTS:
        outs[field] = cone.expression(net_bits(module, port, width))
    return {
        "c": c,
        "lines": list(cone.lines),
        "regs": [fields[name] for name, _, _ in REGISTERS],
        "outs": [outs[field] for _, _, field in OUTPUTS],
        "signals": len(cone.lines),
    }


def lean_core(info, fingerprint, wiring):
    """Emit the two extracted transitions and the proof template."""
    template = TEMPLATE.read_text(encoding="utf-8")
    blocks = []
    for variant in (info[0], info[1]):
        c = variant["c"]
        text = template
        values = {
            "NS": f"Rtl{c}",
            "C": "false" if c == 0 else "true",
            "CELL": wiring[c]["cell"],
            "SIGNALS": str(variant["signals"]),
            "LETS": "\n".join(variant["lines"]),
            "REGS": ", ".join(variant["regs"]),
            "OUTS": ", ".join(variant["outs"]),
        }
        for name, value in values.items():
            require("{{" + name + "}}" in text,
                    f"CoreEquivalence.lean.in: missing {{{{{name}}}}} placeholder")
            text = text.replace("{{" + name + "}}", str(value))
        require("{{" not in text,
                "CoreEquivalence.lean.in: unsubstituted placeholder")
        blocks.append(text)
    header = f"""import Metronome.Core
import Std.Tactic.BVDecide

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {fingerprint}
-- Two elaborated `{CORE_MODULE}` instances: {wiring[0]['cell']} (C = 0) and
-- {wiring[1]['cell']} (C = 1), NT = 6.  Every register input and every
-- combinational output is a Lean function of the elaborated cells; the free
-- leaves are exactly the module ports bound in `rtlStepOut`.

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace Metronome.Core

"""
    return header + "\n".join(blocks) + "\nend Metronome.Core\n"


def axiom_audit(text):
    """Collect the `#print axioms` records from a Lean run."""
    found = {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
             for name, axioms in AXIOM_LINE.findall(text)}
    for name in NO_AXIOM_LINE.findall(text):
        found.setdefault(name, [])
    return found


LEAN_ERROR = re.compile(r"CoreProof\.lean:(\d+):\d+: error")
THEOREM_LINE = re.compile(r"^(?:  )?theorem (\S+)")
NAMESPACE_LINE = re.compile(r"^namespace (\S+)")


def failed_theorem(source, text):
    """Name the first theorem whose proof the Lean run rejected.

    The generated file's `theorem` declarations are the only things checked, so
    mapping the first reported line to the enclosing declaration (with its
    namespace) turns "exit 1" into "rejected by `Rtl1.rtlRv`".
    """
    match = LEAN_ERROR.search(text)
    if match is None:
        return None
    line = int(match.group(1))
    namespace = None
    current = None
    for number, entry in enumerate(source.splitlines(), start=1):
        if number > line:
            break
        ns = NAMESPACE_LINE.match(entry)
        if ns:
            namespace = ns.group(1)
        thm = THEOREM_LINE.match(entry)
        if thm:
            current = thm.group(1)
    if current is None:
        return None
    return f"{namespace}.{current}" if namespace else current


def run_lean(source, filename, artifact, lake, work, evidence, timeout=900):
    """Write and check one generated Lean file with a hard timeout."""
    path = Path(work) / filename
    path.write_text(source, encoding="utf-8")
    if evidence:
        (Path(evidence) / artifact).write_text(source, encoding="utf-8")
    return run([lake, "env", "lean", "-j1", "-DwarningAsError=true", str(path)],
               HERE, timeout=timeout)


def check_core(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the two elaborated cores and the generated Lean proofs.

    `rtlil_or_json` is a parsed Yosys design, a path to `design.json`, or a
    Verilog source directory to elaborate.  Evidence is written to `out_dir` as
    `<case>.core.lean` and `<case>.log`.  Returns a result dictionary; a
    rejected cut raises `CoreRejected` (proof or audit) or `UnsupportedRTL`
    (structure or wiring).
    """
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-core-{case}-") as tmp:
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

        try:
            wiring = check_core_top(modules)
            variants = core_modules(modules)
            info = []
            for c in (0, 1):
                check_fields(variants[c][1])
                check_jg(variants[c][1])
                info.append(extract_core(variants[c][1], c))
                log.append(f"C = {c}: {info[-1]['signals']} extracted signals\n")
            source = lean_core(info, fingerprint, wiring)
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the structural core check: {exc}\n")
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise
        result = run_lean(source, "CoreProof.lean", f"{case}.core.lean",
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
            "signals": [info[0]["signals"], info[1]["signals"]],
            "fingerprint": fingerprint,
            "source": out_dir / f"{case}.core.lean",
            "log": out_dir / f"{case}.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            first = failed_theorem(source, result.stdout)
            if first is not None:
                reason = f"{outcome}, rejected by `{first}`"
            else:
                line = next((line.strip() for line in result.stdout.splitlines()
                             if "error:" in line), outcome)
                reason = f"{outcome}: {line.split('CoreProof.lean:', 1)[-1][:200]}"
            raise CoreRejected(f"{case}: {reason}\n" + "".join(log),
                               reason=reason, code=result.returncode)
    return report


def mutations():
    """The planted core regressions, as snapshot transformers."""
    def replace(name, before, after):
        def apply(snapshot):
            require(name in snapshot, f"mutation: missing {name}")
            data = snapshot[name]
            require(data.count(before.encode()) == 1,
                    f"mutation: anchor changed in {name}: {before}")
            return {**snapshot, name: data.replace(before.encode(), after.encode(), 1)}
        return apply

    return OrderedDict((
        # The circular order starts at `RR + 1` instead of `RR`.
        ("core_rr_plus_one", replace(
            "md2_core.v",
            "assign after_rr[g] = cand[g] & (g[2:0] >= rr);",
            "assign after_rr[g] = cand[g] & (g[2:0] >= (rr + 3'd1));")),
        # `RR` advances on every unfrozen cycle, not only on a dispatch.
        ("core_rr_every_cycle", replace(
            "md2_core.v",
            "if (disp_o) begin\n                xt <= disp_e;",
            "if (1'b1) begin\n                xt <= disp_e;")),
        # The `ifnot` move guard uses `C` instead of `~C`.
        ("core_ifnot_uses_c", replace(
            "md2_core.v",
            "((i_g[m] == GD_IFNOT) & ~cc)",
            "((i_g[m] == GD_IFNOT) & cc)")),
        # A taken jump on a pausing instruction also redirects the fetch.
        ("core_jmp_ignores_pause", replace(
            "md2_core.v",
            "wire jmp  = xa & ~i_pause & taken;",
            "wire jmp  = xa & taken;")),
        # The R word is loaded even when a jump or a pause drops it.
        ("core_load_ignores_jmp", replace(
            "md2_core.v",
            "wire load = ra & ~jmp & ~pse;",
            "wire load = ra;")),
        # Watcher 1 is tested before watcher 0.
        ("core_watcher_order", replace(
            "md2_core.v",
            "wire [7:0] dpc = w0 ? d_w0h : (w1 ? d_w1h : d_pc);",
            "wire [7:0] dpc = w1 ? d_w1h : (w0 ? d_w0h : d_pc);")),
        # A frozen cycle no longer holds the register file: the `!frz` guard on
        # the `XV`/`RV`/`FPC`/`XT`/`XL`/`RR` update is dropped.
        ("core_frz_not_hold", replace(
            "md2_core.v",
            "end else if (!frz) begin",
            "end else begin")),
        # Core 1 dispatches the threads bound to core 0.
        ("core1_wrong_binding", replace(
            "md2_core.v",
            "wire [NT-1:0] mine = (C != 0) ? t_core : ~t_core;",
            "wire [NT-1:0] mine = (C != 0) ? ~t_core : ~t_core;")),
    ))


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted core regression is rejected.

    Returns one `(case, rejected, stage, exit)` record per mutation and raises
    `CoreRejected` if any mutant is accepted.
    """
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-core-mutants-") as tmp:
        for case, transform in mutations().items():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_core(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"structural check: {exc}", 0))
                continue
            except CoreRejected as exc:
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
                        help="also check the planted core regressions")
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
            raise CoreRejected("tool version query failed")

        build = run([lake, "build", "Metronome.Core"], HERE, timeout=900)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise CoreRejected("lake build Metronome.Core failed")

        snapshot = snapshot_of(ROOT / "src")
        try:
            report = check_core(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        except CoreRejected as exc:
            emit(f"baseline: {exc.reason}")
            records.append(("baseline", exc.reason, exc.code, False))
            return 1
        emit(f"baseline: {report['outcome']} "
             f"({report['signals'][0]} / {report['signals'][1]} extracted signals)")
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
        raise SystemExit(f"Core check failed: {exc}") from exc
