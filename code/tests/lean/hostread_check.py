"""Check the host read path of the Metronome chip top.

The host command cut (`hostcmd_check.py`) covers the command, address and data
phases of `src/md2_host.v` and stops at the read request `rd` and the
acknowledge latch `rack`.  This module covers the response path the earlier cut
leaves out (`README.md`, "Host SPI command cut", gap "read path tx, rackv, miso,
rd_val"):

* the two response registers `tx` and `rackv` of `src/md2_host.v`;
* the elaborated host register-read mux `rd_val` of `src/project.v` against the
  independent map of `Metronome.HostRead` (ISA_TABLES_V2 "Host address map");
* the MISO pin path (`u_host.miso` -> `uo_out[0]`);
* the "no host read has a side effect" property: the elaborated `h_rd` net
  enters nothing but the data-RAM host request slot.

Run it from the repository root:

    python code/tests/lean/hostread_check.py
    python code/tests/lean/hostread_check.py --mutations

`check_hostread(src_dir_or_json, out_dir, *, lake, yosys, case)` returns the
report dictionary and raises on a rejected cut; `run_mutations(snapshot,
out_dir, lake, yosys)` plants the regressions on temporary copies of `src/`.
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
from verify import HERE, ROOT, TOP, check_host_top, constant_value, run, run_lean
import hostcmd_check as hostcmd

HOST_CELL = "u_host"
HOST_MODULE = "md2_host"
MEM_CELL = "u_mem"
DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_hostread_v4_20261120"
TEMPLATE = HERE / "HostReadEquivalence.lean.in"
AXIOM_LINE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)

# The register blocks of the host map: the specification's literals.  The
# adapter requires the elaborated and generated constants to equal these and
# the header to agree, so a moved map fails closed instead of redefining the
# specification.
SPEC_BLOCKS = (("inCtl", 0x2400, 0x10), ("inLrt", 0x2410, 0x20),
               ("inTrt", 0x2440, 0x0C), ("inSrt", 0x2450, 0x08),
               ("inDbg", 0x2460, 0x20))
DATA_BASE = 0x1000
DATA_SPAN = 0x0800

# Every free state signal of the read map, as (Regs field, top-level net, width).
REG_LEAVES = (
    ("runG", "run_g", 1), ("cwOverrun", "cw_overrun", 1), ("memhaz", "memhaz", 1),
    ("conflict", "conflict", 1), ("irqen", "irqen", 2), ("inb", "inb", 8),
    ("outb", "outb", 8), ("outv", "outv", 1), ("inv", "inv", 1),
    ("lPh", "l_ph", 64), ("lHeld", "l_held", 4), ("lFired", "l_fired", 12),
    ("lSp", "l_sp", 4), ("lRen", "l_ren", 4), ("lArm", "l_arm", 4),
    ("lRun", "l_run", 4), ("lComm", "l_comm", 16), ("lStaged", "l_staged", 16),
    ("lIn", "l_in", 8), ("lCap", "l_cap", 20), ("lTapmiss", "l_tapmiss", 4),
    ("tPc", "t_pc", 48), ("tOvr", "t_ovr", 6), ("tLate", "t_late", 6),
    ("tEn", "t_en", 6), ("tArmed", "t_armed", 6), ("tRunning", "t_running", 6),
    ("tReady", "t_ready", 6), ("sPos", "s_pos", 24), ("sStarved", "s_starved", 2),
    ("sBidx", "s_bidx", 6), ("freeze", "freeze", 1), ("men", "men", 1),
    ("replay", "replay", 1), ("cen", "cen", 1), ("misr", "misr", 32),
    ("emask", "emask", 13), ("rlv", "rlv", 13), ("accA", "acc_a", 8),
    ("accN", "acc_n", 1), ("accC", "acc_c", 1), ("accZ", "acc_z", 1),
    ("fl", "fl", 16), ("cRv", "c_rv", 2), ("cXv", "c_xv", 2), ("xt", "xt", 6),
    ("cFpc", "c_fpc", 16),
)

# The eight command-machine registers plus the two response registers.
READ_REGISTERS = (
    ("st", 3, "state.phase"), ("bitc", 3, "state.bitc"), ("rx", 7, "state.rx"),
    ("is_rd", 1, "state.isRd"), ("addr", 16, "state.addr"), ("wr", 1, "state.wr"),
    ("wdata", 8, "state.wdata"), ("rd", 1, "state.rd"), ("rack", 1, "state.rack"),
    ("tx", 8, "state.tx"), ("rackv", 8, "state.rackv"),
)

SIMP_LEMMAS = (
    "rtlStep, step, phaseNext, bitcNext, rxNext, isRdNext, addrNext, wrNext, "
    "wdataNext, rdNext, rackNext, txNext, rackvNext, completing, sr, ack, ackv, "
    "byteIn, addrInc, shifted, State.toHostCmd, Input.toHostCmd")


class HostReadRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated read cut."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


class ReadCone(DffCone):
    """A `DffCone` that also decodes the read-path cells.

    `$pmux`, `$logic_not` and `$reduce_or` are the case-mux, zero test and
    reduction shapes of `rd_val`; `$mul` of a constant and `$shiftx`/`$shr` of a
    dynamic index are the part-select arithmetic.  Each extra shape is decoded
    here rather than in the shared adapter.  They stay fail-closed: a `$mul`
    with two non-constant operands, a shift with a non-constant amount or an
    unknown cell raises `UnsupportedRTL`.
    """

    EXTRA = ("$pmux", "$logic_not", "$reduce_or", "$mul", "$shiftx", "$shr", "$shl")

    def __init__(self, name, module):
        super().__init__(name, module)
        self.x_bits = 0
        self.used = set()
        for cell_name, cell in module["cells"].items():
            kind = cell["type"]
            if kind not in ("$pmux", "$logic_not", "$reduce_or", "$mul", "$shr", "$shl"):
                continue
            pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
            where = f"{name}.{cell_name} ({kind})"
            if kind == "$pmux":
                width = int(cell["parameters"]["WIDTH"], 2)
                selects = int(cell["parameters"]["S_WIDTH"], 2)
                require(len(pins["Y"]) == width and len(pins["A"]) == width and
                        len(pins["B"]) == width * selects and len(pins["S"]) == selects,
                        f"{where}: unexpected pmux widths")
                hostcmd.pmux_selects_exclusive(module, pins["S"], where)
            elif kind == "$logic_not":
                require(set(pins) == {"A", "Y"} and len(pins["Y"]) == 1 and
                        len(pins["A"]) == int(cell["parameters"]["A_WIDTH"], 2),
                        f"{where}: expected one scalar result")
            elif kind == "$reduce_or":
                require(len(pins["Y"]) == 1 and len(pins["A"]) ==
                        int(cell["parameters"]["A_WIDTH"], 2),
                        f"{where}: expected one scalar reduction")
            elif kind == "$mul":
                require(len(pins) == 3, f"{where}: unexpected multiply ports")
            else:
                require(len(pins["Y"]) >= 1 and len(pins) == 3,
                        f"{where}: unexpected shift ports")
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = (kind, pins, cell["parameters"], where)

    def bus_bound(self, bits):
        """A conservative upper bound of the unsigned value of a bus.

        `2 ** w - 1` is always sound; a constant multiply and an addition of
        bounded operands sharpen it, which is what the 32-bit part-select
        indices need to stay clear of the sign bit.
        """
        if bits and all(bit in ("0", "1", "x") for bit in bits):
            return int("".join({"0": "0", "1": "1", "x": "0"}[bit]
                               for bit in reversed(bits)), 2)
        driver = self.drivers.get(bits)
        if driver is not None:
            kind, pins, params, _ = driver
            if kind == "$mul" and _is_constant(pins["A"]) != _is_constant(pins["B"]):
                if _is_constant(pins["A"]):
                    factor, other = constant_value(pins["A"], "bound"), pins["B"]
                else:
                    factor, other = constant_value(pins["B"], "bound"), pins["A"]
                bound = factor * self.bus_bound(other)
                if bound < 2 ** len(bits):
                    return bound
            elif kind == "$add":
                bound = self.bus_bound(pins["A"]) + self.bus_bound(pins["B"])
                if bound < 2 ** len(bits):
                    return bound
            elif kind == "$and" and _is_constant(pins["B"]):
                mask = constant_value(pins["B"], "bound")
                bound = min(self.bus_bound(pins["A"]), mask)
                return bound
        return 2 ** len(bits) - 1

    def _bit_bool(self, bit):
        # Yosys leaves `x` where the value is unobservable (an optimised-out
        # branch).  The cut reads it as 0, the two-state value a netlist
        # constant tie-off takes; `x_bits` records how often that happened.
        if bit == "x":
            self.x_bits += 1
            return "false"
        return super()._bit_bool(bit)

    def expression(self, bits):
        driver = self.drivers.get(bits)
        if driver is not None:
            self.used.add(driver[3].split(f"{self.name}.", 1)[-1].split(" (")[0])
        if bits and all(bit in ("0", "1", "x") for bit in bits):
            value = int("".join({"0": "0", "1": "1", "x": "0"}[bit]
                                for bit in reversed(bits)), 2)
            self.x_bits += bits.count("x")
            if len(bits) == 1:
                return "true" if bits == ("1",) else "false"
            return f"({value} : BitVec {len(bits)})"

        driver = self.drivers.get(bits)
        if driver is not None and driver[0] == "$pmux":
            _, pins, params, where = driver
            width = int(params["WIDTH"], 2)
            selects = int(params["S_WIDTH"], 2)
            require(len(bits) == width, f"{where}: unexpected result bus")
            expr = self.expression(pins["A"])
            for index in reversed(range(selects)):
                branch = self.expression(tuple(pins["B"][index * width:(index + 1) * width]))
                expr = f"(if {self._bit_bool(pins['S'][index])} then {branch} else {expr})"
            wire = f"{self.name}{len(self.lines)}"
            self.lines.append(f"  let {wire} := {expr}")
            self.bound[bits] = wire
            return wire
        if driver is not None and driver[0] == "$logic_not":
            _, pins, params, where = driver
            source_width = int(params["A_WIDTH"], 2)
            require(len(bits) == 1 and source_width > 0, f"{where}: unexpected result bus")
            expr = f"({self.expression(pins['A'])} == (0 : BitVec {source_width}))"
            wire = f"{self.name}{len(self.lines)}"
            self.lines.append(f"  let {wire} := {expr}")
            self.bound[bits] = wire
            return wire
        if driver is not None and driver[0] == "$reduce_or":
            _, pins, _, where = driver
            require(len(bits) == 1, f"{where}: unexpected result bus")
            expr = f"({self.expression(pins['A'])} != 0)"
            wire = f"{self.name}{len(self.lines)}"
            self.lines.append(f"  let {wire} := {expr}")
            self.bound[bits] = wire
            return wire
        if driver is not None and driver[0] == "$mul":
            _, pins, params, where = driver
            width = int(params["Y_WIDTH"], 2)
            require(len(bits) == width, f"{where}: unexpected result bus")
            a, b = pins["A"], pins["B"]
            require(_is_constant(a) != _is_constant(b),
                    f"{where}: expected a constant index multiply")
            if _is_constant(a):
                factor, other = constant_value(a, where), b
            else:
                factor, other = constant_value(b, where), a
            require(factor in (2, 3, 4, 5, 8, 12, 16),
                    f"{where}: constant {factor} is not a documented index multiply")
            expr = f"(mulC {factor} (BitVec.setWidth 32 {self.expression(other)}))"
            wire = f"{self.name}{len(self.lines)}"
            self.lines.append(f"  let {wire} := {expr}")
            self.bound[bits] = wire
            return wire
        if driver is not None and driver[0] == "$shiftx":
            _, pins, params, where = driver
            width = int(params["Y_WIDTH"], 2)
            source_width = int(params["A_WIDTH"], 2)
            require(len(bits) == width and width <= source_width,
                    f"{where}: unexpected result bus")
            require(int(params["B_SIGNED"], 2) == 0 or self.bus_bound(pins["B"]) < 2 ** 31,
                    f"{where}: signed shift amount could be negative")
            shifted = (f"(BitVec.ushiftRight {self.expression(pins['A'])} "
                       f"({self.expression(pins['B'])}).toNat)")
            expr = (f"(({shifted} &&& (1 : BitVec {source_width})) != 0)" if width == 1
                    else f"(BitVec.truncate {width} {shifted})")
            wire = f"{self.name}{len(self.lines)}"
            self.lines.append(f"  let {wire} := {expr}")
            self.bound[bits] = wire
            return wire
        if driver is not None and driver[0] in ("$shr", "$shl"):
            _, pins, params, where = driver
            width = int(params["Y_WIDTH"], 2)
            shift = constant_value(pins["B"], where) if _is_constant(pins["B"]) else None
            require(len(bits) == width and shift is not None,
                    f"{where}: expected a constant shift amount")
            operator = ">>>" if driver[0] == "$shr" else "<<<"
            expr = f"({self.expression(pins['A'])} {operator} {shift})"
            wire = f"{self.name}{len(self.lines)}"
            self.lines.append(f"  let {wire} := {expr}")
            self.bound[bits] = wire
            return wire
        return super().expression(bits)


def assemble_fields(cone, bits):
    """Assemble a bus that is a concatenation of fields.

    Yosys writes a Verilog concatenation as a bus of bits with no single
    driver.  Reading it back field by field (a run of one bound bus, a run of
    one cell output, a constant field, a single Boolean) keeps the shape of the
    specification's `++`, which is what the proof compares against.
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
            pieces.append(f"(if {first[1]} then (1 : BitVec 1) else 0)")
        else:
            _, key, offset = first
            value = cone.expression(key)
            pieces.append(f"(BitVec.truncate {count} (BitVec.ushiftRight {value} {offset}))")
    expr = pieces[0]
    for piece in pieces[1:]:
        expr = f"({expr} ++ {piece})"
    return expr


def _field_of(cone, bit):
    """Where one bit of an assembled bus comes from.

    A bound whole bus (a leaf or a checked alias) describes the bit best; a
    cell output is the fallback for the assembly of combinational fields.
    """
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


def _is_constant(bits):
    return bool(bits) and all(bit in ("0", "1") for bit in bits)


class HostReadCone(hostcmd.HostCone):
    """The host command cone, reading concatenations field by field.

    A Verilog concatenation carries no single driver, so the shared adapter
    would assemble it bit by bit; reading it back field by field keeps the
    shape of the specification's `++`, which is what the proof compares.
    """



def elaborate(snapshot, work, yosys):
    return hostcmd.elaborate(snapshot, work, yosys)


def snapshot_of(directory):
    return hostcmd.snapshot_of(directory)


def load_modules(rtlil_or_json):
    return hostcmd.load_modules(rtlil_or_json)


def module_header(path=ROOT / "src" / "md2_map.vh"):
    """Read the host-map base and span constants of the generated header."""
    text = path.read_text(encoding="utf-8")

    def value(name):
        match = re.search(rf"localparam \[15:0\] {name} = 16'h([0-9A-Fa-f]+);", text)
        require(match is not None, f"md2_map.vh: missing {name}")
        return int(match.group(1), 16)

    return {
        "ctl": (value("HA_CTRL_BASE"), value("HSPAN_CTRL")),
        "lrt": (value("HA_LRT_BASE"), value("HSPAN_LRT")),
        "trt": (value("HA_TRT_BASE"), value("HSPAN_TRT")),
        "srt": (value("HA_SRT_BASE"), value("HSPAN_SRT")),
        "dbg": (value("HA_DBG_BASE"), value("HSPAN_DBG")),
        "data": (value("HA_DATA_BASE"), value("HSPAN_DATA")),
    }


def check_header():
    """The specification's literals must be the generated header's."""
    header = module_header()
    spec = dict(zip(("ctl", "lrt", "trt", "srt", "dbg"),
                    ((base, span) for _, base, span in SPEC_BLOCKS)))
    spec["data"] = (DATA_BASE, DATA_SPAN)
    for name, value in spec.items():
        require(header[name] == value,
                f"host map drifted from the specification at {name}: {header[name]} != {value}")
    return header


def check_read_top(modules, header):
    """Check the host instance, the read nets and the side-effect freedom."""
    check_host_top(modules)
    top = modules[TOP]
    host = top["cells"][HOST_CELL]
    pins = host["connections"]
    for port, net in (("rd_val", "rd_val"), ("hland", "h_land"), ("hland_d", "h_land_d"),
                      ("rd_data", "in_data"), ("rd", "h_rd")):
        require(pins[port] == top["netnames"][net]["bits"],
                f"{HOST_CELL}.{port}: unexpected connection")
    # MISO: the host port drives the top net, which is the low pin bit.
    miso = top["netnames"]["miso"]["bits"]
    require(len(miso) == 1 and pins["miso"] == miso, "miso: unexpected host port")
    require(top["ports"]["uo_out"]["bits"][0] == miso[0],
            "uo_out[0] is not the MISO net")
    drivers = {}
    for name, cell in top["cells"].items():
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] in ("output", "inout"):
                for bit in bits:
                    drivers[bit] = (name, pin)
    require(drivers.get(miso[0]) == (HOST_CELL, "miso"),
            "miso is not uniquely driven by the host instance")

    # The data-RAM window: in_data = (ha - HA_DATA_BASE) < HSPAN_DATA.
    in_data = top["netnames"]["in_data"]["bits"]
    require(len(in_data) == 1, "in_data must be scalar")
    owner = drivers[in_data[0]]
    cell = top["cells"][owner[0]]
    require(owner[1] == "Y" and cell["type"] == "$lt", "in_data is not a window compare")
    span = constant_value(tuple(cell["connections"]["B"]), "in_data span")
    require(span == header["data"][1], "in_data span differs from the header")
    sub_name, sub_pin = drivers[tuple(cell["connections"]["A"])[0]]
    sub = top["cells"][sub_name]
    require(sub["type"] == "$sub" and sub_pin == "Y", "in_data window is not a subtraction")
    base = constant_value(tuple(sub["connections"]["B"]), "in_data base")
    require(base == header["data"][0], "a_dat base differs from the header")
    require(tuple(sub["connections"]["A"]) == tuple(top["netnames"]["ha"]["bits"]),
            "a_dat does not subtract from ha")

    # No host read has a side effect: h_rd enters only h_set = (h_wr | h_rd) & in_data.
    h_rd = tuple(top["netnames"]["h_rd"]["bits"])
    require(len(h_rd) == 1, "h_rd must be scalar")
    consumers = []
    for name, cell in top["cells"].items():
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] == "input" and h_rd[0] in bits:
                consumers.append((name, cell, pin))
    require(len(consumers) == 1, f"h_rd has {len(consumers)} consumers, expected only h_set")
    name, cell, _ = consumers[0]
    require(cell["type"] in ("$or", "$logic_or"), "h_rd consumer is not the h_set OR")
    or_out = tuple(cell["connections"]["Y"])
    require(len(or_out) == 1, "h_set OR must be scalar")
    other = tuple(tuple(bits) for pin, bits in cell["connections"].items()
                  if cell["port_directions"][pin] == "input" and tuple(bits) != h_rd)
    require(tuple(other) == (tuple(top["netnames"]["h_wr"]["bits"]),),
            "h_set does not OR h_rd with h_wr")
    and_owners = [n for n, c in top["cells"].items()
                  if c["type"] in ("$and", "$logic_and") and
                  or_out[0] in [bit for pin, bits in c["connections"].items()
                                if c["port_directions"][pin] == "input" for bit in bits]]
    require(len(and_owners) == 1, "h_set OR has multiple consumers")
    and_cell = top["cells"][and_owners[0]]
    require(and_cell["type"] in ("$and", "$logic_and"), "h_set is not an AND with in_data")
    require(tuple(and_cell["connections"]["Y"]) ==
            tuple(top["cells"][MEM_CELL]["connections"]["h_set"]),
            "h_set AND does not drive the host request port")
    require(tuple(in_data) in [tuple(bits) for pin, bits in and_cell["connections"].items()
                               if and_cell["port_directions"][pin] == "input"],
            "h_set is not masked by in_data")

    # Inside the RAM arbiter the request slot is the only state h_set reaches.
    mem = modules[top["cells"][MEM_CELL]["type"]]
    set_bit = tuple(mem["ports"]["h_set"]["bits"])[0]
    slot = {(cell["connections"]["Q"])[0] for cell in mem["cells"].values()
            if cell["type"] in ("$dff", "$adff") and
            _reaches(mem, set_bit, tuple(cell["connections"]["D"]))}
    named = {}
    for net, net_value in mem["netnames"].items():
        for bit in net_value["bits"]:
            named[bit] = net
    reached = {named.get(bit, bit) for bit in slot}
    require(reached <= {"hq", "hqw", "hqa", "hqd"},
            f"the host request slot reaches {sorted(map(str, reached))}")
    require(len(reached) >= 1, "the host request slot reaches no register")


def _reaches(module, seed, bits):
    """Whether the net `bits` depends combinationally on `seed` (registers stop)."""
    drivers = {}
    for name, cell in module["cells"].items():
        for pin, port in cell["connections"].items():
            if cell["port_directions"][pin] in ("output", "inout"):
                for bit in port:
                    drivers[bit] = (name, pin)
    seen = set()
    stack = list(bits)
    while stack:
        bit = stack.pop()
        if bit in ("0", "1") or bit in seen:
            continue
        seen.add(bit)
        if bit == seed:
            return True
        owner = drivers.get(bit)
        if owner is None:
            continue
        cell = module["cells"][owner[0]]
        if cell["type"] in ("$dff", "$adff"):
            continue
        for pin, port in cell["connections"].items():
            if cell["port_directions"][pin] == "input":
                stack.extend(port)
    return False


def check_rdval_cells(modules, header):
    """Require the elaborated block constants to be the specification's."""
    top = modules[TOP]
    cone = ReadCone("rdval", top)
    _bind_regs(cone, top)
    cone.leaf("ha", 16, "a")
    cone.expression(tuple(top["netnames"]["rd_val"]["bits"]))
    used = [top["cells"][name] for name in cone.used]
    subs = [constant_value(tuple(cell["connections"]["B"]), "rd_val sub")
            for cell in used if cell["type"] == "$sub"]
    expect = [base for _, base, _ in SPEC_BLOCKS]
    require(sorted(subs) == sorted(expect),
            f"rd_val subtractions are {sorted(subs)}, expected {sorted(expect)}")
    spans = [constant_value(tuple(cell["connections"]["B"]), "rd_val span")
             for cell in used if cell["type"] == "$lt"]
    expect_spans = [span for _, _, span in SPEC_BLOCKS]
    require(sorted(spans) == sorted(expect_spans),
            f"rd_val window spans are {sorted(spans)}, expected {sorted(expect_spans)}")
    return cone


def _bind_regs(cone, top):
    for field, net, width in REG_LEAVES:
        cone.leaf(net, width, f"state.{field}")


def extract_rdval(modules):
    top = modules[TOP]
    cone = ReadCone("rdval", top)
    _bind_regs(cone, top)
    cone.leaf("ha", 16, "a")
    expr = cone.expression(tuple(top["netnames"]["rd_val"]["bits"]))
    return "\n".join(cone.lines), expr, len(cone.lines), cone.x_bits


class DontCareCone(ReadCone):
    """`ReadCone` with every `x` bit read as a free variable instead of 0.

    Each `x` bit of the elaborated `rd_val` cone becomes one bit of a single
    free vector `xs`.  Proving the result equal to the specification for every
    `xs` shows the read value does not depend on any don't-care arm, so a
    synthesis flow may tie them to anything (including a function of other
    signals, since the claim holds pointwise).  The number of variables must
    equal the zero reading's `x_bits`; a mismatch fails closed.
    """

    def __init__(self, name, module):
        super().__init__(name, module)
        self.x_used = 0

    def _fresh(self, width):
        offset = self.x_used
        self.x_used += width
        return offset

    def _bit_bool(self, bit):
        if bit == "x":
            return f"(xs.getLsbD {self._fresh(1)})"
        return super()._bit_bool(bit)

    def expression(self, bits):
        if bits and "x" in bits and all(bit in ("0", "1", "x") for bit in bits):
            width = len(bits)
            if width == 1:
                return self._bit_bool(bits[0])
            ones = sum(1 << i for i, bit in enumerate(bits) if bit == "1")
            mask = sum(1 << i for i, bit in enumerate(bits) if bit == "x")
            offset = self._fresh(width)
            return (f"(({ones} : BitVec {width}) ||| "
                    f"(BitVec.extractLsb' {offset} {width} xs &&& ({mask} : BitVec {width})))")
        return super().expression(bits)


def extract_rdval_dontcare(modules, expected_x):
    """The `rd_val` cone with its don't-care bits as the free vector `xs`."""
    top = modules[TOP]
    cone = DontCareCone("rdvalx", top)
    _bind_regs(cone, top)
    cone.leaf("ha", 16, "a")
    expr = cone.expression(tuple(top["netnames"]["rd_val"]["bits"]))
    require(cone.x_bits == 0,
            f"rd_val don't-care reading left {cone.x_bits} x bits read as 0")
    require(cone.x_used == expected_x,
            f"rd_val don't-care reading bound {cone.x_used} free bits, "
            f"not the {expected_x} x bits of the zero reading")
    return "\n".join(cone.lines), expr, max(cone.x_used, 1)


def check_address_increment(module):
    """Check `addr_i` is the address register or its increment.

    `md2_host.v` writes `wire [15:0] addr_i = (wr | ack) ? addr + 1 : addr;`
    with `ack = rack | hland`.  The cut reads `addr_i` as the specification's
    `addrInc`, so the adapter has to check that this is what the net is: a mux
    whose arms are `addr` and `addr + 1` and whose select is the disjunction of
    the write strobe and the two response strobes.
    """
    addr = tuple(module["netnames"]["addr"]["bits"])
    wr = tuple(module["netnames"]["wr"]["bits"])
    rack = tuple(module["netnames"]["rack"]["bits"])
    hland = tuple(module["ports"]["hland"]["bits"])
    require(len(wr) == 1 and len(rack) == 1 and len(hland) == 1,
            "md2_host: expected scalar strobes")
    drivers = {}
    for name, cell in module["cells"].items():
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] in ("output", "inout"):
                for bit in bits:
                    drivers[bit] = (name, pin)
    addr_i = tuple(module["netnames"]["addr_i"]["bits"])
    require(len(addr_i) == 16, "md2_host.addr_i: expected 16 bits")
    owner = drivers.get(addr_i[0])
    require(owner is not None, "md2_host.addr_i: no driver")
    mux = module["cells"][owner[0]]
    require(mux["type"] == "$mux" and owner[1] == "Y", "addr_i is not a mux")
    pins = {pin: tuple(bits) for pin, bits in mux["connections"].items()}
    require(pins["A"] == addr, "addr_i does not select the address register")
    require(pins["B"][0:1] and drivers.get(pins["B"][0], (None,))[0] is not None,
            "addr_i increment arm is undriven")
    add = module["cells"][drivers[pins["B"][0]][0]]
    require(add["type"] == "$add", "addr_i increment arm is not an addition")
    add_pins = {pin: tuple(bits) for pin, bits in add["connections"].items()}
    require(add_pins["A"] == addr, "addr_i increment does not add to the address")
    require(constant_value(add_pins["B"], "addr_i increment") == 1,
            "addr_i increments by something other than one")
    # the select is (wr | rack | hland)
    reached = set()
    stack = [pins["S"][0]]
    seen = set()
    while stack:
        bit = stack.pop()
        if bit in ("0", "1") or bit in seen:
            continue
        seen.add(bit)
        if bit in wr or bit in rack or bit in hland:
            reached.add(bit)
            continue
        owner = drivers.get(bit)
        require(owner is not None, "addr_i select has an undriven input")
        cell = module["cells"][owner[0]]
        require(cell["type"] in ("$or", "$logic_or"), "addr_i select is not an OR tree")
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] == "input":
                stack.extend(bits)
    require(reached == {wr[0], rack[0], hland[0]},
            "addr_i select is not (wr | rack | hland)")


def extract_read(module):
    """The twelve next-state fields of the elaborated host link."""
    st = hostcmd.net_bits(module, "st", 3)
    bitc = hostcmd.net_bits(module, "bitc", 3)
    rx = hostcmd.net_bits(module, "rx", 7)
    is_rd = hostcmd.net_bits(module, "is_rd", 1)
    addr = hostcmd.net_bits(module, "addr", 16)
    wr = hostcmd.net_bits(module, "wr", 1)
    wdata = hostcmd.net_bits(module, "wdata", 8)
    rd = hostcmd.net_bits(module, "rd", 1)
    rack = hostcmd.net_bits(module, "rack", 1)
    tx = hostcmd.net_bits(module, "tx", 8)
    rackv = hostcmd.net_bits(module, "rackv", 8)
    byte_in = hostcmd.net_bits(module, "byte_in", 8)
    mosi = module["ports"]["mosi"]["bits"]
    require(byte_in == (mosi[0],) + rx, "md2_host.byte_in is not {rx, mosi}")
    cone = HostReadCone("hostread", module)
    for name, width, value in (
        ("rst_n", 1, "input.resetN"), ("sck", 1, "input.sck"),
        ("sck_p", 1, "input.sckPrev"), ("cs_n", 1, "input.csN"),
        ("mosi", 1, "input.mosi"), ("rd_data", 1, "input.rdData"),
        ("rd_val", 8, "input.rdVal"), ("hland", 1, "input.hland"),
        ("hland_d", 8, "input.hlandD"),
    ):
        cone.input(name, width, value)
    check_address_increment(module)
    cone.alias("byte_in", 8, "(HostCmd.byteIn (state.toHostCmd 0#8) input.toHostCmd)")
    cone.leaf("addr_i", 16, "(HostCmd.addrInc (state.toHostCmd 0#8) input.toHostCmd)")
    next_bits = {}
    for name, width, kind in (("st", 3, "$dff"), ("bitc", 3, "$dff"), ("rx", 7, "$dff"),
                              ("is_rd", 1, "$dff"), ("addr", 16, "$dff"), ("wr", 1, "$dff"),
                              ("wdata", 8, "$dff"), ("rd", 1, "$dff"), ("rack", 1, "$dff"),
                              ("tx", 8, "$dff"), ("rackv", 8, "$dff")):
        next_bits[name] = cone.register(name, width, dict(
            (n, v) for n, w, v in READ_REGISTERS if n == name)[name])
    fields = {name: cone.expression(bits) for name, bits in next_bits.items()}
    require(not cone.registers, "unmodeled read-path state")
    return {"lets": "\n".join(cone.lines), "fields": fields, "registers": len(next_bits)}


def extract_miso(modules):
    """The MISO cone of the elaborated host module (`tx[7]`)."""
    module = modules[hostcmd.host_module(modules)["attributes"].get("hdlname", HOST_MODULE)] \
        if HOST_MODULE not in modules else modules[HOST_MODULE]
    cone = DffCone("miso", module)
    cone.free("tx", 8, "state.tx")
    bits = tuple(module["ports"]["miso"]["bits"])
    require(len(bits) == 1, "md2_host.miso must be scalar")
    expr = cone._bit_bool(bits[0])
    return "\n".join(cone.lines), expr


def lean_read(info, rdval, rdvalx, miso, fingerprint):
    fields = info["fields"]
    return f"""import Metronome.HostRead

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {fingerprint}
-- Host link: the `md2_host` instance `{HOST_CELL}` (all eleven registers).
-- Read map: the `rd_val` mux of the chip top, with every observable state
-- signal bound free.  MISO: the host module's `miso` output cone.

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Metronome.HostRead

/-- The elaborated host-link transition. -/
def rtlStep (state : State) (input : Input) : State :=
{info['lets']}
  \u27e8{fields['st']}, {fields['bitc']}, {fields['rx']}, {fields['is_rd']},
   {fields['addr']}, {fields['wr']}, {fields['wdata']}, {fields['rd']},
   {fields['rack']}, {fields['tx']}, {fields['rackv']}\u27e9

/-- The elaborated `rd_val` mux: the host register-read value at address `a`. -/
def rtlRdVal (a : BitVec 16) (state : Regs) : BitVec 8 :=
{rdval[0]}
  {rdval[1]}

/-- Width of the free don't-care vector of `rtlRdValX`. -/
def xWidth : Nat := {rdvalx[2]}

/-- The elaborated `rd_val` mux with every Yosys `x` bit read from `xs`. -/
def rtlRdValX (a : BitVec 16) (state : Regs) (xs : BitVec xWidth) : BitVec 8 :=
{rdvalx[0]}
  {rdvalx[1]}

/-- The elaborated MISO cone of the host module. -/
def rtlMiso (state : State) : Bool :=
{miso[0]}
  {miso[1]}

"""


def axiom_audit(text):
    return {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
            for name, axioms in AXIOM_LINE.findall(text)}


def check_hostread(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the elaborated host read path and its generated Lean proofs."""
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-hostread-{case}-") as tmp:
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

        build = run([lake, "build", "Metronome.HostRead"], HERE)
        log.append(build.stdout)
        if build.returncode != 0:
            raise HostReadRejected(
                f"{case}: lake build Metronome.HostRead failed\n" + "".join(log))
        try:
            header = check_header()
            check_read_top(modules, header)
            check_rdval_cells(modules, header)
            info = extract_read(hostcmd.host_module(modules))
            rdval = extract_rdval(modules)
            rdvalx = extract_rdval_dontcare(modules, rdval[3])
            miso = extract_miso(modules)
            log.append(f"Host read cut: {info['registers']} registers, "
                       f"{rdval[2]} read-map cells ({rdval[3]} don't-care bits), "
                       f"MISO cone {miso[1]}\n")
            source = lean_read(info, rdval, rdvalx, miso, fingerprint)
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the structural read check: {exc}\n")
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise
        source += TEMPLATE.read_text(encoding="utf-8")
        result = run_lean(source, "HostReadProof.lean", f"{case}.hostread.lean",
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
            "rdval_cells": rdval[2],
            "x_bits": rdval[3],
            "miso": miso[1],
            "fingerprint": fingerprint,
            "source": out_dir / f"{case}.hostread.lean",
            "log": out_dir / f"{case}.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            first = next((line.strip() for line in result.stdout.splitlines()
                          if "error:" in line), outcome)
            first = first.split("HostReadProof.lean:", 1)[-1]
            raise HostReadRejected(f"{case}: {outcome}\n" + "".join(log),
                                   reason=f"{outcome}: {first[:150]}",
                                   code=result.returncode)
    return report


def read_mutations():
    """The planted read-path regressions, as snapshot transformers."""
    def replace(before, after, filename="project.v", count=1):
        def apply(snapshot):
            require(filename in snapshot, f"mutation: missing {filename}")
            data = snapshot[filename]
            require(data.count(before.encode()) == count,
                    f"mutation: anchor changed in {filename}: {before}")
            return {**snapshot, filename: data.replace(before.encode(), after.encode(), count)}
        return apply

    def chain(*steps):
        def apply(snapshot):
            for step in steps:
                snapshot = step(snapshot)
            return snapshot
        return apply

    def two(first, second):
        return chain(first, second)

    return [
        # ERRSUM/STICKY byte layout: the sticky flags are read in the wrong order.
        ("hostread_sticky_layout", replace(
            "rd_val = {5'd0, cw_overrun, memhaz, conflict};",
            "rd_val = {5'd0, conflict, memhaz, cw_overrun};")),
        # The default value of the read mux is no longer zero, so program
        # memory, the data RAM and the configuration window read a constant.
        ("hostread_default_nonzero", replace(
            "\n        rd_val = 8'd0;\n", "\n        rd_val = 8'h5A;\n")),
        # LRT.PHASE reads the wrong half of the phase bus.
        ("hostread_phase_slice", replace(
            "rd_val = l_ph[16*li +: 8];", "rd_val = l_ph[16*li + 8 +: 8];")),
        # The response loads TX one cycle early: the request cycle's `rd`
        # already loads the waiting value instead of the acknowledge cycle.
        ("hostread_tx_early", replace(
            "            tx    <= ack ? ackv : tx;",
            "            tx    <= (rd | hland) ? ackv : tx;", filename="md2_host.v")),
        # TX takes the data-RAM byte for a register read and the register value
        # for a RAM landing.
        ("hostread_ackv_swap", replace(
            "wire [7:0] ackv = rack ? rackv : hland_d;",
            "wire [7:0] ackv = rack ? hland_d : rackv;", filename="md2_host.v")),
        # Unmapped thread and stream register offsets read `x` instead of 0.  The zero
        # reading of the don't-care bits still matches the map, so only
        # `rtlRdValX_eq_spec` (every `x` free) can reject it.
        # (The anchor is the thread and stream blocks' shared default line.)
        ("hostread_default_x", replace(
            "default:     rd_val = 8'd0;", "default:     rd_val = 8'bx;", count=2)),
        # MISO comes from the wrong end of the shift register.
        ("hostread_miso_lsb", replace(
            "    assign miso = tx[7];", "    assign miso = tx[0];", filename="md2_host.v")),
    ]


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted read-path regression is rejected."""
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-hostread-mutants-") as tmp:
        for case, transform in read_mutations():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_hostread(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"structural check: {exc}", 0))
                continue
            except HostReadRejected as exc:
                records.append((case, True, f"generated Lean: {exc.reason}", exc.code))
                continue
            records.append((case, not report["ok"], report["outcome"], report["exit"]))
    accepted = [case for case, rejected, _, _ in records if not rejected]
    require(not accepted, f"mutants accepted: {', '.join(accepted)}")
    return records


def write_status(path, records):
    lines = ["case\toutcome\texit\texpectation"]
    for case, outcome, code, ok in records:
        lines.append(f"{case}\t{outcome}\t{code}\t{'ok' if ok else 'FAILED'}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mutations", action="store_true",
                        help="also check the planted read-path regressions")
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
            raise HostReadRejected("tool version query failed")

        build = run([lake, "build", "Metronome.HostRead"], HERE)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise HostReadRejected("lake build Metronome.HostRead failed")

        snapshot = snapshot_of(ROOT / "src")
        report = check_hostread(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        emit(f"baseline: {report['outcome']} ({report['registers']} registers, "
             f"{report['rdval_cells']} read-map cells, {report['x_bits']} don't-care bits, "
             f"MISO {report['miso']})")
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
        raise SystemExit(f"Host read check failed: {exc}") from exc
