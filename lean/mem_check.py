"""Check the data-RAM arbiter cut of the Metronome chip top.

The shared suite covers the host command machine and the host read path, but its
read cut binds the RAM landing `hland`/`hland_d` as free per-cycle inputs.  This
module covers the arbiter that produces them: `src/md2_mem.v` (pointer P0, the
S0/S1 stream port, the host request slot, the RAM port) and the byte-mask
boundary of `src/md2_dmem.v` (the IHP SRAM macro is a black box).

Run it from the repository root:

    python lean/mem_check.py
    python lean/mem_check.py --mutations

The check re-elaborates `src/` with Yosys (`-D USE_IHP_SRAM`, so the data RAM is
the black-box macro of `src/md2_sram_bb.v`), verifies the chip-top wiring, cuts
the fifteen arbiter registers and the nine RAM-port outputs out of the
elaborated `md2_mem` module, and emits Lean that proves the extracted transition
and outputs equal `Metronome.Mem`, an independent statement of SPEC_V2 §6.1-6.2,
§9, §12.3-12.4 and SPEC v1 §6.1, §9a.2-9a.4.  `run_mutations()` plants eight
regressions on temporary copies of `src/` (never the repository).
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

from rtlil import DffCone, UnsupportedRTL, require
from verify import HERE, ROOT, TOP, check_host_top, run


MEM_CELL = "u_mem"
MEM_MODULE = "md2_mem"
DMEM_CELL = "u_dmem"
DMEM_MODULE = "md2_dmem"
HOST_CELL = "u_host"
SRAM_CELL = "u_sram"
SRAM_MODULE = "RM_IHPSG13_1P_512x32_c2_bm_bist"
DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_mem_v4_20261121"
TEMPLATE = HERE / "MemEquivalence.lean.in"
LEAN_TIMEOUT = 900
AXIOM_LINE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)
ERROR_LINE = re.compile(r"MemProof\.lean:(\d+):(\d+): error:")
DECLARATION = re.compile(r"^(?:theorem|def|instance) ([\w.]+)")

# Ports whose top-level net must be exactly the named net (or the named slice).
NET_PORTS = (
    ("frz", 1, "frz"), ("frzd", 1, "frzd"),
    ("s_req", 2, "s_req"), ("s_we", 2, "s_we"), ("s_addr", 22, "s_addr"),
    ("s_wd", 16, "s_wd"),
    ("p_sel", 2, "p_sel"), ("p_rdy", 1, "p_rdy"), ("p_dat", 8, "p_dat"),
    ("p_haz", 1, "p_haz"),
    ("h_wr", 1, "h_wr"), ("h_d", 8, "h_wd"),
    ("h_land", 1, "h_land"), ("h_land_d", 8, "h_land_d"),
)

# The fifteen registers: RTL net, width, current-state value, `State` field.
REGISTERS = (
    ("ptr", 11, "state.ptr", "ptr"),
    ("rq", 2, "state.req", "req"),
    ("rqa", 11, "state.reqAddr", "reqAddr"),
    ("rqd", 8, "state.reqData", "reqData"),
    ("p_rdy", 1, "state.rdy", "rdy"),
    ("p_dat", 8, "state.dat", "dat"),
    ("land", 1, "state.land", "land"),
    ("plane", 2, "state.landLane", "landLane"),
    ("lok", 1, "state.landRdy", "landRdy"),
    ("hq", 1, "state.hostQ", "hostQ"),
    ("hqw", 1, "state.hostWr", "hostWr"),
    ("hqa", 11, "state.hostAddr", "hostAddr"),
    ("hqd", 8, "state.hostData", "hostData"),
    ("h_land", 1, "state.hLand", "hLand"),
    ("hlane", 2, "state.hLane", "hLane"),
)

INPUTS = (
    ("rst_n", 1, "input.resetN"), ("frz", 1, "input.frz"), ("frzd", 1, "input.frzd"),
    ("s_req", 2, "input.sReq"), ("s_we", 2, "input.sWe"), ("s_addr", 22, "input.sAddr"),
    ("s_wd", 16, "input.sWd"), ("s0_word", 1, "input.s0Word"),
    ("s0_wword", 32, "input.s0WWord"), ("p_we", 1, "input.pWe"),
    ("p_sel", 2, "input.pSel"), ("p_d", 8, "input.pData"),
    ("h_set", 1, "input.hSet"), ("h_wr", 1, "input.hWr"),
    ("h_addr", 11, "input.hAddr"), ("h_d", 8, "input.hData"),
    ("m_rd", 32, "input.ramWord"),
)

OUTPUTS = (
    ("s_gnt", 2, "sGnt"), ("m_we", 1, "mWe"), ("m_ren", 1, "mRen"),
    ("m_addr", 9, "mAddr"), ("m_be", 4, "mBe"), ("m_wd", 32, "mWd"),
    ("p_haz", 1, "haz"), ("h_land_d", 8, "hLandD"),
)

class MemRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated arbiter."""

    def __init__(self, message, reason=None, code=1, theorem=None):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code
        self.theorem = theorem


def constant_value(bits, where):
    """Read a Yosys constant bus (little-endian) as an integer."""
    require(bits and all(bit in ("0", "1") for bit in bits),
            f"{where}: expected a constant bus")
    return int("".join(reversed(bits)), 2)


def is_constant(bits):
    return bool(bits) and all(bit in ("0", "1") for bit in bits)


def drivers_of(module):
    """Net bit -> [(cell, port)] for every driving port of a module."""
    drivers = {}
    for name, cell in module["cells"].items():
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] in ("output", "inout"):
                for bit in bits:
                    drivers.setdefault(bit, []).append((name, pin))
    return drivers


def owner_of(drivers, bit, where):
    """The single (cell, port) that drives a net bit."""
    owners = drivers.get(bit, [])
    require(len(owners) == 1, f"{where}: expected one driver, found {len(owners)}")
    return owners[0]


def input_bits(cell, pin):
    require(cell["port_directions"][pin] == "input", f"{pin}: not an input port")
    return cell["connections"][pin]


def input_buses(cell):
    """The input ports of a cell as a list of bit tuples (A and B, not Y)."""
    return [tuple(cell["connections"][pin]) for pin in cell["connections"]
            if cell["port_directions"][pin] == "input"]


class MemCone(DffCone):
    """A `DffCone` that also decodes the pointer's part-select arithmetic.

    Extra cell shapes: `$mul` with one constant operand (the `8 * lane` part
    select), `$shl`/`$shr` with a symbolic amount (the one-hot byte lane), and
    the reduction forms `$reduce_or`/`$reduce_bool`/`$logic_not` that Yosys uses
    for `|s_req`, `rq != 0` and `rq == 0`.  A contiguous slice of a *driven* bus
    is read as one shifted truncation instead of one bit at a time, and a
    concatenation is assembled field by field so the emitted term keeps the
    shape of the specification's `++`.  Every extension stays fail-closed: an
    unsupported cell, an unresolvable bus, a second driver or a partially
    overlapping slice raises `UnsupportedRTL`.
    """

    EXTRA = ("$mul", "$shl", "$shr", "$reduce_or", "$reduce_bool", "$logic_not")

    def __init__(self, name, module):
        super().__init__(name, module)
        self.used = set()
        for cell_name, cell in module["cells"].items():
            kind = cell["type"]
            if kind not in self.EXTRA:
                continue
            pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
            where = f"{name}.{cell_name} ({kind})"
            if kind == "$mul":
                require(len(pins) == 3, f"{where}: unexpected multiply ports")
                a, b = pins["A"], pins["B"]
                require(is_constant(a) != is_constant(b),
                        f"{where}: expected a constant lane multiply")
                factor = constant_value(a if is_constant(a) else b, where)
                require(factor in (2, 3, 4, 5, 8, 12, 16),
                        f"{where}: constant {factor} is not a lane multiply")
            elif kind in ("$shl", "$shr"):
                require(len(pins) == 3, f"{where}: unexpected shift ports")
                require(len(pins["B"]) <= 5, f"{where}: unexpected shift amount bus")
                require(int(cell["parameters"]["B_SIGNED"], 2) == 0 or
                        self._bound(pins["B"]) < 2 ** 31,
                        f"{where}: signed shift amount could be negative")
            elif kind in ("$reduce_or", "$reduce_bool"):
                require(len(pins["Y"]) == 1 and len(pins["A"]) ==
                        int(cell["parameters"]["A_WIDTH"], 2),
                        f"{where}: expected one scalar reduction")
            else:
                require(set(pins) == {"A", "Y"} and len(pins["Y"]) == 1 and
                        len(pins["A"]) == int(cell["parameters"]["A_WIDTH"], 2),
                        f"{where}: expected one scalar result")
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = (kind, pins, cell["parameters"], where)

    def _bound(self, bits):
        """A conservative upper bound of the unsigned value of a bus."""
        if is_constant(bits):
            return constant_value(bits, "bound")
        driver = self.drivers.get(bits)
        if driver is not None:
            kind, pins, params, _ = driver
            if kind == "$mul" and is_constant(pins["A"]) != is_constant(pins["B"]):
                if is_constant(pins["A"]):
                    factor, other = constant_value(pins["A"], "bound"), pins["B"]
                else:
                    factor, other = constant_value(pins["B"], "bound"), pins["A"]
                bound = factor * self._bound(other)
                if bound < 2 ** len(bits):
                    return bound
        return 2 ** len(bits) - 1

    def expression(self, bits):
        driver = self.drivers.get(bits)
        if driver is not None:
            self.used.add(driver[3].split(f"{self.name}.", 1)[-1].split(" (")[0])
        if driver is not None and driver[0] in self.EXTRA + ("$shiftx",):
            return self._special(bits, driver)
        if driver is not None and driver[0] == "$add" and self._zero_add(driver[1]):
            return self._special(bits, driver)
        if (bits not in self.bound and bits not in self.drivers and
                not is_constant(bits) and len(bits) > 1):
            sliced = self._slice_of_driver(bits)
            if sliced is not None:
                return sliced
        return super().expression(bits)

    def _zero_add(self, pins):
        """Whether a `$add` adds a constant zero (Yosys's `x + 0` for a select)."""
        for pin in ("A", "B"):
            bits = pins.get(pin)
            if bits is not None and is_constant(bits) and constant_value(bits, pin) == 0:
                return True
        return False

    def _slice_of_driver(self, bits):
        """Read a contiguous slice of a driven bus as one shifted truncation."""
        candidates = []
        for key in self.drivers:
            if len(key) <= len(bits):
                continue
            for offset in range(len(key) - len(bits) + 1):
                if key[offset:offset + len(bits)] == bits:
                    candidates.append((key, offset))
        if not candidates:
            return None
        require(len(candidates) == 1,
                f"{self.name}: ambiguous slice of a driven bus {bits}")
        key, offset = candidates[0]
        whole = self.expression(key)
        return (f"(BitVec.truncate {len(bits)} "
                f"(BitVec.ushiftRight {whole} {offset}))")

    def _special(self, bits, driver):
        kind, pins, params, where = driver
        if kind in ("$reduce_or", "$reduce_bool"):
            require(len(bits) == 1, f"{where}: unexpected result bus")
            expr = f"({self.expression(pins['A'])} != 0)"
        elif kind == "$logic_not":
            width = int(params["A_WIDTH"], 2)
            require(len(bits) == 1 and width > 0, f"{where}: unexpected result bus")
            expr = f"({self.expression(pins['A'])} == (0 : BitVec {width}))"
        elif kind == "$mul":
            width = int(params["Y_WIDTH"], 2)
            require(len(bits) == width, f"{where}: unexpected result bus")
            a, b = pins["A"], pins["B"]
            require(is_constant(a) != is_constant(b),
                    f"{where}: expected a constant lane multiply")
            if is_constant(a):
                factor, other = constant_value(a, where), b
            else:
                factor, other = constant_value(b, where), a
            require(factor in (2, 3, 4, 5, 8, 12, 16),
                    f"{where}: constant {factor} is not a lane multiply")
            expr = f"(mulC {factor} (BitVec.setWidth {width} {self.expression(other)}))"
        elif kind in ("$shl", "$shr"):
            width = int(params["Y_WIDTH"], 2)
            require(len(bits) == width and len(pins["A"]) ==
                    int(params["A_WIDTH"], 2), f"{where}: unexpected result bus")
            operator = "BitVec.shiftLeft" if kind == "$shl" else "BitVec.ushiftRight"
            expr = (f"({operator} {self.expression(pins['A'])} "
                    f"({self.expression(pins['B'])}).toNat)")
        elif kind == "$add":
            width = int(params["Y_WIDTH"], 2)
            require(len(bits) == width, f"{where}: unexpected result bus")
            keep = None
            for pin, other in (("B", "A"), ("A", "B")):
                if (is_constant(pins[pin]) and
                        constant_value(pins[pin], where) == 0):
                    keep = pins[other]
            require(keep is not None and len(keep) == width,
                    f"{where}: expected a zero addend of the result width")
            return self.expression(keep)
        else:  # $shiftx
            width = int(params["Y_WIDTH"], 2)
            source = int(params["A_WIDTH"], 2)
            require(len(bits) == width and 0 < width <= source,
                    f"{where}: unexpected result bus")
            shifted = (f"(BitVec.ushiftRight {self.expression(pins['A'])} "
                       f"({self.expression(pins['B'])}).toNat)")
            expr = (f"(({shifted} &&& (1 : BitVec {source})) != 0)" if width == 1
                    else f"(BitVec.truncate {width} {shifted})")
        wire = f"{self.name}{len(self.lines)}"
        self.lines.append(f"  let {wire} := {expr}")
        self.bound[bits] = wire
        return wire

    def _assemble(self, bits):
        """Assemble a concatenation field by field, one shift per run of bits."""
        fields = [self._field_of(bit) for bit in bits]
        runs = []
        for index, field in enumerate(fields):
            if runs and self._continues(runs[-1][3], field):
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
                value = self.expression(key)
                pieces.append(
                    f"(BitVec.truncate {count} (BitVec.ushiftRight {value} {offset}))")
        expr = pieces[0]
        for piece in pieces[1:]:
            expr = f"({expr} ++ {piece})"
        return expr

    def _field_of(self, bit):
        if bit in ("0", "1", "x"):
            return ("const", "0" if bit == "x" else bit, 0)
        slot = self.bound.get((bit,))
        if slot is not None:
            return ("bool", slot, 0)
        best = None
        for key in self.bound:
            if len(key) > 1 and bit in key and (best is None or len(key) > len(best[0])):
                best = (key, key.index(bit))
        if best is not None:
            return ("bus", best[0], best[1])
        for key in self.drivers:
            if len(key) > 1 and bit in key and (best is None or len(key) > len(best[0])):
                best = (key, key.index(bit))
        if best is not None:
            return ("bus", best[0], best[1])
        return ("bool", self._bit_bool(bit), 0)

    @staticmethod
    def _continues(previous, field):
        if previous[0] != field[0]:
            return False
        if previous[0] == "const":
            return previous[1] == field[1]
        if previous[0] == "bool":
            return False
        return previous[1] == field[1] and previous[2] + 1 == field[2]


def elaborate(snapshot, work, yosys):
    """Elaborate a source snapshot with the shared recipe and the SRAM macro."""
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
        raise MemRejected(f"Yosys elaboration failed: {result.stdout.strip()}")
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


def check_mem_top(modules):
    """Check the arbiter instance, its host slot and its RAM port at the top."""
    check_host_top(modules)
    top = modules[TOP]
    require(MEM_CELL in top["cells"], f"{TOP}.{MEM_CELL}: missing arbiter instance")
    cell = top["cells"][MEM_CELL]
    require(cell["type"] in modules and
            (cell["type"] == MEM_MODULE or
             modules[cell["type"]]["attributes"].get("hdlname") == MEM_MODULE),
            f"{MEM_CELL}: unexpected arbiter module")
    conn = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
    require(conn["clk"] == tuple(top["ports"]["clk"]["bits"]),
            f"{MEM_CELL}: unexpected clock")
    require(conn["rst_n"] == tuple(top["netnames"]["rst_q"]["bits"]),
            f"{MEM_CELL}: unexpected reset (expected rst_q)")
    for port, width, net in NET_PORTS:
        require(net in top["netnames"], f"{TOP}.{net}: missing net")
        bits = tuple(top["netnames"][net]["bits"])
        require(len(bits) == width and conn[port] == bits,
                f"{MEM_CELL}.{port}: unexpected connection")

    # The S0 edge-capture record and the pointer's move bundle.
    s_word = tuple(top["netnames"]["s_word"]["bits"])
    require(conn["s0_word"] == (s_word[0],), f"{MEM_CELL}.s0_word: unexpected net")
    s_ww = tuple(top["netnames"]["s_ww"]["bits"])
    require(conn["s0_wword"] == s_ww[:32], f"{MEM_CELL}.s0_wword: unexpected net")
    w_p0 = tuple(top["netnames"]["w_p0"]["bits"])
    require(conn["p_we"] == (w_p0[14],), f"{MEM_CELL}.p_we: unexpected net")
    require(conn["p_d"] == w_p0[:8], f"{MEM_CELL}.p_d: unexpected net")
    a_dat = tuple(top["netnames"]["a_dat"]["bits"])
    require(conn["h_addr"] == a_dat[:11], f"{MEM_CELL}.h_addr: unexpected net")

    # The host request strobe is exactly `(h_wr | h_rd) & in_data`.
    drivers = drivers_of(top)
    require(len(conn["h_set"]) == 1, f"{MEM_CELL}.h_set: expected one bit")
    owner = owner_of(drivers, conn["h_set"][0], f"{MEM_CELL}.h_set")
    and_cell = top["cells"][owner[0]]
    require(owner[1] == "Y" and and_cell["type"] in ("$and", "$logic_and"),
            f"{MEM_CELL}.h_set: not an AND of the host strobe with in_data")
    inputs = input_buses(and_cell)
    in_data = tuple(top["netnames"]["in_data"]["bits"])
    require(len(inputs) == 2 and in_data in inputs,
            f"{MEM_CELL}.h_set: not masked by in_data")
    other = [bits for bits in inputs if bits != in_data][0]
    require(len(other) == 1, f"{MEM_CELL}.h_set: unexpected operand width")
    or_owner = owner_of(drivers, other[0], f"{MEM_CELL}.h_set")
    or_cell = top["cells"][or_owner[0]]
    require(or_owner[1] == "Y" and or_cell["type"] in ("$or", "$logic_or"),
            f"{MEM_CELL}.h_set: host strobe is not h_wr | h_rd")
    or_inputs = set(input_buses(or_cell))
    require(or_inputs == {tuple(top["netnames"]["h_wr"]["bits"]),
                          tuple(top["netnames"]["h_rd"]["bits"])},
            f"{MEM_CELL}.h_set: host strobe is not h_wr | h_rd")

    # The landing nets are the ones the host read cut consumes.
    host = top["cells"][HOST_CELL]
    require(tuple(host["connections"]["hland"]) == conn["h_land"],
            "u_host.hland is not the arbiter's h_land")
    require(tuple(host["connections"]["hland_d"]) == conn["h_land_d"],
            "u_host.hland_d is not the arbiter's h_land_d")
    require(tuple(host["connections"]["rd_data"]) == in_data,
            "u_host.rd_data is not in_data")
    require(tuple(host["connections"]["rd"]) == tuple(top["netnames"]["h_rd"]["bits"]),
            "u_host.rd is not h_rd")

    # The RAM port is the data-RAM wrapper's port, and its read data comes back.
    require(DMEM_CELL in top["cells"], f"{TOP}.{DMEM_CELL}: missing data RAM")
    dmem = top["cells"][DMEM_CELL]
    dconn = {pin: tuple(bits) for pin, bits in dmem["connections"].items()}
    for port, memport in (("ren", "m_ren"), ("we", "m_we"), ("addr", "m_addr"),
                          ("be", "m_be"), ("wd", "m_wd"), ("rd", "m_rd")):
        require(dconn[port] == conn[memport],
                f"{MEM_CELL}.{memport} is not {DMEM_CELL}.{port}")
    return top


def check_dmem(modules):
    """Check the data-RAM wrapper's byte mask and its SRAM macro boundary."""
    top = modules[TOP]
    cell = top["cells"][DMEM_CELL]
    require(cell["type"] in modules and
            (cell["type"] == DMEM_MODULE or
             modules[cell["type"]]["attributes"].get("hdlname") == DMEM_MODULE),
            f"{DMEM_CELL}: unexpected data-RAM module")
    module = modules[cell["type"]]
    require(SRAM_CELL in module["cells"],
            f"{DMEM_MODULE}: no SRAM macro instance (elaborate with USE_IHP_SRAM)")
    sram = module["cells"][SRAM_CELL]
    require(sram["type"] == SRAM_MODULE,
            f"{DMEM_MODULE}.{SRAM_CELL}: unexpected macro {sram['type']}")
    conn = {pin: tuple(bits) for pin, bits in sram["connections"].items()}
    ports = module["ports"]
    for macro, port in (("A_CLK", "clk"), ("A_ADDR", "addr"), ("A_DIN", "wd"),
                        ("A_DOUT", "rd"), ("A_WEN", "we")):
        require(conn[macro] == tuple(ports[port]["bits"]),
                f"{SRAM_CELL}.{macro} is not {DMEM_MODULE}.{port}")
    require(conn["A_DLY"] == ("1",), f"{SRAM_CELL}.A_DLY: expected 1")
    for name in ("A_BIST_CLK", "A_BIST_EN", "A_BIST_MEN", "A_BIST_WEN",
                 "A_BIST_REN", "A_BIST_ADDR", "A_BIST_DIN", "A_BIST_BM"):
        require(all(bit == "0" for bit in conn[name]), f"{SRAM_CELL}.{name}: not tied off")

    # A_MEN = ren | we and A_REN = ren & ~we.
    drivers = drivers_of(module)
    ren = tuple(ports["ren"]["bits"])
    we = tuple(ports["we"]["bits"])
    require(len(ren) == 1 and len(we) == 1, "md2_dmem: expected scalar strobes")
    owner = owner_of(drivers, conn["A_MEN"][0], f"{SRAM_CELL}.A_MEN")
    require(owner[1] == "Y", f"{SRAM_CELL}.A_MEN: undriven")
    men = module["cells"][owner[0]]
    require(men["type"] in ("$or", "$logic_or"),
            f"{SRAM_CELL}.A_MEN: not ren | we")
    require(set(input_buses(men)) == {ren, we},
            f"{SRAM_CELL}.A_MEN: not ren | we")
    owner = owner_of(drivers, conn["A_REN"][0], f"{SRAM_CELL}.A_REN")
    require(owner[1] == "Y", f"{SRAM_CELL}.A_REN: undriven")
    ren_cell = module["cells"][owner[0]]
    require(ren_cell["type"] in ("$and", "$logic_and"),
            f"{SRAM_CELL}.A_REN: not ren & ~we")
    operands = input_buses(ren_cell)
    require(len(operands) == 2 and ren in operands,
            f"{SRAM_CELL}.A_REN: not ren & ~we")
    inverted = [bits for bits in operands if bits != ren][0]
    require(len(inverted) == 1, f"{SRAM_CELL}.A_REN: unexpected operand width")
    owner = owner_of(drivers, inverted[0], f"{SRAM_CELL}.A_REN")
    require(owner[1] == "Y",
            f"{SRAM_CELL}.A_REN: the second operand is not we inverted")
    not_cell = module["cells"][owner[0]]
    require(not_cell["type"] == "$not" and
            tuple(input_bits(not_cell, "A")) == we,
            f"{SRAM_CELL}.A_REN: the second operand is not we inverted")

    # The byte mask: lane k of A_BM is `be[k]` repeated eight times (`bm`).
    be = tuple(ports["be"]["bits"])
    require(len(be) == 4 and len(conn["A_BM"]) == 32,
            f"{SRAM_CELL}.A_BM: expected 32 bits for a 4-lane mask")
    for lane in range(4):
        for index in range(8):
            require(conn["A_BM"][8 * lane + index] == be[lane],
                    f"{SRAM_CELL}.A_BM: bit {8 * lane + index} is not be[{lane}]")
    return module


def extract_mem(module):
    """Extract the arbiter's next state and outputs from the elaborated module."""
    cone = MemCone("mem", module)
    for name, width, value in INPUTS:
        cone.input(name, width, value)
    next_bits = {}
    for name, width, current, _field in REGISTERS:
        next_bits[name] = cone.register(name, width, current)
    fields = {name: cone.expression(bits) for name, bits in next_bits.items()}
    step_lets = "\n".join(cone.lines)

    out_cone = MemCone("mem_out", module)
    for name, width, value in INPUTS:
        out_cone.input(name, width, value)
    for name, width, current, _field in REGISTERS:
        out_cone.register(name, width, current)
    drivers = {}
    for pin, bits in module["ports"].items():
        if bits["direction"] == "output":
            drivers[pin] = tuple(bits["bits"])
    outs = {}
    for port, width, field in OUTPUTS:
        bits = drivers.get(port)
        if bits is None:
            bits = tuple(module["netnames"][port]["bits"])
        require(len(bits) == width, f"{MEM_MODULE}.{port}: expected {width} bits")
        outs[field] = out_cone.expression(bits)
    out_lets = "\n".join(out_cone.lines)
    return {
        "step_lets": step_lets,
        "fields": fields,
        "out_lets": out_lets,
        "outs": outs,
        "gates": len(cone.lines) + len(out_cone.lines),
        "cells": len(cone.used | out_cone.used),
    }


def lean_mem(info, fingerprint):
    """Emit the extracted transition and outputs as Lean definitions."""
    fields = info["fields"]
    outs = info["outs"]
    step = ",\n    ".join(f"{field} := {fields[name]}"
                          for name, _, _, field in REGISTERS)
    output = ",\n    ".join(
        [f"{field} := {outs[field]}" for _, _, field in OUTPUTS] +
        ["pRdy := state.rdy", "pDat := state.dat", "hLand := state.hLand"])
    return f"""import Metronome.Mem

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {fingerprint}
-- Arbiter: the `{MEM_MODULE}` instance `{TOP}.{MEM_CELL}`; the data RAM is the
-- black-box macro behind `{TOP}.{DMEM_CELL}`.  The fifteen registers are sampled
-- as `state`, the seventeen inputs as `input`, and the SRAM word as
-- `input.ramWord`.  {info['cells']} RTL cells, {info['gates']} emitted terms.

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Metronome.Mem

/-- The elaborated arbiter transition. -/
def rtlStep (state : State) (input : Input) : State :=
{info['step_lets']}
  {{ {step} }}

/-- The elaborated arbiter outputs (`s_gnt`, the RAM port, the hazard event and
the host landing byte); `p_rdy`, `p_dat` and `h_land` are state. -/
def rtlOuts (state : State) (input : Input) : Outs :=
{info['out_lets']}
  {{ {output} }}

"""


def failing_declaration(source, message):
    """The declaration whose proof the first Lean error belongs to."""
    match = ERROR_LINE.search(message)
    if match is None:
        return None
    line = int(match.group(1))
    lines = source.splitlines()
    for index in range(min(line, len(lines)) - 1, -1, -1):
        found = DECLARATION.match(lines[index])
        if found:
            return found.group(1)
    return None


def axiom_audit(text):
    """Collect the `#print axioms` records from a Lean run."""
    return {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
            for name, axioms in AXIOM_LINE.findall(text)}


def run_lean_mem(source, filename, artifact, lake, work, evidence):
    """Run the generated proof, keeping the source and its log.

    A Lean process that dies without any diagnostic (a negative exit code, seen
    under machine load) is retried once, so a transient crash is not reported as
    a proof failure.  The wall time of every attempt is recorded.
    """
    path = Path(work) / filename
    path.write_text(source, encoding="utf-8")
    if evidence:
        (Path(evidence) / artifact).write_text(source, encoding="utf-8")
    notes = []
    elapsed = []
    for attempt in range(2):
        started = time.monotonic()
        try:
            result = run([lake, "env", "lean", "-j1", "-DwarningAsError=true", str(path)],
                         HERE, timeout=LEAN_TIMEOUT)
        except subprocess.TimeoutExpired:
            raise MemRejected(f"{artifact}: Lean timed out after {LEAN_TIMEOUT} s",
                              code=-1)
        elapsed.append(time.monotonic() - started)
        notes.append(f"lean attempt {attempt + 1}: exit {result.returncode} "
                     f"after {elapsed[-1]:.1f} s\n")
        if result.returncode == 0 or "error" in result.stdout:
            break
    result.stdout = "".join(notes) + result.stdout
    result.wall = round(sum(elapsed), 1)
    return result


def check_mem(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the elaborated data-RAM arbiter and its generated Lean proofs.

    `rtlil_or_json` is a parsed Yosys design, a path to `design.json`, or a
    Verilog source directory to elaborate.  A JSON design must have been
    produced with `-D USE_IHP_SRAM` (the macro instance is part of the dmem
    check).  Evidence is written to `out_dir` as `<case>.mem.lean`,
    `<case>.log` and `<case>.axioms.txt`.  Returns a result dictionary; a
    rejected cut raises `MemRejected` (proof or audit) or `UnsupportedRTL`
    (structure or wiring).
    """
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-mem-{case}-") as tmp:
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
            check_mem_top(modules)
            check_dmem(modules)
            module = modules[modules[TOP]["cells"][MEM_CELL]["type"]]
            info = extract_mem(module)
            log.append(f"Arbiter cut: 15 registers, {len(OUTPUTS) + 3} outputs, "
                       f"{info['cells']} RTL cells, {info['gates']} emitted terms\n")
            source = lean_mem(info, fingerprint)
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the structural arbiter check: {exc}\n")
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise
        source += TEMPLATE.read_text(encoding="utf-8")
        result = run_lean_mem(source, "MemProof.lean", f"{case}.mem.lean",
                              lake, work, out_dir)
        log.append(result.stdout)
        axioms = axiom_audit(result.stdout)
        theorem = None
        if result.returncode != 0:
            theorem = failing_declaration(source, result.stdout)
            outcome = f"rejected by Lean (exit {result.returncode})"
            log.append(f"-- {case}: {outcome}\n")
        elif "sorryAx" in result.stdout or any(
                "sorryAx" in found for found in axioms.values()):
            outcome = "rejected: the proof used sorryAx"
            log.append(f"-- {case}: {outcome}\n")
        else:
            outcome = "accepted"
            log.append(f"-- {case}: {outcome} in {result.wall} s\n")
        detail = ""
        if theorem:
            first = next((line.strip() for line in result.stdout.splitlines()
                          if "error:" in line), outcome)
            detail = f"{theorem}: {first.split('error:', 1)[-1].strip()[:120]}"
        (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
        (out_dir / f"{case}.axioms.txt").write_text(
            "".join(f"{name}: {', '.join(found)}\n" for name, found in axioms.items()),
            encoding="utf-8")
        report = {
            "case": case,
            "ok": outcome == "accepted",
            "outcome": outcome,
            "exit": result.returncode,
            "theorem": theorem,
            "seconds": result.wall,
            "cells": info["cells"],
            "gates": info["gates"],
            "fingerprint": fingerprint,
            "source": out_dir / f"{case}.mem.lean",
            "log": out_dir / f"{case}.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            raise MemRejected(f"{case}: {outcome}\n" + "".join(log),
                              reason=detail or outcome,
                              code=result.returncode, theorem=theorem)
    return report


def replace(*pairs):
    """A snapshot transformer replacing anchored text in the named sources."""
    def apply(snapshot):
        changed = dict(snapshot)
        for name, before, after in pairs:
            require(name in changed, f"mutation: missing {name}")
            data = changed[name]
            require(data.count(before.encode()) == 1,
                    f"mutation: anchor changed in {name}: {before}")
            changed[name] = data.replace(before.encode(), after.encode(), 1)
        return changed
    return apply


def mem_mutations():
    """The planted arbiter regressions, as snapshot transformers."""
    return [
        # P0 is served while S1 requests: `gp` drops the stream-idle condition
        # and S1 is gated off by it, so a two-requester cycle serves P0 and the
        # grant vector loses the S1 grant.
        ("mem_p0_over_s1", replace(
            ("md2_mem.v",
             "wire gs1 = ~s_req[0] & s_req[1] & ~frz;",
             "wire gs1 = ~s_req[0] & s_req[1] & ~frz & ~gp;"),
            ("md2_mem.v",
             "wire gp  = ~(|s_req) & (rq != RQ_NONE) & ~frz;",
             "wire gp  = (rq != RQ_NONE) & ~frz;"))),
        # The host is served whenever it asks, ahead of every stream and the
        # pointer (a priority swap).
        ("mem_host_first", replace(
            ("md2_mem.v",
             "wire gh  = (frz | (~(|s_req) & (rq == RQ_NONE))) & hq;",
             "wire gh  = hq;"))),
        # The host landing takes the wrong byte lane.
        ("mem_host_lane", replace(
            ("md2_mem.v", "hlane  <= hqa[1:0];", "hlane  <= hqa[2:1];"))),
        # A new host request does not overwrite an unserved one.
        ("mem_host_no_overwrite", replace(
            ("md2_mem.v", "if (h_set) begin", "if (h_set & ~hq) begin"))),
        # P0 raises RDY in the cycle its fetch is served instead of one cycle
        # later, from the landing.
        ("mem_p0_rdy_early", replace(
            ("md2_mem.v",
             "else if (land & lok & ~frz) p_rdy <= 1'b1;",
             "else if (gp & lok & ~frz) p_rdy <= 1'b1;"))),
        # The pointer wraps at 1,024 bytes, not 2,048.
        ("mem_ptr_wrap_1024", replace(
            ("md2_mem.v",
             "else if (op_w | op_r) ptr <= ptr + 11'd1;",
             "else if (op_w | op_r) ptr <= {1'b0, ptr[9:0] + 10'd1};"))),
        # The S0 edge-capture write loses its all-lane byte mask.
        ("mem_s0_word_be", replace(
            ("md2_mem.v",
             "assign m_be   = gw ? 4'hF : (4'd1 << a[1:0]);",
             "assign m_be   = 4'hF & (4'd1 << a[1:0]);"))),
        # The data-RAM wrapper replicates the wrong byte lane into the mask.
        ("mem_dmem_lane", replace(
            ("md2_dmem.v",
             "wire [31:0] bm = {{8{be[3]}}, {8{be[2]}}, {8{be[1]}}, {8{be[0]}}};",
             "wire [31:0] bm = {{8{be[3]}}, {8{be[2]}}, {8{be[0]}}, {8{be[1]}}};"))),
    ]


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted arbiter regression is rejected.

    Returns one `(case, rejected, stage, exit)` record per mutation and raises
    `MemRejected` if any mutant is accepted.
    """
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-mem-mutants-") as tmp:
        for case, transform in mem_mutations():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_mem(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"structural check: {exc}", 0))
                continue
            except MemRejected as exc:
                stage = f"generated Lean: {exc.theorem}" if exc.theorem else \
                    f"generated Lean: {exc.reason}"
                records.append((case, True, stage, exc.code))
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
                        help="also check the planted arbiter regressions")
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
            raise MemRejected("tool version query failed")

        build = run([lake, "build", "Metronome.Mem"], HERE)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise MemRejected("lake build Metronome.Mem failed")

        snapshot = snapshot_of(ROOT / "src")
        report = check_mem(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        emit(f"baseline: {report['outcome']} ({report['cells']} RTL cells, "
             f"{report['gates']} emitted terms, {report['seconds']} s)")
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
        raise SystemExit(f"Memory check failed: {exc}") from exc
