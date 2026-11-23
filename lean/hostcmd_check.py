"""Check the host SPI command-machine cut of the Metronome chip top.

The shared suite (`verify.py`) covers the host write strobe `wr` and the bit
counter `bitc` of `src/md2_host.v`, but it binds the byte state `st` and the
command latch `is_rd` as free per-cycle inputs.  This module discharges them.
It re-elaborates the chip top with the same Yosys recipe as `verify.py`,
extracts the next state of `st`, `is_rd`, the 16-bit address register `addr`,
the data register `wdata`, the read request `rd` and the read-acknowledge flag
`rack` from the elaborated `md2_host` instance, and emits Lean that proves the
extracted transition equal to `Metronome.HostCmd`'s independent specification
of the SPEC_V2 section 9 command machine (component by component, with
`bv_decide`).

`Metronome.HostCmd` additionally carries `cmd`, a history variable that records
the byte completed in the command state.  `md2_host.v` does not register it: the
RTL keeps only `is_rd`.  The generated Lean defines it from the RTL's own
command-completion nets, and `extract_host` refuses the design unless every gate
in its cone also feeds the RTL `st` or `is_rd` next-state logic, so the
definition cannot introduce logic the RTL does not have.

Run it from the repository root:

    python lean/hostcmd_check.py
    python lean/hostcmd_check.py --mutations

`run_mutations()` plants the required regressions on temporary copies of `src/`
(never the repository): a read data byte that also strobes a write, an `ST_AL`
next state that skips `ST_DATA`, a `CS_N`-high branch that keeps the byte state,
a write that does not step the address, and swapped address bytes.  Every one
must be rejected.
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
from verify import HERE, ROOT, TOP, check_host_top, run, run_lean


HOST_CELL = "u_host"
HOST_MODULE = "md2_host"
DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_hostcmd_v4_20261120"
TEMPLATE = HERE / "HostCmdEquivalence.lean.in"
AXIOM_LINE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)

# The specification definitions the generated transition must be unfolded
# against; `Metronome.HostCmd.step` is the record of the same equations.
SIMP_LEMMAS = ("rtlStep, step, phaseNext, bitcNext, rxNext, isRdNext, addrNext, "
               "wrNext, wdataNext, rdNext, rackNext, cmdNext, completing, sr, "
               "byteIn, ackBit, addrInc")


class HostCmdRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated host cut."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


class HostCone(DffCone):
    """A `DffCone` that also decodes Yosys's `$logic_not` and `$pmux` cells.

    `$logic_not` is how Yosys lowers a bus-equals-zero test (`st == ST_CMD`), and
    `$pmux` is the priority mux of a `case` statement.  The extra shapes are
    decoded here rather than in `rtlil.py` because the shared adapter is used by
    every other cut.  Both stay fail-closed: `$logic_not` must be one scalar
    result of a bus, and every `$pmux` select must be an equality or zero test of
    one common bus against distinct constants, which makes the select bits
    mutually exclusive and the branch order irrelevant.  Anything else fails.
    """

    def __init__(self, name, module):
        super().__init__(name, module)
        for cell_name, cell in module["cells"].items():
            kind = cell["type"]
            if kind not in ("$logic_not", "$pmux"):
                continue
            pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
            where = f"{name}.{cell_name} ({kind})"
            if kind == "$logic_not":
                require(set(pins) == {"A", "Y"} and len(pins["Y"]) == 1,
                        f"{where}: expected one scalar result")
                require(len(pins["A"]) == int(cell["parameters"]["A_WIDTH"], 2) and
                        int(cell["parameters"]["Y_WIDTH"], 2) == 1,
                        f"{where}: unexpected widths")
            else:
                width = int(cell["parameters"]["WIDTH"], 2)
                selects = int(cell["parameters"]["S_WIDTH"], 2)
                require(len(pins["Y"]) == width and len(pins["A"]) == width and
                        len(pins["B"]) == width * selects and len(pins["S"]) == selects,
                        f"{where}: unexpected pmux widths")
                pmux_selects_exclusive(module, pins["S"], where)
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = (kind, pins, cell["parameters"], where)

    def alias(self, name, width, value):
        """Bind a named net to an expression built from already-bound nets.

        The net is checked against the design's bit layout by the caller, so this
        is a checked modelling step rather than an assumption: `byte_in` is the
        RTL's `{rx, mosi}` wire, and the caller requires exactly that bit order
        before aliasing it to the specification's `byteIn`.
        """
        net = self.module["netnames"].get(name)
        require(net is not None, f"{self.name}.{name}: missing net")
        bits = tuple(net["bits"])
        require(len(bits) == width, f"{self.name}.{name}: expected {width} bits")
        require(bits not in self.bound, f"{self.name}.{name}: already bound")
        require(bits not in self.drivers, f"{self.name}.{name}: is a cell output")
        self.bound[bits] = value
        return bits

    def expression(self, bits):
        driver = self.drivers.get(bits)
        if driver is not None and driver[0] == "$logic_not":
            _, pins, params, where = driver
            source_width = int(params["A_WIDTH"], 2)
            require(len(bits) == 1 and source_width > 0, f"{where}: unexpected result bus")
            source = self.expression(pins["A"])
            expr = f"({source} == (0 : BitVec {source_width}))"
            wire = f"{self.name}{len(self.lines)}"
            self.lines.append(f"  let {wire} := {expr}")
            self.bound[bits] = wire
            return wire
        if driver is not None and driver[0] == "$pmux":
            _, pins, params, where = driver
            width = int(params["WIDTH"], 2)
            selects = int(params["S_WIDTH"], 2)
            require(len(bits) == width, f"{where}: unexpected result bus")
            expr = self.expression(pins["A"])
            # Higher select indices are applied first so that the lowest set
            # select wins, as a Verilog `case` does.
            for index in reversed(range(selects)):
                branch = self.expression(tuple(pins["B"][index * width:(index + 1) * width]))
                expr = f"(if {self._bit_bool(pins['S'][index])} then {branch} else {expr})"
            wire = f"{self.name}{len(self.lines)}"
            self.lines.append(f"  let {wire} := {expr}")
            self.bound[bits] = wire
            return wire
        return super().expression(bits)


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
        raise HostCmdRejected(f"Yosys elaboration failed: {result.stdout.strip()}")
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
    require(net is not None, f"{HOST_MODULE}.{name}: missing net")
    require("init" not in net["attributes"], f"{HOST_MODULE}.{name}: unexpected initial value")
    bits = tuple(net["bits"])
    require(len(bits) == width, f"{HOST_MODULE}.{name}: expected {width} bits")
    return bits


def register_data(module, name, width):
    """The D-input bus of the one register driving the named net."""
    bits = net_bits(module, name, width)
    matches = [cell for cell in module["cells"].values()
               if cell["type"] in ("$dff", "$adff") and
               tuple(cell["connections"]["Q"]) == bits]
    require(len(matches) == 1,
            f"md2_host.{name}: expected exactly one register driver")
    return tuple(matches[0]["connections"]["D"])


def rtl_cone_cells(module, seeds):
    """Names of the combinational cells reachable backwards from a set of bits.

    Registers are leaves: their `Q` bits are state, so this follows the same
    boundary as the extraction, where register outputs are bound as inputs.
    """
    drivers = {}
    for name, cell in module["cells"].items():
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] in ("output", "inout"):
                for bit in bits:
                    drivers[bit] = name
    cells = set()
    visited = set()
    stack = list(seeds)
    while stack:
        bit = stack.pop()
        if bit in ("0", "1") or bit in visited:
            continue
        visited.add(bit)
        cell_name = drivers.get(bit)
        if cell_name is None:
            continue
        if cell_name in cells:
            continue
        cell = module["cells"][cell_name]
        if cell["type"] in ("$dff", "$adff"):
            continue
        cells.add(cell_name)
        for pin, bits in cell["connections"].items():
            if cell["port_directions"][pin] == "input":
                stack.extend(bits)
    return cells


def find_compare(module, kind, operand, value=None):
    """The unique `kind` cell comparing `operand` with `value`."""
    matches = []
    for name, cell in module["cells"].items():
        if cell["type"] != kind:
            continue
        pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
        if pins.get("A") != tuple(operand) or len(pins.get("Y", ())) != 1:
            continue
        if value is not None and tuple(pins.get("B", ())) != tuple(value):
            continue
        matches.append(name)
    require(matches, f"md2_host: no {kind} of the command-machine operand")
    return module["cells"][matches[0]]["connections"]["Y"][0]


def host_module(modules):
    """The specialized `md2_host` module the chip top instantiates."""
    top = modules[TOP]
    require(HOST_CELL in top["cells"], f"{TOP}.{HOST_CELL}: missing host instance")
    cell = top["cells"][HOST_CELL]
    require(cell["type"] in modules, f"{HOST_CELL}: missing specialized module")
    module = modules[cell["type"]]
    require(cell["type"] == HOST_MODULE or
            module["attributes"].get("hdlname") == HOST_MODULE,
            f"{HOST_CELL}: unexpected host module")
    require(tuple(cell["connections"]["clk"]) == tuple(top["ports"]["clk"]["bits"]),
            f"{HOST_CELL}: unexpected clock")
    require(tuple(cell["connections"]["rst_n"]) == tuple(top["netnames"]["rst_q"]["bits"]),
            f"{HOST_CELL}: unexpected reset")
    return module


def extract_host(module):
    """Extract the command-machine next state from the elaborated host module.

    Returns the Lean let-chain, the ten next-state field expressions, and the
    layout facts the adapter relied on.  Extraction is fail-closed: an
    unsupported cell, a register in a combinational cone, an unresolvable bus or
    a wiring that does not match the checked layout raises `UnsupportedRTL`.
    """
    st = net_bits(module, "st", 3)
    bitc = net_bits(module, "bitc", 3)
    rx = net_bits(module, "rx", 7)
    is_rd = net_bits(module, "is_rd", 1)
    addr = net_bits(module, "addr", 16)
    wr = net_bits(module, "wr", 1)
    wdata = net_bits(module, "wdata", 8)
    rd = net_bits(module, "rd", 1)
    rack = net_bits(module, "rack", 1)
    byte_in = net_bits(module, "byte_in", 8)
    mosi = module["ports"]["mosi"]["bits"]
    require(len(mosi) == 1, "md2_host.mosi: expected one bit")
    require(byte_in == (mosi[0],) + rx,
            "md2_host.byte_in is not {rx, mosi}")

    cone = HostCone("hostcmd", module)
    for name, width, value in (
        ("rst_n", 1, "input.resetN"),
        ("sck", 1, "input.sck"),
        ("sck_p", 1, "input.sckPrev"),
        ("cs_n", 1, "input.csN"),
        ("mosi", 1, "input.mosi"),
        ("rd_data", 1, "input.rdData"),
        ("hland", 1, "input.hland"),
    ):
        cone.input(name, width, value)
    next_bits = {}
    for name, width, current in (
        ("st", 3, "state.phase"),
        ("bitc", 3, "state.bitc"),
        ("rx", 7, "state.rx"),
        ("is_rd", 1, "state.isRd"),
        ("addr", 16, "state.addr"),
        ("wr", 1, "state.wr"),
        ("wdata", 8, "state.wdata"),
        ("rd", 1, "state.rd"),
        ("rack", 1, "state.rack"),
    ):
        next_bits[name] = cone.register(name, width, current)
    cone.alias("byte_in", 8, "(byteIn state input)")

    fields = {name: cone.expression(bits) for name, bits in next_bits.items()}

    # The `cmd` history variable: the byte completed in the command state.
    # `sr`, the `$ne` of `bitc` against 7 and the `$logic_not` of `st` (which
    # tests `st == ST_CMD`) are the RTL's own completion condition; the `$ne`
    # is negative, so the condition below negates it.
    sr_bit = net_bits(module, "sr", 1)[0]
    bitc_ne_seven = find_compare(module, "$ne", bitc, ("1", "1", "1"))
    st_is_cmd = find_compare(module, "$logic_not", st)
    ghost = (rtl_cone_cells(module, (sr_bit, bitc_ne_seven, st_is_cmd) + byte_in))
    # The history variable must draw only on gates that already feed the RTL
    # `st` or `is_rd` next-state logic.  The register *Q* buses are leaves of
    # this cut, so the allowed set starts from the two registers' D buses.
    allowed = (rtl_cone_cells(module, register_data(module, "st", 3)) |
               rtl_cone_cells(module, register_data(module, "is_rd", 1)))
    require(ghost <= allowed,
            "md2_host: the command-byte history variable would use gates outside "
            "the RTL st/is_rd cones")
    byte_in_expr = cone.expression(byte_in)
    fields["cmd"] = (
        f"(if !input.resetN then (0 : BitVec 8) else if input.csN then state.cmd "
        f"else if ({cone.expression((sr_bit,))} && !{cone.expression((bitc_ne_seven,))} "
        f"&& {cone.expression((st_is_cmd,))}) then {byte_in_expr} else state.cmd)")
    return {
        "lets": "\n".join(cone.lines),
        "fields": fields,
        "ghost_cells": len(ghost),
        "byte_in": byte_in,
        "registers": 9,
    }


def lean_hostcmd(info, fingerprint):
    """Emit the extracted transition as a Lean definition."""
    fields = info["fields"]
    return f"""import Metronome.HostCmd

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {fingerprint}
-- Host: the `{HOST_MODULE}` instance `{TOP}.{HOST_CELL}`.  Every register of the
-- command machine is sampled; `cmd` is the history variable for the byte
-- completed in `ST_CMD`, defined from the same nets as the RTL `st`/`is_rd`
-- ({info['ghost_cells']} gates, all of them in those two cones).

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Metronome.HostCmd

/-- The elaborated host-link transition.  `state.phase`, `state.bitc`, `state.rx`,
`state.isRd`, `state.addr`, `state.wr`, `state.wdata`, `state.rd` and
`state.rack` are the register values of this cycle. -/
def rtlStep (state : State) (input : Input) : State :=
{info['lets']}
  ⟨{fields['st']}, {fields['bitc']}, {fields['rx']}, {fields['is_rd']},
   {fields['addr']}, {fields['wr']}, {fields['wdata']}, {fields['rd']},
   {fields['rack']}, {fields['cmd']}⟩

end Metronome.HostCmd

"""


def axiom_audit(text):
    """Collect the `#print axioms` records from a Lean run."""
    return {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
            for name, axioms in AXIOM_LINE.findall(text)}


def check_hostcmd(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the elaborated host command machine and its generated Lean proofs.

    `rtlil_or_json` is a parsed Yosys design, a path to `design.json`, or a
    Verilog source directory to elaborate.  Evidence is written to `out_dir` as
    `<case>.hostcmd.lean` and `<case>.log`.  Returns a result dictionary; a
    rejected cut raises `HostCmdRejected` (proof or audit) or `UnsupportedRTL`
    (structure or wiring).
    """
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-hostcmd-{case}-") as tmp:
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
            check_host_top(modules)
            module = host_module(modules)
            info = extract_host(module)
            log.append(f"Host cut: {info['registers']} registers extracted, "
                       f"command-byte history variable uses "
                       f"{info['ghost_cells']} RTL gates\n")
            source = lean_hostcmd(info, fingerprint)
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the structural host check: {exc}\n")
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise
        source += TEMPLATE.read_text(encoding="utf-8")
        result = run_lean(source, "HostCmdProof.lean", f"{case}.hostcmd.lean",
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
            "ghost_cells": info["ghost_cells"],
            "fingerprint": fingerprint,
            "source": out_dir / f"{case}.hostcmd.lean",
            "log": out_dir / f"{case}.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            first = next((line.strip() for line in result.stdout.splitlines()
                          if "error:" in line), outcome)
            first = first.split("HostCmdProof.lean:", 1)[-1]
            raise HostCmdRejected(f"{case}: {outcome}\n" + "".join(log),
                                  reason=f"{outcome}: {first[:150]}",
                                  code=result.returncode)
    return report


def hostcmd_mutations():
    """The planted command-machine regressions, as snapshot transformers."""
    def replace(before, after):
        def apply(snapshot):
            require("md2_host.v" in snapshot, "mutation: missing md2_host.v")
            data = snapshot["md2_host.v"]
            require(data.count(before.encode()) == 1,
                    f"mutation: anchor changed in md2_host.v: {before}")
            return {**snapshot,
                    "md2_host.v": data.replace(before.encode(), after.encode(), 1)}
        return apply

    return [
        # A read data byte also issues a write strobe: the write path is enabled
        # for reads.
        ("hostcmd_read_strobes", replace(
            "if (is_rd) rd <= 1'b1;",
            "if (is_rd) begin rd <= 1'b1; wr <= 1'b1; end")),
        # ST_AL skips the data bytes and lands in the ignored state.
        ("hostcmd_al_next", replace(
            "addr <= {addr_i[15:8], byte_in}; st <= ST_DATA;",
            "addr <= {addr_i[15:8], byte_in}; st <= ST_IGN;")),
        # CS_N high keeps the byte state instead of returning to the command
        # byte.
        ("hostcmd_cs_hold", replace(
            "st <= ST_CMD; bitc <= 3'd0; tx <= 8'd0;",
            "bitc <= 3'd0; tx <= 8'd0;")),
        # A write strobe does not step the address, so a burst rewrites one
        # address.
        ("hostcmd_no_addr_step", replace(
            "wire [15:0] addr_i = (wr | ack) ? addr + 16'd1 : addr;",
            "wire [15:0] addr_i = ack ? addr + 16'd1 : addr;")),
        # The low address byte is placed in the high half, so the AH/AL bytes
        # are swapped.
        ("hostcmd_addr_bytes_swap", replace(
            "addr <= {addr_i[15:8], byte_in}; st <= ST_DATA;",
            "addr <= {byte_in, addr_i[15:8]}; st <= ST_DATA;")),
    ]


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted command-machine regression is rejected.

    Returns one `(case, rejected, stage, exit)` record per mutation and raises
    `HostCmdRejected` if any mutant is accepted.
    """
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-hostcmd-mutants-") as tmp:
        for case, transform in hostcmd_mutations():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_hostcmd(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"structural check: {exc}", 0))
                continue
            except HostCmdRejected as exc:
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
                        help="also check the planted command-machine regressions")
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
            raise HostCmdRejected("tool version query failed")

        build = run([lake, "build", "Metronome.HostCmd"], HERE)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise HostCmdRejected("lake build Metronome.HostCmd failed")

        snapshot = snapshot_of(ROOT / "src")
        report = check_hostcmd(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        emit(f"baseline: {report['outcome']} ({report['registers']} registers, "
             f"command-byte history variable on {report['ghost_cells']} RTL gates)")
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
        raise SystemExit(f"Host command check failed: {exc}") from exc
