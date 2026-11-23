"""Check the Metronome v4 stream datapath against SPEC_V2 §6.3, §12.3, §12.4, §13.2.

`src/md2_stream.v` is instantiated twice in the chip top, as
`tt_um_brentius_metronome.g_s[0].u` with `CAP = 1` (S0: edge capture and edge
replay) and `g_s[1].u` with `CAP = 0` (S1).  Both elaborated variants are cut
here: every state register's next-state cone is extracted fail-closed from the
elaborated `md2_stream` module, emitted as Lean, and proved equal to
`Metronome.Stream`'s independent specification written from the SPEC text.

The RAM is outside the cut.  `gnt` (the arbiter grant), `rdata` (the word the
RAM presents, §6.2: a word read in cycle `s` is at the RAM output in `s+1` and
the requester loads it at the end of `s+1`) and the capture/replay control
signals (`cap_push`, `replay_apply`, `replay_late`, the capture record) are
per-cycle inputs.  So are `frz`/`frzd` (§12.3): the freeze register is a
separate cut.

Run it from the repository root:

    python lean/stream_check.py
    python lean/stream_check.py --mutations

`run_mutations()` plants regressions on temporary copies of `src/` (never the
repository) and requires every one to be rejected.
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
from hostcmd_check import HostCone, axiom_audit, snapshot_of

STREAM_MODULE = "md2_stream"
DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_stream_v4_20261121"
TEMPLATE = HERE / "StreamEquivalence.lean.in"
LEAN_TIMEOUT = 900

# The two elaborated instances of the chip top, in the order they are emitted.
# `g_s[k].u` is the generate label of `project.v`.
INSTANCES = (("g_s[0].u", "CapOne", "true"), ("g_s[1].u", "CapTwo", "false"))

# (RTL net, width, Lean state field, Lean type) in `Metronome.Stream.State` order.
STATE = (
    ("pos", 12, "pos", "BitVec 12"),
    ("bidx", 3, "bidx", "BitVec 3"),
    ("ba", 11, "ba", "BitVec 11"),
    ("cur", 8, "cur", "BitVec 8"),
    ("cv", 1, "cv", "Bool"),
    ("wb", 32, "wb", "BitVec 32"),
    ("wv", 1, "wv", "Bool"),
    ("rq", 1, "rq", "Bool"),
    ("ld", 1, "ld", "Bool"),
    ("pend", 8, "pend", "BitVec 8"),
    ("pv", 1, "pv", "Bool"),
    ("starved", 1, "starved", "Bool"),
    ("nb", 32, "nb", "BitVec 32"),
    ("nv", 1, "nv", "Bool"),
)

# The §13.2 replay buffer slot, which only a `CAP = 1` stream has in the RTL.
CAP_ONLY = ("nb", "nv")

# (module port, width, Lean input field) of `Metronome.Stream.Input`.
INPUTS = (
    ("frz", 1, "frz"),
    ("frzd", 1, "frzd"),
    ("cap_en", 1, "capEn"),
    ("cap_push", 1, "capPush"),
    ("cap_rec", 32, "capRec"),
    ("replay_en", 1, "replayEn"),
    ("replay_apply", 1, "replayApply"),
    ("replay_late", 1, "replayLate"),
    ("cfg_mode", 1, "cfgMode"),
    ("cfg_msb", 1, "cfgMsb"),
    ("cfg_start", 11, "cfgStart"),
    ("cfg_len", 12, "cfgLen"),
    ("cfg_mark", 12, "cfgMark"),
    ("adv", 1, "adv"),
    ("rx_we", 1, "rxWe"),
    ("rx_bit", 1, "rxBit"),
    ("rewind", 1, "rewind"),
    ("flush", 1, "flush"),
    ("clr_starved", 1, "clrStarved"),
    ("gnt", 1, "gnt"),
    ("rdata", 32, "rdata"),
)

# (module output port, width, Lean `Metronome.Stream.Out` field, Lean def name)
OUTPUTS = (
    ("bit_out", 1, "bit", "rtlBit"),
    ("byte_out", 8, "byteOut", "rtlByteOut"),
    ("g_end", 1, "gEnd", "rtlGEnd"),
    ("g_mark", 1, "gMark", "rtlGMark"),
    ("g_byte", 1, "gByte", "rtlGByte"),
    ("req", 1, "req", "rtlReq"),
    ("req_we", 1, "reqWe", "rtlReqWe"),
    ("req_addr", 11, "reqAddr", "rtlReqAddr"),
    ("req_wdata", 8, "reqWdata", "rtlReqWdata"),
    ("req_word", 1, "reqWord", "rtlReqWord"),
    ("req_wword", 32, "reqWword", "rtlReqWword"),
    ("replay_valid", 1, "replayValid", "rtlReplayValid"),
    ("replay_word", 32, "replayWord", "rtlReplayWord"),
)

# `rtl<Field>` names for the state registers, in the same order as `STATE`.
STATE_DEFS = {"pos": "rtlPos", "bidx": "rtlBidx", "ba": "rtlBa", "cur": "rtlCur",
              "cv": "rtlCv", "wb": "rtlWb", "wv": "rtlWv", "rq": "rtlRq",
              "ld": "rtlLd", "pend": "rtlPend", "pv": "rtlPv",
              "starved": "rtlStarved", "nb": "rtlNb", "nv": "rtlNv"}


class StreamRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated stream cut."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


def _is_constant(bits):
    return bool(bits) and all(bit in ("0", "1") for bit in bits)


def constant_bits(bits, where):
    """Read a Yosys constant bus (little-endian) as an integer."""
    require(_is_constant(bits), f"{where}: expected a constant bus")
    return int("".join(reversed(bits)), 2)


class StreamCone(HostCone):
    """A host-command cone plus the shapes `md2_stream`'s cones need.

    `$mul` scales a narrow index by a constant (the `8 * BA[1:0]` lane select),
    `$shl` shifts by a variable amount (`(bitin & bit) << b`), `$reduce_bool`
    is Yosys's `!= 0` on a bus (`BIDX != 0`), `$shiftx` reads a part-select, and
    `$and`/`$or`/`$not` are also used on whole bytes.  Every extension stays
    fail-closed: a multiply with two non-constant operands, a shift or reduce
    of unexpected width, or any other cell raises `UnsupportedRTL`.
    """

    EXTRA = ("$mul", "$shl", "$shr", "$reduce_bool")

    def __init__(self, name, module):
        super().__init__(name, module)
        for cell_name, cell in module["cells"].items():
            kind = cell["type"]
            if kind not in self.EXTRA:
                continue
            pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
            where = f"{name}.{cell_name} ({kind})"
            if kind == "$reduce_bool":
                require(set(pins) == {"A", "Y"} and len(pins["Y"]) == 1 and
                        len(pins["A"]) == int(cell["parameters"]["A_WIDTH"], 2),
                        f"{where}: expected one scalar reduction")
            elif kind == "$mul":
                require(set(pins) == {"A", "B", "Y"},
                        f"{where}: unexpected multiply ports")
                require(_is_constant(pins["A"]) != _is_constant(pins["B"]),
                        f"{where}: expected a constant scale")
                factor = constant_bits(pins["A"] if _is_constant(pins["A"])
                                       else pins["B"], where)
                require(factor in (2, 4, 8, 16),
                        f"{where}: constant {factor} is not a documented lane scale")
            else:
                require(set(pins) == {"A", "B", "Y"} and len(pins["Y"]) >= 1,
                        f"{where}: unexpected shift ports")
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = (kind, pins, cell["parameters"], where)

    def expression(self, bits):
        driver = self.drivers.get(bits)
        if driver is not None and driver[0] in self.EXTRA:
            return self._extra_expression(bits, driver)
        if driver is not None and driver[0] == "$shiftx" and len(bits) > 1:
            return self._extra_expression(bits, driver)
        if driver is not None and driver[0] in ("$not", "$and", "$or") and len(bits) > 1:
            return self._bus_logic(bits, driver)
        return super().expression(bits)

    def nat_amount(self, bits):
        """A shift amount as a `Nat`, so Lean keeps it out of `BitVec` arithmetic.

        Yosys lowers `WB[8*BA[1:0] +: 8]` to a 32-bit `$mul`/`$add` chain feeding
        a `$shiftx`.  Reading that chain as a `Nat` expression keeps the part
        select in the form the specification writes (`8 * BA[1:0]`), instead of a
        `toNat` of a 32-bit product, which `simp` would turn into `Nat` modular
        arithmetic that `bv_decide` cannot bit-blast.
        """
        driver = self.drivers.get(bits)
        if driver is None and _is_constant(bits):
            return str(constant_bits(bits, "shift amount"))
        if driver is not None:
            kind, pins, params, where = driver
            if kind == "$mul":
                require(_is_constant(pins["A"]) != _is_constant(pins["B"]),
                        f"{where}: expected a constant scale")
                factor = constant_bits(pins["A"] if _is_constant(pins["A"])
                                       else pins["B"], where)
                other = pins["B"] if _is_constant(pins["A"]) else pins["A"]
                return f"({factor} * ({self.expression(other)}).toNat)"
            if kind == "$add":
                require(len(pins["A"]) == len(pins["B"]),
                        f"{where}: expected an equal-width sum")
                return (f"({self.nat_amount(pins['A'])} + "
                        f"{self.nat_amount(pins['B'])})")
        return f"({self.expression(bits)}).toNat"

    def _extra_expression(self, bits, driver):
        kind, pins, params, where = driver
        if kind == "$reduce_bool":
            require(len(bits) == 1, f"{where}: unexpected result bus")
            expr = f"({self.expression(pins['A'])} != 0)"
        elif kind == "$shiftx":
            width = int(params["Y_WIDTH"], 2)
            source_width = int(params["A_WIDTH"], 2)
            require(len(bits) == width and 1 < width <= source_width,
                    f"{where}: unexpected part-select widths")
            expr = (f"(BitVec.truncate {width} (BitVec.ushiftRight "
                    f"{self.expression(pins['A'])} "
                    f"{self.nat_amount(pins['B'])}))")
        elif kind == "$mul":
            width = int(params["Y_WIDTH"], 2)
            require(len(bits) == width, f"{where}: unexpected result bus")
            factor = constant_bits(pins["A"] if _is_constant(pins["A"])
                                   else pins["B"], where)
            other = pins["B"] if _is_constant(pins["A"]) else pins["A"]
            expr = (f"((BitVec.setWidth {width} {self.expression(other)}) * "
                    f"({factor} : BitVec {width}))")
        else:
            width = int(params["Y_WIDTH"], 2)
            require(len(bits) == width and len(pins["A"]) == width,
                    f"{where}: expected an in-place shift")
            operator = "<<<" if kind == "$shl" else ">>>"
            amount = self.expression(pins["B"])
            expr = f"({self.expression(pins['A'])} {operator} ({amount}).toNat)"
        wire = f"{self.name}{len(self.lines)}"
        self.lines.append(f"  let {wire} := {expr}")
        self.bound[bits] = wire
        return wire

    def _bus_logic(self, bits, driver):
        kind, pins, params, where = driver
        width = int(params["A_WIDTH"], 2)
        require(len(bits) == width == int(params["Y_WIDTH"], 2),
                f"{where}: expected a byte-wide logic cell")
        left = self.expression(pins["A"])
        if kind == "$not":
            expr = f"(~~~{left})"
        else:
            require(len(pins["B"]) == width, f"{where}: expected two operands")
            operator = "&&&" if kind == "$and" else "|||"
            expr = f"({left} {operator} {self.expression(pins['B'])})"
        wire = f"{self.name}{len(self.lines)}"
        self.lines.append(f"  let {wire} := {expr}")
        self.bound[bits] = wire
        return wire


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
        raise StreamRejected(f"Yosys elaboration failed: {result.stdout.strip()}")
    modules = json.loads((work / "design.json").read_text(encoding="utf-8"))["modules"]
    return modules, digest.hexdigest(), commands, result.stdout


def load_modules(rtlil_or_json):
    """Accept a parsed Yosys design dictionary or a path to its JSON file."""
    if isinstance(rtlil_or_json, dict):
        return rtlil_or_json.get("modules", rtlil_or_json)
    path = Path(rtlil_or_json)
    require(path.suffix == ".json", f"{path}: expected a Yosys JSON design")
    return json.loads(path.read_text(encoding="utf-8"))["modules"]


def net_bits(module, name, width, where):
    net = module["netnames"].get(name)
    require(net is not None, f"{where}.{name}: missing net")
    require("init" not in net["attributes"], f"{where}.{name}: unexpected initial value")
    bits = tuple(net["bits"])
    require(len(bits) == width, f"{where}.{name}: expected {width} bits")
    return bits


def register_cells(module):
    """Every `$dff` of the module as `(Q bits, D bits)`, and its width."""
    cells = []
    for name, cell in module["cells"].items():
        if cell["type"] not in ("$dff", "$adff"):
            continue
        pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
        cells.append((name, cell["type"], pins))
    return cells


def register_data(module, name, width, where):
    """The D-input bus of the one `$dff` driving the named net."""
    bits = net_bits(module, name, width, where)
    matches = [cell for cell in module["cells"].values()
               if cell["type"] in ("$dff", "$adff") and
               tuple(cell["connections"]["Q"]) == bits]
    require(len(matches) == 1, f"{where}.{name}: expected exactly one register driver")
    cell = matches[0]
    require(cell["type"] == "$dff", f"{where}.{name}: expected a plain register")
    return tuple(cell["connections"]["D"])


def stream_module(modules, instance, cap):
    """The specialized `md2_stream` module of one chip-top instance."""
    top = modules[TOP]
    require(instance in top["cells"], f"{TOP}.{instance}: missing stream instance")
    cell = top["cells"][instance]
    require(cell["type"] in modules, f"{instance}: missing specialized module")
    module = modules[cell["type"]]
    require(module["attributes"].get("hdlname") == STREAM_MODULE,
            f"{instance}: unexpected stream module")
    params = cell.get("parameters") or module.get("parameter_default_values") or {}
    require("CAP" in params, f"{instance}: missing CAP parameter")
    require(int(params["CAP"], 2) == (1 if cap else 0),
            f"{instance}: unexpected CAP parameter")
    require(tuple(cell["connections"]["clk"]) == tuple(top["ports"]["clk"]["bits"]),
            f"{instance}: unexpected clock")
    require(tuple(cell["connections"]["rst_n"]) == tuple(top["netnames"]["rst_q"]["bits"]),
            f"{instance}: unexpected reset")
    return module


def check_layout(module, cap, where):
    """Fail-closed checks on the register set and the module ports.

    Every state register must be a plain `$dff` of the specified width (the
    reset is synchronous in the RTL), the `CAP` variant must have the §13.2
    buffer slot only when it is a capture stream, and no other register may
    exist.
    """
    dffs = register_cells(module)
    by_width = {}
    for name, kind, pins in dffs:
        require(kind == "$dff", f"{where}.{name}: expected a synchronous-reset register")
        width = len(pins["Q"])
        require(len(pins["D"]) == width, f"{where}.{name}: inconsistent register width")
        by_width.setdefault(width, []).append(name)
    expected = [(name, width) for name, width, _, _ in STATE
                if cap or name not in CAP_ONLY]
    seen = []
    for name, width, _, _ in STATE:
        if not cap and name in CAP_ONLY:
            continue
        bits = net_bits(module, name, width, where)
        matches = [(cell_name, pins) for cell_name, kind, pins in dffs
                   if tuple(pins["Q"]) == bits]
        require(len(matches) == 1,
                f"{where}.{name}: expected exactly one register driver")
        seen.append((name, width))
    require(seen == expected, f"{where}: unexpected register set")
    register_count = len(dffs)
    require(register_count == len(expected),
            f"{where}: {register_count} registers, expected {len(expected)}")
    if not cap:
        for name in CAP_ONLY:
            net = module["netnames"].get(name)
            if net is None:
                continue
            bits = tuple(net["bits"])
            owners = [cell for cell in dffs if tuple(cell[2]["Q"]) == bits]
            require(not owners, f"{where}.{name}: unexpected replay buffer register")
    for port, width, _ in INPUTS:
        require(port in module["ports"], f"{where}.{port}: missing input port")
        require(module["ports"][port]["direction"] == "input" and
                len(module["ports"][port]["bits"]) == width,
                f"{where}.{port}: expected a {width}-bit input")
    for port, width, _, _ in OUTPUTS:
        require(port in module["ports"], f"{where}.{port}: missing output port")
        require(module["ports"][port]["direction"] == "output" and
                len(module["ports"][port]["bits"]) == width,
                f"{where}.{port}: expected a {width}-bit output")
    return {"registers": register_count,
            "cells": len([cell for cell in module["cells"].values()
                          if not cell["type"].startswith("$dff")])}


def seed(module, cap, name):
    """A fresh cone with every register and input bound to its Lean name.

    A fresh cone per field keeps each emitted definition to the logic of one
    next-state or output cone; a shared cone would leak the let-bound wires of
    one field into the definitions of all the others.
    """
    cone = StreamCone(name, module)
    cone.input("rst_n", 1, "input.resetN")
    for port, width, field in INPUTS:
        cone.input(port, width, f"input.{field}")
    for rtl_name, width, field, _ in STATE:
        if not cap and rtl_name in CAP_ONLY:
            continue
        cone.register(rtl_name, width, f"state.{field}")
    return cone


def field_definition(module, cap, rtl_name, width, field):
    """The Lean `def` of one next-state field, with its own let chain."""
    cone = seed(module, cap, STATE_DEFS[rtl_name])
    if not cap and rtl_name in CAP_ONLY:
        return (f"  -- a CAP = 0 stream has no §13.2 buffer slot: the field is inert\n"
                f"  state.{field}")
    data = register_data(module, rtl_name, width, STATE_DEFS[rtl_name])
    expr = cone.expression(data)
    body = "\n".join(cone.lines)
    return f"{body}\n  {expr}" if body else f"  {expr}"


def output_definition(module, cap, port, width, field, def_name):
    """The Lean `def` of one combinational output, with its own let chain."""
    cone = seed(module, cap, def_name)
    bits = tuple(module["ports"][port]["bits"])
    require(bits, f"{STREAM_MODULE}.{port}: empty output")
    expr = cone.expression(bits)
    body = "\n".join(cone.lines)
    return f"{body}\n  {expr}" if body else f"  {expr}"


def extract_stream(modules, instance, cap):
    """Extract both the next-state fields and the outputs of one variant."""
    module = stream_module(modules, instance, cap)
    where = f"{instance}({STREAM_MODULE})"
    layout = check_layout(module, cap, where)
    state_defs = {}
    for rtl_name, width, field, lean_type in STATE:
        body = field_definition(module, cap, rtl_name, width, field)
        state_defs[STATE_DEFS[rtl_name]] = (field, lean_type, body)
    output_defs = {}
    for port, width, field, def_name in OUTPUTS:
        body = output_definition(module, cap, port, width, field, def_name)
        output_defs[def_name] = (field, "Bool" if width == 1 else f"BitVec {width}", body)
    return {"state": state_defs, "out": output_defs, "layout": layout,
            "module": module, "instance": instance}


def binders(body):
    """The `State`/`Input` binders a generated definition actually uses.

    A field whose cone ignores the cycle's inputs (`NB`/`NV` of a `CAP = 0`
    stream, `BA` as a request address) must not name them, or the linter's
    unused-variable check would fail the generated file.
    """
    state = "state" if "state." in body else "_state"
    inp = "input" if "input." in body else "_input"
    return f"{state} : State) ({inp} : Input"


def lean_variant(info, cap_text, suffix, fingerprint):
    """Emit the extracted defs and the equivalence template of one variant."""
    lines = [f"namespace {suffix}",
             "",
             f"-- {info['instance']}: the elaborated `{STREAM_MODULE}` with CAP = {cap_text}.",
             f"-- Register states and combinational cells: "
             f"{info['layout']['registers']} registers, {info['layout']['cells']} gates.",
             f"-- RTL snapshot SHA-256: {fingerprint}",
             "",
             "/-- The `CAP` argument of this variant. -/",
             f"abbrev capValue : Bool := {cap_text}",
             ""]
    for def_name, (field, lean_type, body) in info["state"].items():
        lines.append(f"/-- Next state of `{field}`. -/")
        lines.append(f"def {def_name} ({binders(body)}) : {lean_type} :=")
        lines.append(body)
        lines.append("")
    for def_name, (field, lean_type, body) in info["out"].items():
        lines.append(f"/-- Output `{field}`. -/")
        lines.append(f"def {def_name} ({binders(body)}) : {lean_type} :=")
        lines.append(body)
        lines.append("")
    state_literal = ", ".join(STATE_DEFS[rtl_name] + " state input"
                              for rtl_name, _, _, _ in STATE)
    out_literal = ", ".join(def_name + " state input"
                            for _, _, _, def_name in OUTPUTS)
    lines += [f"/-- The elaborated next state, field by field. -/",
              f"def rtlStep (state : State) (input : Input) : State :=",
              f"  \u27e8{state_literal}\u27e9",
              "",
              f"/-- The elaborated combinational outputs. -/",
              f"def rtlOut (state : State) (input : Input) : Out :=",
              f"  \u27e8{out_literal}\u27e9",
              ""]
    template = TEMPLATE.read_text(encoding="utf-8")
    template = template.replace("@@CAP@@", cap_text).replace("@@SUFFIX@@", suffix)
    lines.append(template.rstrip("\n"))
    lines.append("")
    lines.append(f"end {suffix}")
    lines.append("")
    return "\n".join(lines)


def lean_stream(info_one, info_two, fingerprint):
    """The whole generated file: both elaborated variants of the stream."""
    header = f"""import Metronome.Stream

-- Generated from Yosys RTLIL by `stream_check.py`.  Both instantiations of
-- `src/md2_stream.v` are cut: S0 (`CAP = 1`, edge capture and edge replay) and
-- S1 (`CAP = 0`).  Every state register and every output cone is extracted
-- fail-closed from the elaborated cells; `gnt`, the RAM read word, the
-- capture/replay control signals and `frz`/`frzd` are per-cycle inputs.
-- RTL snapshot SHA-256: {fingerprint}

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Metronome.Stream

"""
    return (header + lean_variant(info_one, "true", "CapOne", fingerprint) + "\n" +
            lean_variant(info_two, "false", "CapTwo", fingerprint) + "\n" +
            "end Metronome.Stream\n")


def failing_theorem(source, text):
    """The generated declaration whose proof Lean rejected first."""
    match = re.search(r"StreamProof\.lean:(\d+):\d+: error", text)
    if match is None:
        return None
    lines = source.splitlines()
    for index in range(min(int(match.group(1)), len(lines)) - 1, -1, -1):
        stripped = lines[index].lstrip()
        if stripped.startswith("theorem ") or stripped.startswith("def "):
            return stripped.split()[1]
    return None


def run_lean(source, filename, artifact, lake, work, evidence):
    """Run the generated file with a real exit code and a hard timeout."""
    path = work / filename
    path.write_text(source, encoding="utf-8")
    if evidence:
        (evidence / artifact).write_text(source, encoding="utf-8")
    return run([lake, "env", "lean", "-j1", "-DwarningAsError=true", str(path)],
               HERE, timeout=LEAN_TIMEOUT)


def check_stream(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check both elaborated stream variants and their generated Lean proofs.

    `rtlil_or_json` is a parsed Yosys design, a path to `design.json`, or a
    Verilog source directory to elaborate.  Evidence is written to `out_dir` as
    `<case>.stream.lean` and `<case>.log`.  Returns a result dictionary; a
    rejected cut raises `StreamRejected` (proof or audit) or `UnsupportedRTL`
    (structure or wiring).
    """
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-stream-{case}-") as tmp:
        work = Path(tmp)
        is_json = isinstance(rtlil_or_json, dict) or (
            isinstance(rtlil_or_json, (str, Path)) and
            Path(rtlil_or_json).suffix == ".json")
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
            one = extract_stream(modules, INSTANCES[0][0], True)
            two = extract_stream(modules, INSTANCES[1][0], False)
            for info in (one, two):
                log.append(f"{info['instance']}: {info['layout']['registers']} registers, "
                           f"{info['layout']['cells']} gates\n")
            source = lean_stream(one, two, fingerprint)
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the structural stream check: {exc}\n")
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise
        result = run_lean(source, "StreamProof.lean", f"{case}.stream.lean",
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
            "registers": one["layout"]["registers"] + two["layout"]["registers"],
            "gates": one["layout"]["cells"] + two["layout"]["cells"],
            "fingerprint": fingerprint,
            "source": out_dir / f"{case}.stream.lean",
            "log": out_dir / f"{case}.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            first = next((line.strip() for line in result.stdout.splitlines()
                          if "error:" in line), outcome)
            first = first.split("StreamProof.lean:", 1)[-1]
            where = failing_theorem(source, result.stdout)
            detail = f"{outcome} at {where}: {first[:120]}" if where else f"{outcome}: {first[:150]}"
            raise StreamRejected(f"{case}: {outcome}\n" + "".join(log),
                                 reason=detail, code=result.returncode)
    return report


def stream_mutations():
    """The planted stream regressions, as snapshot transformers."""
    def replace(before, after):
        def apply(snapshot):
            require("md2_stream.v" in snapshot, "mutation: missing md2_stream.v")
            data = snapshot["md2_stream.v"]
            require(data.count(before.encode()) == 1,
                    f"mutation: anchor changed in md2_stream.v: {before}")
            return {**snapshot,
                    "md2_stream.v": data.replace(before.encode(), after.encode(), 1)}
        return apply

    return [
        # MSB-first transmits the LSB-first bit position.
        ("stream_msb_index", replace(
            "wire [2:0] bsel  = cfg_msb ? ~bidx : bidx;",
            "wire [2:0] bsel  = bidx;")),
        # An advance with no byte does not set STARVED.
        ("stream_no_adv_starve", replace(
            "wire starve_tx = tx_adv & (~cv | (last & ~wv));",
            "wire starve_tx = tx_adv & (last & ~wv);")),
        # A rewind leaves PV set, so a stale write request survives it.
        ("stream_rewind_keeps_pv", replace(
            "                rq <= 1'b0; ld <= 1'b0; pv <= 1'b0;",
            "                rq <= 1'b0; ld <= 1'b0; pv <= pv;")),
        # A completed byte overwrites PEND while an unserved byte still waits.
        ("stream_write_when_stalled", replace(
            "                    if (~(pv & ~gnt)) begin pend <= nsh; pv <= 1'b1; end",
            "                    begin pend <= nsh; pv <= 1'b1; end")),
        # The assembly register takes the pin bit without a received bit, so a
        # flushed byte is not zero-padded.
        ("stream_flush_unpadded", replace(
            "wire [7:0] nsh = cur | ({7'd0, bitin & rx_bit} << bsel);",
            "wire [7:0] nsh = cur | ({7'd0, rx_bit} << bsel);")),
        # The END guard compares POS with MARK instead of the live LEN.
        ("stream_end_is_mark", replace(
            "assign g_end    = end_c;",
            "assign g_end    = (pos == cfg_mark);")),
        # A capture record writes four bytes at BA + 1 instead of BA + 4.
        ("stream_capture_ba_one", replace(
            "            if (pv & gnt) begin pv <= 1'b0; ba <= ba + 11'd4; end",
            "            if (pv & gnt) begin pv <= 1'b0; ba <= ba + 11'd1; end")),
        # A served replay read advances POS by one byte instead of one word.
        ("stream_replay_pos_one", replace(
            "                    ba <= ba + 11'd4; pos <= pos + 12'd4;",
            "                    ba <= ba + 11'd4; pos <= pos + 12'd1;")),
    ]


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted stream regression is rejected.

    Returns one `(case, rejected, stage, exit)` record per mutation and raises
    `StreamRejected` if any mutant is accepted.
    """
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-stream-mutants-") as tmp:
        for case, transform in stream_mutations():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_stream(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"structural check: {exc}", 0))
                continue
            except StreamRejected as exc:
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
                        help="also check the planted stream regressions")
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
            raise StreamRejected("tool version query failed")

        build = run([lake, "build", "Metronome.Stream"], HERE, timeout=LEAN_TIMEOUT)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise StreamRejected("lake build Metronome.Stream failed")

        snapshot = snapshot_of(ROOT / "src")
        report = check_stream(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        emit(f"baseline: {report['outcome']} ({report['registers']} registers, "
             f"{report['gates']} gates, both CAP variants)")
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
        raise SystemExit(f"Stream check failed: {exc}") from exc
