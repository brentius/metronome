#!/usr/bin/env python3
"""Inventory and closure check for the Metronome v4 Lean cut suite (item 4M).

This is not a new proof.  It answers two questions about the existing
`*_check.py` cuts by reading the same Yosys elaboration and the same
extraction entry points the checkers use:

1. **Coverage.**  Which elaborated cells does each cut's cones read?
   Walked over the whole instance tree, which cells does no cut read at all?
2. **Closure.**  For every net a cut leaves free, where does that net come
   from?  A top-level pin, a register some cut proves, the output of a cone
   some cut proves, a configuration-latch output, an SRAM macro output, or
   nothing proved (UNCLOSED)?

The tooling is read-only: it imports the checker modules and calls their
extraction functions (never their Lean proofs), with the adapter's binding
methods instrumented so the roots, free leaves and owned registers of every
cone are recorded.  It elaborates once with the hardened SRAM define
(`-D USE_IHP_SRAM`, the recipe `mem_check.py` and `debug_check.py` use), since
that is the design the two macro-boundary cuts see.

Run:

    python lean/coverage_check.py --artifacts-dir data/raw/lean_coverage_v4_20261121

The directory must not exist.  The run is an inventory and exits 0 when it
completes; `--strict` additionally exits 1 if any free leaf is UNCLOSED or any
non-black-box cell is uncovered.
"""

import argparse
from collections import Counter, OrderedDict, defaultdict
import json
import platform
import shutil
import subprocess
import sys
import time
import traceback
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[0]
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import rtlil  # noqa: E402
import bank_check  # noqa: E402
import core_check  # noqa: E402
import corectl_check  # noqa: E402
import debug_check  # noqa: E402
import glue_check  # noqa: E402
import hostcmd_check  # noqa: E402
import hostmap_check  # noqa: E402
import hostpins_check  # noqa: E402
import hostread_check  # noqa: E402
import line_check  # noqa: E402
import mem_check  # noqa: E402
import moves_check  # noqa: E402
import spipins_check  # noqa: E402
import stream_check  # noqa: E402
import strobes_check  # noqa: E402
import thread_check  # noqa: E402
import units_check  # noqa: E402
import verify  # noqa: E402

TOP = verify.TOP
SRAM_DEFINES = ("USE_IHP_SRAM",)
STATE_TYPES = ("$dff", "$adff", "$dffe", "$adffe", "$sdff", "$sdffe",
               "$dlatch", "$adlatch", "$sr")
# Behavioural models of the two IHP library cells used by the latch bank.  The
# suite trusts the models match the library cells (lean/README.md,
# "Proof boundary"), so the models are a stated boundary, not proved logic.
BANK_CELL_TYPES = ("cfg_dlhrq_beh", "cfg_lgcp_beh")
# SRAM macro black boxes declared in src/md2_sram_bb.v.
MACRO_TYPES = ("RM_IHPSG13_1P_256x64_c2_bm_bist",
               "RM_IHPSG13_1P_512x32_c2_bm_bist")

CHECKERS = (bank_check, core_check, corectl_check, debug_check, glue_check,
            hostcmd_check, hostmap_check, hostpins_check, hostread_check,
            line_check, mem_check, moves_check, spipins_check, stream_check, strobes_check,
            thread_check, units_check, verify)

FREE_METHODS = ("free", "leaf", "input", "opaque", "bind_bits", "leaf_bits",
                "overwrite")
BOUND_METHODS = ("register", "alias")
# Methods that ask the adapter to express a net's driver.  `_bit_bool` and
# `bool_of` are the one-bit forms the thread/glue cuts use instead of a
# one-element `expression` call.
ROOT_METHODS = ("expression", "_bit_bool", "bool_of")


# --------------------------------------------------------------------------
# Elaboration

def snapshot_of(directory):
    directory = Path(directory)
    snapshot = {path.name: path.read_bytes() for path in sorted(directory.iterdir())
                if path.suffix in (".v", ".vh")}
    if not snapshot:
        raise SystemExit(f"{directory}: no Verilog sources")
    return snapshot


def elaborate(snapshot, work, yosys, timeout):
    """The shared Yosys recipe, with the hardened SRAM define."""
    work = Path(work)
    src = work / "src"
    src.mkdir(parents=True, exist_ok=True)
    for name, content in sorted(snapshot.items()):
        (src / name).write_bytes(content)
    files = " ".join(f"src/{path.name}" for path in sorted(src.glob("*.v")))
    defines = " ".join(f"-D {name}" for name in SRAM_DEFINES)
    commands = (f"read_verilog -I src {defines} {files}; "
                f"hierarchy -check -top {TOP}; proc; opt_clean; write_json design.json")
    result = subprocess.run([yosys, "-Q", "-q", "-p", commands], cwd=work,
                            capture_output=True, text=True, timeout=timeout)
    tool_log = (f"yosys: {yosys}\ncommand: {commands}\n"
                f"exit: {result.returncode}\n"
                f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}\n")
    if result.returncode != 0:
        raise SystemExit("Yosys elaboration failed\n" + tool_log)
    modules = json.loads((work / "design.json").read_text(encoding="utf-8"))["modules"]
    return modules, commands, tool_log


def yosys_version(yosys, timeout):
    try:
        result = subprocess.run([yosys, "-V"], capture_output=True, text=True,
                                timeout=timeout)
        return result.stdout.strip() or result.stderr.strip()
    except Exception as exc:  # pragma: no cover - diagnostics only
        return f"unavailable: {exc}"


# --------------------------------------------------------------------------
# Design index

class Design:
    """Read-only indexes over one elaborated Yosys design."""

    def __init__(self, modules):
        self.modules = modules
        self.module_of_id = {id(module): name for name, module in modules.items()}
        self.drivers = {}
        self.inputs = {}
        self.cell_types = {}
        self.instances = defaultdict(list)
        for name, module in modules.items():
            drivers = {}
            for cell_name, cell in module.get("cells", {}).items():
                for pin, bits in cell["connections"].items():
                    if cell["port_directions"][pin] in ("output", "inout"):
                        for bit in bits:
                            drivers.setdefault(bit, (cell_name, pin))
                self.instances[(name, cell["type"])].append((cell_name, cell))
            self.drivers[name] = drivers
            inputs = {}
            for port_name, port in module.get("ports", {}).items():
                if port["direction"] == "input":
                    for bit in port["bits"]:
                        inputs.setdefault(bit, port_name)
            self.inputs[name] = inputs
            self.cell_types[name] = {cell_name: cell["type"]
                                     for cell_name, cell in module.get("cells", {}).items()}

    def module_name(self, module):
        return self.module_of_id[id(module)]

    def is_blackbox(self, name):
        module = self.modules.get(name)
        if module is None:
            return False
        attributes = module.get("attributes", {})
        value = attributes.get("blackbox")
        return value not in (None, "", "0")

    def is_state(self, cell_type):
        return cell_type.startswith(STATE_TYPES)

    def is_instance(self, cell_type):
        return cell_type in self.modules

    def int_module(self, module):
        return (module.get("attributes", {}).get("hdlname") or "")

    def cell_src(self, module_name, cell_name):
        cell = self.modules[module_name]["cells"][cell_name]
        value = cell.get("attributes", {}).get("src")
        if not value:
            return None
        text = value.strip("\\\"")
        # Yosys emits `file.v:start.column-end.column`; keep file and start line.
        head = text.split("-", 1)[0]
        parts = head.split(":")
        if len(parts) >= 2:
            file = parts[0].replace("\\", "/")
            line = parts[1].split(".", 1)[0]
            return file, int(line) if line.isdigit() else 0
        return text, 0


# --------------------------------------------------------------------------
# Binding recorder
#
# Every checker builds cones from the shared rtlil.Cone/DffCone adapter or a
# subclass of it.  Wrapping the binding methods of those classes records the
# exact roots, free leaves and owned registers without editing any checker.

EVENTS = None
_NEXT_CONE = [0]


def _resolve_bits(cone, name):
    module = cone.module
    net = module.get("netnames", {}).get(name)
    if net is not None:
        return tuple(net["bits"])
    port = module.get("ports", {}).get(name)
    if port is not None:
        return tuple(port["bits"])
    return None


def _emit(cone, method, kind, name=None, bits=None):
    if EVENTS is None:
        return
    if bits is None and name is not None:
        bits = _resolve_bits(cone, name)
    # `id(cone)` is reused after a cone is collected (the line and thread cuts
    # build one cone per layer/pin), so give each cone object a stable number.
    cone_id = getattr(cone, "_coverage_cone_id", None)
    if cone_id is None:
        cone_id = _NEXT_CONE[0]
        _NEXT_CONE[0] += 1
        cone._coverage_cone_id = cone_id
    EVENTS.append({
        "method": method,
        "kind": kind,
        "module": id(cone.module),
        "cone": cone_id,
        "name": name,
        "bits": tuple(bits) if bits is not None else None,
    })


def _wrap(cls, method, kind):
    original = cls.__dict__[method]
    if getattr(original, "__coverage_wrapped__", False):
        return

    def wrapper(self, *args, **kwargs):
        result = original(self, *args, **kwargs)
        try:
            if method in ("expression", "bool_of"):
                _emit(self, method, kind, bits=args[0])
            elif method == "_bit_bool":
                bit = args[0]
                _emit(self, method, kind,
                      bits=bit if isinstance(bit, (tuple, list)) else (bit,))
            elif method in ("bind_bits", "leaf_bits"):
                _emit(self, method, kind, bits=args[0])
            elif method in ("free", "leaf", "input", "opaque", "overwrite", "register", "alias"):
                _emit(self, method, kind, name=args[0])
        except Exception:
            # Recording must never change the extraction's behaviour.
            pass
        return result

    wrapper.__coverage_wrapped__ = True
    wrapper.__name__ = getattr(original, "__name__", method)
    wrapper.__doc__ = getattr(original, "__doc__", None)
    setattr(cls, method, wrapper)


def instrument():
    for method in ROOT_METHODS:
        if method in rtlil.Cone.__dict__:
            _wrap(rtlil.Cone, method, "root")
        if method in rtlil.DffCone.__dict__:
            _wrap(rtlil.DffCone, method, "root")
    for method in ("input",):
        _wrap(rtlil.Cone, method, "free")
    for method in ("register",):
        for cls in (rtlil.Cone, rtlil.DffCone):
            if method in cls.__dict__:
                _wrap(cls, method, "bound")
    for method in ("free", "leaf"):
        _wrap(rtlil.DffCone, method, "free")
    classes = {rtlil.Cone, rtlil.DffCone}
    for checker in CHECKERS:
        for value in list(vars(checker).values()):
            if isinstance(value, type) and issubclass(value, rtlil.Cone):
                classes.add(value)
    for cls in classes:
        for method in FREE_METHODS + ROOT_METHODS:
            if method in cls.__dict__:
                _wrap(cls, method, "root" if method in ROOT_METHODS else "free")
        for method in BOUND_METHODS:
            if method in cls.__dict__:
                _wrap(cls, method, "bound")


# --------------------------------------------------------------------------
# Cut registry.  Each entry names the checker entry points it runs.  Nothing
# here re-implements a checker: the extraction functions are the checkers' own.

def cut_config(design, snapshot):
    verify.lean_transition(design.modules, "coverage")
    return "verify.lean_transition (arbiter + write stage)"


def cut_host(design, snapshot):
    verify.lean_host(design.modules, "coverage")
    return "verify.lean_host (md2_host wr/bitc)"


def cut_decode(design, snapshot):
    verify.lean_decode(design.modules, "coverage")
    return "verify.lean_decode (host/core configuration decode)"


def cut_corequeue(design, snapshot):
    verify.lean_core_queue(design.modules, "coverage")
    return "verify.lean_core_queue (pending configuration write queue)"


def cut_bank(design, snapshot):
    info = bank_check.extract_bank(design.modules)
    return (f"bank_check.extract_bank + verify.check_bank_mask "
            f"({len(info['live'])} live byte gates, {info['latch_bits']} latches)")


def cut_hostcmd(design, snapshot):
    hostcmd_check.extract_host(hostcmd_check.host_module(design.modules))
    return "hostcmd_check.extract_host (md2_host command machine)"


def cut_corectl(design, snapshot):
    params = corectl_check.header_params(snapshot)
    corectl_check.extract_pick(design.modules, params)
    corectl_check.extract_freeze(design.modules)
    corectl_check.extract_strobe(design.modules, "c_wr_stk", params,
                                 "ctrl_base", "ctrl_span", "ctrl_offset")
    corectl_check.extract_strobe(design.modules, "d_wr_dbg", params,
                                 "dbg_base", "dbg_span", "dbg_offset")
    corectl_check.extract_sticky_bit(design.modules)
    return "corectl_check.extract_pick/freeze/strobe/sticky_bit"


def cut_hostmap(design, snapshot):
    params = hostmap_check.header_params(snapshot)
    table = hostmap_check.enable_table(params)
    hostmap_check.extract_all(design.modules, table)
    return f"hostmap_check.extract_all ({len(table)} register enables)"


def cut_hostread(design, snapshot):
    module = hostcmd_check.host_module(design.modules)
    hostread_check.extract_read(module)
    rdval = hostread_check.extract_rdval(design.modules)
    hostread_check.extract_rdval_dontcare(design.modules, rdval[3])
    hostread_check.extract_miso(design.modules)
    return "hostread_check.extract_read/rdval/rdval_dontcare/miso"


def cut_spipins(design, snapshot):
    spipins_check.extract_pins(design.modules)
    return "spipins_check.extract_pins (synchronisers and host wiring)"


def cut_mem(design, snapshot):
    mem_check.check_mem_top(design.modules)
    mem_check.check_dmem(design.modules)
    module = design.modules[design.modules[TOP]["cells"][mem_check.MEM_CELL]["type"]]
    mem_check.extract_mem(module)
    return "mem_check.extract_mem + check_dmem (arbiter and SRAM boundary)"


def cut_thread(design, snapshot):
    module = thread_check.check_thread_top(design.modules)
    thread_check.extract_thread_module(module)
    constants, _codes = thread_check.header_constants(ROOT / "src")
    for k in range(thread_check.NTHREADS):
        thread_check.extract_thread_inputs(design.modules, k, constants)
    return "thread_check.extract_thread_module + extract_thread_inputs x6"


def cut_stream(design, snapshot):
    for instance, _name, _cap in stream_check.INSTANCES:
        stream_check.extract_stream(design.modules, instance, _cap == "true")
    return "stream_check.extract_stream (CAP=1 and CAP=0 variants)"


def cut_units(design, snapshot):
    consts = units_check.header_constants(snapshot)
    units_check.check_units_top(design.modules, consts)
    units_check.extract_counter(design.modules["md2_counter"])
    units_check.extract_shifter(design.modules["md2_shifter"])
    units_check.extract_lfsr(design.modules["md2_lfsr"])
    acc = next(module for name, module in design.modules.items()
               if units_check.ACC_MODULE_HINT in name and "paramod" in name)
    units_check.extract_acc(acc)
    for k in range(3):
        units_check.extract_sel(design.modules, "counter", k)
    for k in range(2):
        units_check.extract_sel(design.modules, "lfsr", k)
    for slot in range(6):
        units_check.extract_acc_sel(design.modules, slot)
    return "units_check.extract_counter/shifter/lfsr/acc/sel/acc_sel"


def cut_moves(design, snapshot):
    params = moves_check.moves_params(snapshot)
    moves_check.extract_moves(design.modules, params)
    header = corectl_check.header_params(snapshot)
    moves_check.extract_sticky(design.modules, params, header)
    return "moves_check.extract_moves + extract_sticky"


def cut_line(design, snapshot):
    header = line_check.check_header(line_check.module_header(ROOT / "src" / "md2_map.vh"))
    module, _kind = line_check.line_module(design.modules, header)
    line_check.check_line_top(design.modules, header)
    line_check.extract_line(design.modules, header, module)
    return "line_check.extract_line (layers, outputs, transition)"


def cut_core(design, snapshot):
    core_check.check_core_top(design.modules)
    variants = core_check.core_modules(design.modules)
    for c in (0, 1):
        core_check.check_fields(variants[c][1])
        core_check.check_jg(variants[c][1])
        core_check.extract_core(variants[c][1], c)
    return "core_check.extract_core (C=0 and C=1 variants)"


def cut_debug(design, snapshot):
    debug_check.extract_all(design.modules)
    return "debug_check.extract_all (pins, digest, ctrl, pmem, reset)"


def cut_glue(design, snapshot):
    header = glue_check.header_constants(snapshot)
    tables = glue_check.check_tables(snapshot)
    glue_check.extract(design.modules, header, tables)
    return "glue_check.extract (sources, guards, lines, control, outputs, pins)"


def cut_hostpins(design, snapshot):
    hostcmd_check.host_module(design.modules)
    module = hostcmd_check.host_module(design.modules)
    spipins_check.extract_pins(design.modules)
    hostcmd_check.extract_host(module)
    read = hostread_check.extract_read(module)
    hostpins_check.extract_read_noaddr(module)
    rdval = hostread_check.extract_rdval(design.modules)
    hostread_check.extract_rdval_dontcare(design.modules, rdval[3])
    hostread_check.extract_miso(design.modules)
    return "spipins + hostcmd + hostread + hostpins.extract_read_noaddr (composed)"



def cut_strobes(design, snapshot):
    params = strobes_check.strobes_params(snapshot)
    strobes_check.extract_opg(design.modules, params)
    strobes_check.extract_acc_hit(design.modules, params)
    strobes_check.extract_units(design.modules, params)
    strobes_check.extract_control(design.modules, params)
    return "strobes_check.extract_{opg,acc_hit,units,control} (op strobes, selectors, stream/DBG strobes)"

CUTS = (
    dict(name="verify/config", section="SPEC_V2 13.1 arbiter and write stage",
         run=cut_config),
    dict(name="verify/host", section="SPEC_V2 9 host wr/bitc",
         run=cut_host),
    dict(name="verify/decode", section="SPEC_V2 13.1 configuration address decode",
         run=cut_decode),
    dict(name="verify/corequeue", section="SPEC_V2 13.1 core pending write queue",
         run=cut_corequeue),
    dict(name="bank", section="SPEC_V2 13.1 latch bank (gates, latches, mask)",
         run=cut_bank),
    dict(name="hostcmd", section="SPEC_V2 9 SPI command machine",
         run=cut_hostcmd),
    dict(name="corectl", section="SPEC_V2 6/9/12.3 CW pick, freeze, sticky",
         run=cut_corectl),
    dict(name="hostmap", section="SPEC_V2 9 host write decode and registers",
         run=cut_hostmap),
    dict(name="hostread", section="SPEC_V2 9/13.2 host read path",
         run=cut_hostread),
    dict(name="spipins", section="SPEC_V2 2 pin synchronisers",
         run=cut_spipins),
    dict(name="mem", section="SPEC_V2 9a data-RAM arbiter and SRAM boundary",
         run=cut_mem),
    dict(name="thread", section="SPEC_V2 4/5 thread state and chip-top inputs",
         run=cut_thread),
    dict(name="stream", section="SPEC_V2 13.2 stream buffer",
         run=cut_stream),
    dict(name="units", section="SPEC_V2 6 accumulator/counters/shifters/LFSRs",
         run=cut_units),
    dict(name="moves", section="SPEC_V2 6/7 move resolution and sticky errors",
         run=cut_moves),
    dict(name="line", section="SPEC_V2 3 line state",
         run=cut_line),
    dict(name="core", section="SPEC_V2 5 core state and outputs",
         run=cut_core),
    dict(name="debug", section="SPEC_V2 2/12 pins, digest, replay, pmem, reset",
         run=cut_debug),
    dict(name="glue", section="SPEC_V2 6/6.1/7/8/9/12 sources, guards, control, outputs",
         run=cut_glue),
    dict(name="hostpins", section="SPEC_V2 2/9/13.2 composed host transaction",
         run=cut_hostpins),
    dict(name="strobes", section="SPEC_V2 6/6.1/6.3/3.6/13.1 per-unit op strobes and selectors",
         run=cut_strobes),
)


# --------------------------------------------------------------------------
# Cone walking and closure

class Report:
    def __init__(self, design):
        self.design = design
        self.cells = defaultdict(lambda: defaultdict(list))   # module -> cell -> [cut]
        self.owned = defaultdict(list)                       # (module, bit) -> [(cut, name)]
        self.leaves = []                                     # closure rows
        self.cuts = []                                       # per-cut records
        self.errors = []
        self.structural = defaultdict(list)                  # module -> cell -> [label]

    def add_covered(self, module_name, cell_names, cut_name):
        for cell_name in cell_names:
            names = self.cells[module_name][cell_name]
            if not any(name == cut_name for name, _ in names):
                names.append((cut_name, "cone"))


def walk_cells(design, module_name, roots, stops, register_net_bits):
    """Combinational cells behind `roots`, stopping at leaves and state."""
    module = design.modules[module_name]
    drivers = design.drivers[module_name]
    cells = set()
    seen = set()
    stack = list(roots)
    while stack:
        bit = stack.pop()
        if not isinstance(bit, int) or bit in seen:
            continue
        seen.add(bit)
        if bit in stops:
            continue
        driver = drivers.get(bit)
        if driver is None:
            continue
        cell_name, pin = driver
        cell = module["cells"][cell_name]
        cell_type = cell["type"]
        if design.is_state(cell_type) or design.is_instance(cell_type):
            continue
        cells.add(cell_name)
        for in_pin, bits in cell["connections"].items():
            if cell["port_directions"][in_pin] == "input":
                stack.extend(bits)
    if register_net_bits:
        for bits in register_net_bits:
            for bit in bits:
                driver = drivers.get(bit)
                if driver is not None and design.is_state(
                        module["cells"][driver[0]]["type"]):
                    cells.add(driver[0])
                    break
    return cells


def process_cut(design, report, label, events, extraction):
    by_module = defaultdict(list)
    for event in events:
        by_module[event["module"]].append(event)
    record = {"name": label, "extraction": extraction, "modules": []}
    for module_id, module_events in by_module.items():
        module_name = design.module_of_id[module_id]
        covered = set()
        all_roots, all_stops = set(), set()
        free, registers = [], []
        seen_free, seen_reg = set(), set()
        # One cone (adapter instance) has its own roots and leaves.  A net that
        # is a root of one cone can be a leaf of another (the line cut's
        # layers, the glue cut's output index), so the walk is per cone.
        cones = defaultdict(list)
        for event in module_events:
            cones[event["cone"]].append(event)
        for cone_events in cones.values():
            roots, stops, cone_registers = set(), set(), []
            for event in cone_events:
                if event["kind"] == "root" and event["bits"]:
                    roots.update(event["bits"])
                elif event["kind"] == "free" and event["bits"]:
                    stops.update(event["bits"])
                elif event["kind"] == "bound" and event["bits"]:
                    stops.update(event["bits"])
                    if event["method"] == "register":
                        cone_registers.append(tuple(event["bits"]))
            covered |= walk_cells(design, module_name, roots, stops, cone_registers)
            all_roots |= roots
            all_stops |= stops
        for event in module_events:
            if event["kind"] == "free" and event["bits"]:
                key = (event["name"], tuple(event["bits"]))
                if key not in seen_free:
                    seen_free.add(key)
                    free.append((event["name"], tuple(event["bits"]), event["method"]))
            elif event["kind"] == "bound" and event["bits"] and event["method"] == "register":
                key = (event["name"], tuple(event["bits"]))
                if key not in seen_reg:
                    seen_reg.add(key)
                    registers.append((event["name"], tuple(event["bits"])))
                for bit in event["bits"]:
                    report.owned[(module_name, bit)].append((label, event["name"]))
        report.add_covered(module_name, covered, label)
        record["modules"].append({
            "module": module_name,
            "cones": len(cones),
            "roots": len(all_roots),
            "stops": len(all_stops),
            "cells": len(covered),
            "registers": [{"net": name, "width": len(bits)} for name, bits in registers],
            "leaves": [{"net": name, "width": len(bits), "method": method}
                       for name, bits, method in free],
        })
        for name, bits, method in free:
            report.leaves.append({
                "cut": label,
                "module": module_name,
                "leaf": name if name is not None else "<bits>",
                "width": len(bits),
                "method": method,
                "bits": bits,
            })
    report.cuts.append(record)


def classify_source(design, report, module_name, bit, depth=0):
    """Classify one net bit by its ultimate source (recursively)."""
    if not isinstance(bit, int):
        return "constant", "tie-off"
    module = design.modules[module_name]
    driver = design.drivers[module_name].get(bit)
    if driver is None:
        port = design.inputs[module_name].get(bit)
        if port is not None:
            port_bits = tuple(module["ports"][port]["bits"])
            index = port_bits.index(bit)
            if module_name == TOP:
                return "pin", f"{port}[{index}]"
            # A leaf may be a slice of a module input (the line cut's cfg
            # fields): resolve it through every chip-top instance of the module
            # to the connected top-level net.
            instances = design.instances.get((TOP, module_name), ())
            if instances and depth < 12:
                categories = Counter()
                details = []
                for cell_name, cell in instances:
                    connection = tuple(cell["connections"].get(port, ()))
                    if index >= len(connection):
                        categories["UNCLOSED"] += 1
                        details.append(f"{cell_name}.{port}[{index}]: unconnected")
                        continue
                    category, detail = classify_source(design, report, TOP,
                                                       connection[index], depth + 1)
                    categories[category] += 1
                    details.append(f"{cell_name}: {detail}")
                return _merge(categories, details), f"{module_name}.{port}[{index}]"
            return "module_input", f"{module_name}.{port}[{index}]"
        return "UNCLOSED", f"{module_name}: undriven bit"
    cell_name, pin = driver
    cell = module["cells"][cell_name]
    cell_type = cell["type"]
    if design.is_state(cell_type):
        owners = report.owned.get((module_name, bit), [])
        if owners:
            cuts = sorted({name for name, _ in owners})
            return "owned_register", f"{cell_name} ({cell_type}) owned by {', '.join(cuts)}"
        return "UNCLOSED", f"{module_name}.{cell_name} ({cell_type}) register not owned by a cut"
    if design.is_instance(cell_type):
        if cell_type in BANK_CELL_TYPES:
            return ("bank_latch",
                    f"{module_name}.{cell_name} ({cell_type}) library cell model")
        if cell_type in MACRO_TYPES or design.is_blackbox(cell_type):
            return ("macro", f"{module_name}.{cell_name} ({cell_type}).{pin}")
        if depth > 12:
            return "UNCLOSED", "hierarchy recursion limit"
        sub = design.modules[cell_type]
        target = tuple(sub["ports"][pin]["bits"])
        if not target:
            return "UNCLOSED", f"{cell_type}.{pin}: empty port"
        # A child output bus may assemble several internal nets; classify the
        # bus as the collection of its bit sources.
        categories = Counter()
        details = []
        for inner in target:
            category, detail = classify_source(design, report, cell_type, inner, depth + 1)
            categories[category] += 1
            details.append(detail)
        return _merge(categories, details), f"{cell_type}.{pin}"
    covered = report.cells[module_name].get(cell_name, [])
    if covered:
        cuts = sorted({name for name, _ in covered})
        return "covered_cone", f"{module_name}.{cell_name} ({cell_type}) by {', '.join(cuts)}"
    structural = [label for name, label in report.structural[module_name]
                  if name == cell_name]
    if structural:
        return ("covered_cone",
                f"{module_name}.{cell_name} ({cell_type}) structural: "
                f"{', '.join(sorted(set(structural)))}")
    return "UNCLOSED", f"{module_name}.{cell_name} ({cell_type}) not in any cut cone"


def _merge(categories, details):
    if len(categories) == 1:
        return next(iter(categories))
    # Mixed bus: report the dominant category set as a joined label.
    if "UNCLOSED" in categories:
        return "UNCLOSED"
    return "+".join(sorted(categories))


def classify_leaf(design, report, row):
    module_name = row["module"]
    module = design.modules[module_name]
    port = module.get("ports", {}).get(row["leaf"])
    is_port = port is not None and port["direction"] == "input"
    sources = Counter()
    details = []
    unclosed = False
    if row["method"] == "input" or is_port:
        # A module input: resolve through every chip-top instance of this
        # module to the connected top-level nets.
        instances = []
        if module_name == TOP:
            instances = [("", tuple(module["ports"][row["leaf"]]["bits"]))]
        else:
            for cell_name, cell in design.instances.get((TOP, module_name), ()):
                instances.append((cell_name,
                                  tuple(cell["connections"].get(row["leaf"], ()))))
        if not instances:
            unclosed = True
            sources["UNCLOSED"] += 1
            details.append(f"{module_name}.{row['leaf']}: no chip-top instance")
        for instance_name, bits in instances:
            if not bits:
                unclosed = True
                sources["UNCLOSED"] += row["width"]
                details.append(f"{module_name}.{row['leaf']}: unconnected")
                continue
            for bit in bits:
                category, detail = classify_source(design, report, TOP, bit)
                if instance_name:
                    detail = f"{instance_name}: {detail}"
                sources[category] += 1
                details.append(detail)
                unclosed = unclosed or category == "UNCLOSED"
    else:
        for bit in row["bits"]:
            category, detail = classify_source(design, report, module_name, bit)
            sources[category] += 1
            details.append(detail)
            unclosed = unclosed or category == "UNCLOSED"
    row["status"] = "UNCLOSED" if unclosed else "closed"
    row["sources"] = dict(sources)
    row["details"] = _unique(details)
    return row


def _unique(items, limit=8):
    out = []
    for item in items:
        if item not in out:
            out.append(item)
        if len(out) >= limit:
            break
    return out


# --------------------------------------------------------------------------
# Instance tree and coverage

def instance_tree(design, root=TOP, path=None, depth=0):
    """Every cell occurrence in the used instance tree, with its path."""
    path = path or root
    items = []
    module = design.modules[root]
    for cell_name, cell in sorted(module.get("cells", {}).items()):
        cell_type = cell["type"]
        cell_path = f"{path}/{cell_name}"
        src = design.cell_src(root, cell_name)
        items.append({
            "path": cell_path,
            "module": root,
            "cell": cell_name,
            "type": cell_type,
            "src": src,
            "instance": design.is_instance(cell_type) and not design.is_blackbox(cell_type),
        })
        if (design.is_instance(cell_type) and not design.is_blackbox(cell_type)
                and cell_type not in BANK_CELL_TYPES and cell_type not in MACRO_TYPES):
            items.extend(instance_tree(design, cell_type, cell_path, depth + 1))
    return items


def apply_structural(report):
    """Regions the checkers verify structurally rather than by a cone.

    * bank_check.check_bank_mask checks every clock gate and latch of the bank.
    * mem_check.check_dmem and debug_check._pm_macro_check check the SRAM
      wrapper gates and the macro pin contract.
    """
    bank_module = None
    for name, module in report.design.modules.items():
        if module.get("attributes", {}).get("hdlname") == "md2_cfg_cells":
            bank_module = name
            break
    if bank_module:
        for cell_name, cell in report.design.modules[bank_module]["cells"].items():
            if cell["type"] in BANK_CELL_TYPES:
                report.structural[bank_module].append((cell_name,
                                                       "bank (structural latch/gate wiring)"))
    for name in ("md2_dmem", "md2_pmem"):
        if name in report.design.modules:
            for cell_name, cell in report.design.modules[name]["cells"].items():
                if cell["type"] in MACRO_TYPES:
                    report.structural[name].append((cell_name, "mem (SRAM macro contract)"))
                else:
                    report.structural[name].append((cell_name, "mem (macro-boundary structural check)"))
    # glue_check.emit_outputs binds each OUT/OEN register's Q bus as `cur` and
    # extracts its reset-released D cone with the table index and LUT bound as
    # leaves.  The register is proved, but `find_register` is a structural
    # lookup rather than a `cone.register`, so credit it explicitly.
    try:
        top = report.design.modules[TOP]
        for net_name in ("o_out", "o_oe"):
            bits = tuple(top["netnames"][net_name]["bits"])
            for index, bit in enumerate(bits):
                for cell_name, cell in top["cells"].items():
                    if cell["type"] == "$dff" and \
                            tuple(cell["connections"]["Q"]) == (bit,):
                        report.structural[TOP].append(
                            (cell_name, "glue (output register Q bound as cur)"))
                        report.owned[(TOP, bit)].append(
                            ("glue", f"{net_name}[{index}]"))
    except Exception:
        pass
    # debug_check.extract_reset reads rst_m/rst_q through `_adff` and proves
    # both next states.  Credit the two synchroniser registers the same way.
    try:
        top = report.design.modules[TOP]
        for net_name in ("rst_m", "rst_q"):
            bit = tuple(top["netnames"][net_name]["bits"])[0]
            for cell_name, cell in top["cells"].items():
                if cell["type"] == "$adff" and \
                        tuple(cell["connections"]["Q"]) == (bit,):
                    report.structural[TOP].append(
                        (cell_name, "debug (reset synchroniser)"))
                    report.owned[(TOP, bit)].append(("debug", net_name))
    except Exception:
        pass
    # verify.check_core_queue_top expands the arbiter `core_valid` net to the
    # leaves `cw_pending`, `~frz`, `cw_is_cfg` and requires a real `$not` on
    # `frz`; the queue proof then consumes those leaves.  The gate tree itself
    # is therefore inside the cut's checked structure.
    try:
        top = report.design.modules[TOP]
        drivers = verify.top_drivers(top)
        valid = tuple(top["cells"]["u_cfg_arb"]["connections"]["core_valid"])
        if len(valid) == 1:
            marked, seen, stack = [], set(), [valid[0]]
            frz = tuple(top["netnames"]["frz"]["bits"])
            while stack:
                bit = stack.pop()
                if bit in seen:
                    continue
                seen.add(bit)
                owners = drivers.get(bit, [])
                if len(owners) != 1:
                    continue
                cell_name, pin = owners[0]
                cell = top["cells"].get(cell_name)
                if cell is None:
                    continue
                if cell["type"] in ("$and", "$logic_and"):
                    marked.append(cell_name)
                    stack.extend(cell["connections"]["A"])
                    stack.extend(cell["connections"]["B"])
                elif cell["type"] == "$not" and \
                        tuple(cell["connections"]["A"]) == frz:
                    marked.append(cell_name)
            report.structural[TOP].extend(
                (name, "verify/corequeue (core_valid gate tree)") for name in marked)
    except Exception:
        pass


def coverage(report, items):
    design = report.design
    rows = []
    for item in items:
        module_name, cell_name = item["module"], item["cell"]
        cell_type = item["type"]
        cuts = [name for name, _ in report.cells[module_name].get(cell_name, [])]
        structural = [label for name, label in report.structural[module_name]
                      if name == cell_name]
        status = "uncovered"
        detail = ""
        if cell_type in MACRO_TYPES or (
                cell_type in design.modules and design.is_blackbox(cell_type)):
            status = "blackbox"
            detail = "SRAM macro black box (stated contract)"
        elif cuts:
            status = "covered"
            detail = ", ".join(sorted(set(cuts)))
        elif structural:
            status = "covered"
            detail = ", ".join(sorted(set(structural)))
        elif cell_type in BANK_CELL_TYPES:
            status = "covered"
            detail = "bank (library cell model)"
        elif item["instance"]:
            inner = report.cells.get(cell_type, {})
            labels = sorted({label for cells in inner.values() for label, _ in cells})
            if not labels:
                labels = sorted({label for _, label in report.structural.get(cell_type, [])})
            if labels:
                status = "covered"
                detail = "instance of a module covered by " + ", ".join(labels)
        rows.append({**item, "status": status, "detail": detail})
    return rows


# --------------------------------------------------------------------------
# Output pins

OUTPUT_PORTS = ("uo_out", "uio_out", "uio_oe")


def check_outputs(design, report):
    rows = []
    module = design.modules[TOP]
    for port_name in OUTPUT_PORTS:
        port = module["ports"][port_name]
        for index, bit in enumerate(port["bits"]):
            category, detail = classify_source(design, report, TOP, bit)
            rows.append({
                "port": port_name,
                "bit": index,
                "status": "covered" if category != "UNCLOSED" else "UNCLOSED",
                "category": category,
                "detail": detail,
            })
    return rows


# --------------------------------------------------------------------------
# Reporting

def fmt_sources(sources):
    return ", ".join(f"{name} x{count}" for name, count in
                     sorted(sources.items(), key=lambda item: (-item[1], item[0])))


def write_closure(path, rows):
    lines = ["CLOSURE: where every free leaf of every cut comes from",
             "",
             "category key: pin=top-level input pin; owned_register=register a cut",
             "proves; covered_cone=output of a cone a cut proves; bank_latch=bank",
             "latch/gate output (structural); macro=SRAM macro output (black-box",
             "contract); module_input=module port resolved at the chip top;",
             "constant=tie-off.  Any UNCLOSED bit makes the leaf UNCLOSED.",
             "A mixed bus shows its categories joined with '+'; counts are bits.",
             ""]
    unclosed = [row for row in rows if row["status"] == "UNCLOSED"]
    lines.append(f"UNCLOSED leaves: {len(unclosed)}")
    lines.append("")
    category_counts = Counter()
    for row in rows:
        for name, count in row["sources"].items():
            category_counts[name] += 1
    lines.append("Leaves by source category (a leaf may use more than one):")
    for name, count in sorted(category_counts.items(), key=lambda item: (-item[1], item[0])):
        lines.append(f"  {name:<16} {count:>4} leaves")
    lines.append("")
    if unclosed:
        for row in unclosed:
            lines.append(f"  {row['cut']}  {row['module']}.{row['leaf']} "
                         f"[{row['width']}] {fmt_sources(row['sources'])}")
            for detail in row["details"]:
                lines.append(f"      {detail}")
        lines.append("")
    lines.append("All leaves")
    lines.append(f"{'cut':<18} {'module':<44} {'leaf':<22} {'w':>3}  status  sources")
    for row in sorted(rows, key=lambda item: (item["status"] != "UNCLOSED",
                                              item["cut"], item["module"], item["leaf"])):
        lines.append(f"{row['cut']:<18} {row['module']:<44} {row['leaf']:<22} "
                     f"{row['width']:>3}  {row['status']:<8} {fmt_sources(row['sources'])}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def group_uncovered(design, rows):
    uncovered = [row for row in rows if row["status"] == "uncovered"]
    by_module = defaultdict(list)
    for row in uncovered:
        by_module[row["module"]].append(row)
    return uncovered, by_module


def write_uncovered(path, design, rows):
    uncovered, by_module = group_uncovered(design, rows)
    lines = ["UNCOVERED CELLS",
             f"{len(uncovered)} of {len(rows)} cell occurrences are not read by any "
             "cut cone and are not covered structurally.",
             ""]
    for module_name in sorted(by_module, key=lambda name: (-len(by_module[name]), name)):
        items = by_module[module_name]
        lines.append(f"== {module_name} ({len(items)} cells) ==")
        groups = OrderedDict()
        for row in sorted(items, key=lambda item: (item["src"] or ("", 0), item["cell"])):
            key = row["src"] or ("<no src>", 0)
            groups.setdefault(key, []).append(row)
        for (file, line), cells in groups.items():
            types = Counter(cell["type"] for cell in cells)
            lines.append(f"  {file}:{line}  {len(cells)} cells  "
                         f"{', '.join(f'{name} x{count}' for name, count in sorted(types.items()))}")
            for cell in cells[:40]:
                lines.append(f"      {cell['path']}  {cell['type']}")
            if len(cells) > 40:
                lines.append(f"      ... {len(cells) - 40} more")
        lines.append("")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_summary(path, report, rows, output_rows, meta):
    design = report.design
    covered = [row for row in rows if row["status"] == "covered"]
    blackbox = [row for row in rows if row["status"] == "blackbox"]
    uncovered, by_module = group_uncovered(design, rows)
    unclosed = [row for row in report.leaves if row.get("status") == "UNCLOSED"]
    total = len(rows)
    pct = 100.0 * (len(covered) + len(blackbox)) / total if total else 0.0
    lines = [
        "Metronome v4 Lean cut coverage and closure inventory",
        f"generated: {meta['generated']}",
        f"elapsed: {meta['elapsed']:.1f} s",
        f"design: {meta['commands']}",
        f"modules: {len(design.modules)}  cell occurrences: {total}",
        "",
        f"Cell coverage: {len(covered)} covered + {len(blackbox)} black-box "
        f"= {100.0 * (len(covered) + len(blackbox)) / total:.2f}% "
        f"({len(uncovered)} uncovered)",
        f"  covered by a cut cone or a structural check: {len(covered)}",
        f"  SRAM macro black boxes (stated contract): {len(blackbox)}",
        f"  uncovered: {len(uncovered)}",
        "",
        f"Free leaves: {len(report.leaves)}  UNCLOSED: {len(unclosed)}",
    ]
    for row in unclosed:
        lines.append(f"  UNCLOSED {row['cut']} {row['module']}.{row['leaf']} "
                     f"[{row['width']}] {fmt_sources(row['sources'])}")
    lines.extend([
        "",
        "Per cut",
        "cells = distinct cells read per module type; a module-level cut applies",
        "to every chip-top instance of that module.  cones = adapter instances.",
        f"{'cut':<18} {'modules':<52} {'cones':>5} {'cells':>6} {'regs':>5} {'leaves':>6}",
    ])
    for cut in report.cuts:
        modules = ", ".join(module["module"] for module in cut["modules"])
        cones = sum(module.get("cones", 0) for module in cut["modules"])
        cells = sum(module["cells"] for module in cut["modules"])
        regs = sum(len(module["registers"]) for module in cut["modules"])
        leaves = sum(len(module["leaves"]) for module in cut["modules"])
        lines.append(f"{cut['name']:<18} {modules[:52]:<52} {cones:>5} {cells:>6} "
                     f"{regs:>5} {leaves:>6}")
    lines.append("")
    lines.append("Uncovered by module")
    for module_name in sorted(by_module, key=lambda name: (-len(by_module[name]), name)):
        lines.append(f"  {module_name:<44} {len(by_module[module_name]):>5} cells")
    lines.append("")
    lines.append("Uncovered by source line (top 25)")
    by_src = Counter()
    for row in uncovered:
        file, line = row["src"] or ("<no src>", 0)
        by_src[(file, line)] += 1
    for (file, line), count in by_src.most_common(25):
        lines.append(f"  {file}:{line:<6} {count:>4} cells")
    lines.append("")
    lines.append("Output pins")
    bad_outputs = [row for row in output_rows if row["status"] != "covered"]
    lines.append(f"  {len(output_rows)} output bits; "
                 f"{len(output_rows) - len(bad_outputs)} driven by covered logic; "
                 f"{len(bad_outputs)} not")
    for row in output_rows:
        if len(output_rows) <= 24 or row["status"] != "covered":
            lines.append(f"  {row['port']}[{row['bit']}] {row['status']:<8} "
                         f"{row['category']:<16} {row['detail']}")
    lines.append("")
    if report.errors:
        lines.append("Extraction errors")
        for label, message in report.errors:
            lines.append(f"  {label}: {message}")
        lines.append("")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


# --------------------------------------------------------------------------
# Main

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--artifacts-dir", required=True,
                        help="new directory for coverage.json and the reports")
    parser.add_argument("--src", default=str(ROOT / "src"),
                        help="Verilog source directory (default: src/)")
    parser.add_argument("--yosys", default=None, help="yosys executable")
    parser.add_argument("--timeout", type=int, default=300,
                        help="Yosys elaboration timeout in seconds")
    parser.add_argument("--strict", action="store_true",
                        help="exit 1 if any leaf is UNCLOSED or any non-black-box "
                             "cell is uncovered")
    parser.add_argument("--only", default=None,
                        help="debug: comma-separated cut names (default: all)")
    parser.add_argument("--quiet", action="store_true",
                        help="do not print per-cut progress to stderr")
    args = parser.parse_args(argv)
    only = set(args.only.split(",")) if args.only else None

    def progress(message):
        if not args.quiet:
            print(message, file=sys.stderr, flush=True)

    out = Path(args.artifacts_dir)
    if out.exists():
        raise SystemExit(f"{out}: artifacts directory already exists")
    yosys = args.yosys or shutil.which("yosys")
    if not yosys:
        raise SystemExit("yosys not on PATH; add the OSS CAD Suite to PATH")

    started = time.time()
    snapshot = snapshot_of(args.src)
    import tempfile
    instrument()
    report = None
    commands = ""
    tool_logs = [f"python: {platform.python_version()} ({sys.executable})",
                 f"platform: {platform.platform()}",
                 f"yosys version: {yosys_version(yosys, args.timeout)}",
                 f"src: {Path(args.src).resolve()}",
                 f"defines: {' '.join(SRAM_DEFINES)}"]
    with tempfile.TemporaryDirectory(prefix="metronome-coverage-") as tmp:
        modules, commands, tool_log = elaborate(snapshot, Path(tmp) / "rtl",
                                                yosys, args.timeout)
        tool_logs.append(tool_log)
        design = Design(modules)
        report = Report(design)
        progress(f"elaborated: {len(modules)} modules, "
                 f"{sum(len(m.get('cells', {})) for m in modules.values())} module cells")

        global EVENTS
        for cut in CUTS:
            if only is not None and cut["name"] not in only:
                continue
            begin = time.time()
            progress(f"[cut] {cut['name']} ...")
            EVENTS = []
            try:
                extraction = cut["run"](design, snapshot)
            except Exception as exc:
                report.errors.append((cut["name"],
                                      f"{type(exc).__name__}: {exc}"))
                tool_logs.append(
                    f"-- {cut['name']}: extraction failed\n{traceback.format_exc()}")
                EVENTS = None
                progress(f"[cut] {cut['name']} FAILED: {exc}")
                continue
            events = EVENTS
            EVENTS = None
            try:
                process_cut(design, report, cut["name"], events, extraction)
            except Exception as exc:  # pragma: no cover - defensive
                report.errors.append((cut["name"], f"walk: {exc}"))
                tool_logs.append(f"-- {cut['name']}: walk failed\n{traceback.format_exc()}")
            progress(f"[cut] {cut['name']} done in {time.time() - begin:.1f} s")

        progress("[phase] structural credit")
        apply_structural(report)
        progress("[phase] closure classification")
        for index, row in enumerate(report.leaves):
            classify_leaf(design, report, row)
            if index % 100 == 0:
                progress(f"  leaves {index}/{len(report.leaves)}")
        progress("[phase] instance tree")
        items = instance_tree(design)
        progress(f"  {len(items)} cell occurrences")
        coverage_rows = coverage(report, items)
        progress("[phase] output pins")
        output_rows = check_outputs(design, report)

    out.mkdir(parents=True)
    elapsed = time.time() - started
    meta = {"generated": time.strftime("%Y-%m-%d %H:%M:%S"), "elapsed": elapsed,
            "commands": commands}

    covered = [row for row in coverage_rows if row["status"] == "covered"]
    blackbox = [row for row in coverage_rows if row["status"] == "blackbox"]
    uncovered, by_module = group_uncovered(design, coverage_rows)
    unclosed = [row for row in report.leaves if row.get("status") == "UNCLOSED"]

    payload = {
        "generated": meta["generated"],
        "elapsed_s": round(elapsed, 2),
        "commands": commands,
        "defines": list(SRAM_DEFINES),
        "modules": len(design.modules),
        "counts": {
            "cell_occurrences": len(coverage_rows),
            "covered": len(covered),
            "blackbox": len(blackbox),
            "uncovered": len(uncovered),
            "coverage_percent": round(100.0 * (len(covered) + len(blackbox)) /
                                      max(len(coverage_rows), 1), 3),
            "leaves": len(report.leaves),
            "unclosed": len(unclosed),
        },
        "cuts": report.cuts,
        "closure": [{key: value for key, value in row.items() if key != "bits"}
                    for row in report.leaves],
        "uncovered": [{
            "path": row["path"], "module": row["module"], "cell": row["cell"],
            "type": row["type"], "src": row["src"],
        } for row in uncovered],
        "coverage": [{
            "path": row["path"], "module": row["module"], "cell": row["cell"],
            "type": row["type"], "status": row["status"], "detail": row["detail"],
        } for row in coverage_rows],
        "outputs": output_rows,
        "errors": report.errors,
    }
    (out / "coverage.json").write_text(json.dumps(payload, indent=2) + "\n",
                                      encoding="utf-8")
    write_closure(out / "closure.txt", report.leaves)
    write_uncovered(out / "uncovered.txt", design, coverage_rows)
    write_summary(out / "summary.txt", report, coverage_rows, output_rows, meta)
    tool_logs.append(f"elapsed: {elapsed:.1f} s")
    (out / "tools.log").write_text("\n".join(tool_logs) + "\n", encoding="utf-8")

    print(f"coverage: {payload['counts']['coverage_percent']:.2f}% by cell "
          f"({len(covered)} covered, {len(blackbox)} black-box, "
          f"{len(uncovered)} uncovered of {len(coverage_rows)})")
    print(f"closure: {len(report.leaves)} free leaves, {len(unclosed)} UNCLOSED")
    print(f"output pins: {sum(1 for row in output_rows if row['status'] == 'covered')}"
          f"/{len(output_rows)} bits driven by covered logic")
    print(f"artifacts: {out}")
    if report.errors:
        print("extraction errors:", file=sys.stderr)
        for label, message in report.errors:
            print(f"  {label}: {message}", file=sys.stderr)
        return 2
    if args.strict and (unclosed or uncovered):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
