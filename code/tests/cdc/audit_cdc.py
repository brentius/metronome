"""Structural CDC audit of tt_um_brentius_metronome (SPEC V2 section 1-2).

Elaborates the v2 RTL with Yosys (``proc; opt; opt_clean``, the same source list and defines as the lockstep bench)
and proves, from the resulting netlist:

  RAW_FANOUT       every bit of ``ui_in``/``uio_in`` loads exactly one pin: the D input of its first-stage flop
                   (register ``s1``), in the documented bit order.  No other load exists (no comb cell, no second
                   flop, no output port, no submodule port).
  SYNC_CHAIN       ``s1`` loads only ``s2``'s D input; ``s2`` feeds ``sp`` bit for bit and may drive logic.
  RSTN_FANOUT      ``rst_n`` reaches exactly the two async reset pins of the reset synchroniser (``rst_m``,
                   ``rst_q``) and nothing else - no combinational cell at all.
  RESET_NETS       the synchronised resets (``rst_q`` at the top, plus every submodule port named ``rst_n``/
                   ``rst_s`` and the whitelisted cell-model async-clear ports) reach only reset pins: async reset
                   (``ARST``), synchronous reset (``SRST``), latch async clear, or a reset pin of a submodule.
                   Combinational cones are followed; a cone is allowed only if every terminal is a reset pin.
                   ``$print``-style observation sinks are allowed and reported separately.
  NO_RAW_COMB_PATH no ``ui_in``/``uio_in``/``rst_n``/``ena`` bit has a combinational path to any output port, nor
                   into a transparent (latch) element.

Fail-closed: any cell type, sequential pin or module without an explicit rule raises ``AuditError`` and the audit
fails.  The JSON netlist is inspected module by module; cell instances of design/sub-cell modules are described by
their own module definition (hierarchical combinational reachability), never assumed opaque.

CLI:
    python code/tests/cdc/audit_cdc.py [--src DIR] [--json-out FILE]
Exit code 0 = all checks passed.
"""
from __future__ import annotations

import argparse
import collections
import json
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LOCKSTEP = ROOT / "code/tests/lockstep_v2"
if str(LOCKSTEP) not in sys.path:
    sys.path.insert(0, str(LOCKSTEP))

import rtl_sources  # noqa: E402  (source list shared with the lockstep bench)

TOP = "tt_um_brentius_metronome"
RAW_INPUTS = {"uio_in": 8, "ui_in": 8}          # s1 order: {ui_in, uio_in}
RAW_NETS = ("ui_in", "uio_in", "rst_n", "ena")
OUTPUT_PORTS = ("uo_out", "uio_out", "uio_oe")
SYNC_REGS = (("s1", "s2"), ("s2", "sp"))


# ---------------------------------------------------------------------------------------------------- classifications
# Combinational Yosys cells: any input bit may influence any output bit (conservative all-to-all).
COMB_CELLS = frozenset({
    "$not", "$pos", "$neg", "$and", "$or", "$xor", "$xnor", "$bwmux", "$bweqx",
    "$reduce_and", "$reduce_or", "$reduce_xor", "$reduce_xnor", "$reduce_bool",
    "$logic_not", "$logic_and", "$logic_or", "$eq", "$eqx", "$ne", "$nex",
    "$lt", "$le", "$gt", "$ge", "$add", "$sub", "$mul", "$div", "$mod", "$pow",
    "$shl", "$shr", "$sshl", "$sshr", "$shift", "$shiftx", "$mux", "$pmux",
    "$lut", "$concat", "$slice", "$memrd", "$sop", "$alu", "$fa", "$lcu", "$tribuf", "$buf",
})

# Sequential cells: pin -> role.  Anything not listed raises (fail-closed).
SEQ_CELLS = {
    "$dff":     {"CLK": "clock", "D": "data"},
    "$dffe":    {"CLK": "clock", "D": "data", "EN": "enable"},
    "$sdff":    {"CLK": "clock", "D": "data", "SRST": "sync_reset"},
    "$sdffe":   {"CLK": "clock", "D": "data", "EN": "enable", "SRST": "sync_reset"},
    "$adff":    {"CLK": "clock", "D": "data", "ARST": "async_reset"},
    "$adffe":   {"CLK": "clock", "D": "data", "EN": "enable", "ARST": "async_reset"},
    "$aldff":   {"CLK": "clock", "D": "data", "ALOAD": "async_reset", "AD": "async_reset_data"},
    "$aldffe":  {"CLK": "clock", "D": "data", "EN": "enable", "ALOAD": "async_reset", "AD": "async_reset_data"},
    "$dffsr":   {"CLK": "clock", "D": "data", "SET": "async_set", "CLR": "async_reset"},
    "$dlatch":  {"EN": "enable", "D": "data"},
    "$adlatch": {"EN": "enable", "D": "data", "ARST": "async_reset"},
    "$dlatchsr": {"EN": "enable", "D": "data", "SET": "async_set", "CLR": "async_reset"},
    "$sr":      {"SET": "async_set", "CLR": "async_reset"},
}
LATCH_CELLS = frozenset({"$dlatch", "$adlatch", "$dlatchsr"})
SINK_CELLS = frozenset({"$print", "$check", "$assert", "$assume", "$cover", "$finish", "$stop", "$display"})
SOURCE_CELLS = frozenset({"$anyseq", "$anyconst", "$allseq", "$allconst", "$random", "$time"})
NO_OBS_CELLS = frozenset({"$memwr_v2", "$meminit_v2", "$mem_v2"})   # state/init cells: no combinational output

RESET_PORTS = frozenset({"rst_n", "rst_s"})
# Behavioural cell models whose ports have a fixed role.  RESET_B is the async clear of the library latch
# (sg13cmos5l_dlhrq_1) and is verified to reach only the latch's async reset pin.
CELL_MODELS = {
    "cfg_dlhrq_beh": {"D": "data", "GATE": "enable", "RESET_B": "async_clear", "Q": "output"},
    "cfg_lgcp_beh": {"CLK": "clock", "GATE": "enable", "GCLK": "output"},
}
RESET_TERMINALS = frozenset({"async_reset", "sync_reset", "async_clear", "reset_port", "async_set"})


class AuditError(RuntimeError):
    """The audit cannot make a statement (unknown cell type, missing register, Yosys failure)."""


@dataclass(frozen=True)
class Pin:
    inst: str | None          # None: a port of the module under analysis
    port: str
    bit: int

    def label(self, module: "Module") -> str:
        if self.inst is None:
            return f"{self.port}[{self.bit}]"
        cell = module.cells[self.inst]
        if cell["type"] in CELL_MODELS:
            return f"{self.inst}.{self.port}"
        width = len(cell["connections"].get(self.port, []))
        return f"{self.inst}.{self.port}[{self.bit}]" if width > 1 else f"{self.inst}.{self.port}"


@dataclass
class Finding:
    check: str
    detail: str

    def __str__(self) -> str:
        return f"[{self.check}] {self.detail}"


@dataclass
class Module:
    name: str
    raw: dict
    known: set[str] = field(default_factory=set)      # every module name in the design
    loads: dict = field(default_factory=lambda: collections.defaultdict(list))
    drivers: dict = field(default_factory=lambda: collections.defaultdict(list))
    netnames: dict[int, list[str]] = field(default_factory=dict)

    @property
    def ports(self) -> dict:
        return self.raw["ports"]

    @property
    def cells(self) -> dict:
        return self.raw["cells"]

    def port_net(self, name: str, bit: int = 0) -> int:
        return self.ports[name]["bits"][bit]

    def net_label(self, net: int) -> str:
        names = self.netnames.get(net, [])
        return names[0] if names else f"${net}"

    def net_bits(self, name: str) -> list[int]:
        for candidate in (name, f"${name}", f"\\{name}"):
            if candidate in self.raw["netnames"]:
                return list(self.raw["netnames"][candidate]["bits"])
        raise AuditError(f"{self.name}: no net named {name!r} (registers renamed?)")

    def cell_output_nets(self, inst: str, port: str | None = None) -> list[int]:
        cell = self.cells[inst]
        direction = cell["port_directions"]
        nets: list[int] = []
        for pname, bits in cell["connections"].items():
            if direction.get(pname) != "output":
                continue
            if port is not None and pname != port:
                continue
            nets.extend(b for b in bits if isinstance(b, int))
        return nets


def _build_module(name: str, raw: dict) -> Module:
    m = Module(name, raw)
    for net, names in raw["netnames"].items():
        for bit in names["bits"]:
            m.netnames.setdefault(bit, []).append(net)
    for pname, pdata in raw["ports"].items():
        for i, bit in enumerate(pdata["bits"]):
            if not isinstance(bit, int):
                continue
            pin = Pin(None, pname, i)
            (m.drivers if pdata["direction"] == "input" else m.loads)[bit].append(pin)
    for inst, cell in raw["cells"].items():
        for pname, bits in cell["connections"].items():
            direction = cell["port_directions"].get(pname)
            for i, bit in enumerate(bits):
                if not isinstance(bit, int):
                    continue
                pin = Pin(inst, pname, i)
                (m.drivers if direction == "output" else m.loads)[bit].append(pin)
    # Prefer non-generated names for diagnostics.
    for bit, names in m.netnames.items():
        names.sort(key=lambda n: (n.startswith("$"), len(n)))
    return m


def cell_class(module: Module, cell_type: str) -> str:
    """comb / dff / latch / sink / source / module / cellmodel; unknown types raise."""
    if cell_type in CELL_MODELS:
        return "cellmodel"
    if cell_type in SEQ_CELLS:
        return "dff"
    if cell_type in COMB_CELLS:
        return "comb"
    if cell_type in SINK_CELLS:
        return "sink"
    if cell_type in SOURCE_CELLS:
        return "source"
    if cell_type in NO_OBS_CELLS:
        return "sink"
    if cell_type in module.known:
        return "module"
    raise AuditError(f"{module.name}: unknown cell type {cell_type!r} (fail-closed)")


def is_reset_port(module: Module, port: str) -> bool:
    if module.name in CELL_MODELS:
        return CELL_MODELS[module.name].get(port) == "async_clear"
    return port in RESET_PORTS


@dataclass
class Report:
    passed: bool = True
    findings: list[Finding] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)
    sections: dict[str, list[str]] = field(default_factory=dict)

    def fail(self, check: str, detail: str) -> None:
        self.passed = False
        self.findings.append(Finding(check, detail))

    def note(self, section: str, text: str) -> None:
        self.sections.setdefault(section, []).append(text)

    def as_dict(self) -> dict:
        return {"passed": self.passed, "findings": [f.__dict__ for f in self.findings],
                "notes": self.notes, "sections": self.sections}

    def text(self) -> str:
        lines = [f"structural CDC audit: {'PASS' if self.passed else 'FAIL'}"]
        for section, items in self.sections.items():
            lines.append(f"\n## {section}")
            lines.extend(f"  {i}" for i in items)
        for note in self.notes:
            lines.append(f"note: {note}")
        if self.findings:
            lines.append("\n## findings")
            lines.extend(f"  {f}" for f in self.findings)
        return "\n".join(lines)


class Audit:
    def __init__(self, netlist_json: Path, note: str | None = None):
        data = json.loads(Path(netlist_json).read_text(encoding="utf-8"))
        self.modules = {name: _build_module(name, raw) for name, raw in data["modules"].items()}
        if TOP not in self.modules:
            raise AuditError(f"top module {TOP} not found in {netlist_json}")
        for module in self.modules.values():
            module.known = set(self.modules)
        self.report = Report()
        self.note = note
        self._comb_dep: dict[str, dict[tuple[str, int], set[tuple[str, int]]]] = {}

    # ---------------------------------------------------------------------------------------------- helpers
    def check_cell_types(self) -> None:
        unknown = collections.Counter()
        for module in self.modules.values():
            for inst, cell in module.cells.items():
                try:
                    cls = cell_class(module, cell["type"])
                except AuditError as exc:
                    unknown[str(exc)] += 1
                    continue
                if cls == "dff":
                    for pname, direction in cell["port_directions"].items():
                        if direction == "input" and pname not in SEQ_CELLS[cell["type"]]:
                            unknown[f"{module.name}: {inst} ({cell['type']}) has unmapped input pin {pname}"] += 1
                elif cls in ("cellmodel", "comb", "sink", "source", "module"):
                    pass
        for msg, count in sorted(unknown.items()):
            self.report.fail("CELL_TYPES", f"{msg}" + (f" x{count}" if count > 1 else ""))
        if not unknown:
            types = sorted({c["type"] for m in self.modules.values() for c in m.cells.values()})
            self.report.note("audit", f"cell types classified: {len(types)} distinct, none unknown")
            modules = sorted(self.modules)
            self.report.note("audit", f"{len(modules)} modules elaborate"
                                      + (f"; {self.note}" if self.note else ""))

    def register_for(self, module: Module, netname: str) -> tuple[str, dict]:
        """The single dff-family cell whose Q drives the net named `netname`."""
        bits = set(module.net_bits(netname))
        hits = []
        for inst, cell in module.cells.items():
            cls = cell_class(module, cell["type"])
            if cls == "dff" and bits & set(module.cell_output_nets(inst)):
                hits.append((inst, cell))
        if len(hits) != 1:
            raise AuditError(f"{module.name}: expected exactly one flop for {netname!r}, found "
                             f"{[h[0] + ':' + h[1]['type'] for h in hits]}")
        inst, cell = hits[0]
        q = module.net_bits(netname)
        if cell["connections"].get("Q") != q or any(
                module.drivers.get(net) != [Pin(inst, "Q", k)] for k, net in enumerate(q)):
            raise AuditError(f"{module.name}: {netname!r} must be driven bit-for-bit by {inst}.Q alone")
        return inst, cell

    def seq_role(self, module: Module, inst: str, port: str) -> str:
        cell = module.cells[inst]
        cls = cell_class(module, cell["type"])
        table = SEQ_CELLS[cell["type"]] if cls == "dff" else CELL_MODELS[cell["type"]]
        if port not in table:
            raise AuditError(f"{module.name}: {inst} ({cell['type']}) pin {port} has no role rule")
        return table[port]

    def comb_input_to_output(self, module: Module, stack: tuple[str, ...] = ()) -> dict[tuple[str, int], set[tuple[str, int]]]:
        """For every input-port bit, the set of output-port bits reachable through combinational cells only.

        Sequential cells, latches and sinks terminate a path.  Instance ports are resolved through the callee's
        own relation (cached), so this is a real hierarchical combinational reachability, not an assumption.
        """
        if module.name in self._comb_dep:
            return self._comb_dep[module.name]
        if module.name in stack:
            raise AuditError(f"recursive instantiation of {module.name} (cannot analyse)")
        rel: dict[tuple[str, int], set[tuple[str, int]]] = {}
        out_ports = {name for name, d in module.ports.items() if d["direction"] == "output"}
        for in_name, pdata in module.ports.items():
            if pdata["direction"] != "input":
                continue
            for i, start in enumerate(pdata["bits"]):
                if not isinstance(start, int):
                    continue
                seen: set[int] = set()
                queue = [start]
                reached: set[tuple[str, int]] = set()
                while queue:
                    net = queue.pop()
                    if net in seen:
                        continue
                    seen.add(net)
                    for pin in module.loads.get(net, ()):
                        if pin.inst is None:
                            if pin.port in out_ports:
                                reached.add((pin.port, pin.bit))
                            continue
                        cell = module.cells[pin.inst]
                        cls = cell_class(module, cell["type"])
                        if cls == "comb":
                            queue.extend(module.cell_output_nets(pin.inst))
                        elif cls == "module":
                            sub = self.modules[cell["type"]]
                            subrel = self.comb_input_to_output(sub, stack + (module.name,))
                            for out_name, out_bit in subrel.get((pin.port, pin.bit), ()):
                                for j, net2 in enumerate(cell["connections"].get(out_name, [])):
                                    if j == out_bit and isinstance(net2, int):
                                        queue.append(net2)
                        elif cls == "cellmodel":
                            subrel = self.comb_input_to_output(self.modules[cell["type"]],
                                                              stack + (module.name,))
                            for out_name, out_bit in subrel.get((pin.port, pin.bit), ()):
                                for j, net2 in enumerate(cell["connections"].get(out_name, [])):
                                    if j == out_bit and isinstance(net2, int):
                                        queue.append(net2)
                        # dff / latch / sink / source terminate
                rel[(in_name, i)] = reached
        self._comb_dep[module.name] = rel
        return rel

    # ---------------------------------------------------------------------------------------------- RAW_FANOUT
    def check_raw_fanout(self) -> None:
        top = self.modules[TOP]
        s1_inst, s1 = self.register_for(top, "s1")
        s1_q = top.net_bits("s1")
        s1_d = list(s1["connections"]["D"])
        if s1["type"] not in ("$dff", "$sdff"):
            self.report.fail("RAW_FANOUT", f"s1 is a {s1['type']}, not a plain flop")
        if len(s1_q) != 16 or len(s1_d) != 16:
            self.report.fail("RAW_FANOUT", f"s1 width {len(s1_q)} (expected 16)")
            return
        if (s1["connections"].get("CLK") != [top.port_net("clk")] or
                int(s1["parameters"]["CLK_POLARITY"], 2) != 1):
            self.report.fail("RAW_FANOUT", "s1 is not clocked by the rising edge of clk")
        if s1["connections"].get("SRST") or s1["connections"].get("ARST"):
            self.report.note("RAW_FANOUT", f"s1 has a reset {(s1['connections'].get('SRST') or s1['connections'].get('ARST'))} "
                                            "(synchronous reset through rst_q; not the raw pin)")

        expected = [("uio_in", i) for i in range(8)] + [("ui_in", i) for i in range(8)]
        for k, (port, bit) in enumerate(expected):
            net = top.port_net(port, bit)
            if s1_d[k] != net:
                self.report.fail("RAW_FANOUT", f"s1 D bit {k} is driven by {top.net_label(s1_d[k])}, "
                                               f"expected {port}[{bit}]")
                continue
            loads = top.loads.get(net, [])
            unexpected = [p for p in loads if not (p.inst == s1_inst and p.port == "D" and p.bit == k)]
            if not any(p.inst == s1_inst and p.port == "D" and p.bit == k for p in loads):
                self.report.fail("RAW_FANOUT", f"{port}[{bit}] does not load s1 D bit {k}")
            for pin in unexpected:
                where = pin.label(top)
                self.report.fail("RAW_FANOUT", f"{port}[{bit}] has an extra load: {where}"
                                               f" ({top.cells[pin.inst]['type']})" if pin.inst else
                                               f"{port}[{bit}] drives port {where}")
            drivers = top.drivers.get(net, [])
            if drivers != [Pin(None, port, bit)]:
                self.report.fail("RAW_FANOUT", f"{port}[{bit}] net has unexpected drivers: "
                                               f"{[p.label(top) for p in drivers]}")
        if self.report.passed:
            self.report.note("RAW_FANOUT", f"all 16 raw input bits (uio_in[7:0], ui_in[7:0]) drive only the "
                                           f"{s1['type']} {s1_inst} D inputs, in order "
                                           f"s1[k]=raw[k] (raw = {{ui_in, uio_in}})")

    # ---------------------------------------------------------------------------------------------- SYNC_CHAIN
    def check_sync_chain(self) -> None:
        top = self.modules[TOP]
        for src, dst in SYNC_REGS:
            self.register_for(top, src)
            dst_inst, dst_cell = self.register_for(top, dst)
            if (dst_cell["type"] not in ("$dff", "$sdff") or
                    dst_cell["connections"].get("CLK") != [top.port_net("clk")] or
                    int(dst_cell["parameters"]["CLK_POLARITY"], 2) != 1):
                self.report.fail("SYNC_CHAIN", f"{dst} is not an ungated positive-edge clk flop")
            q = top.net_bits(src)
            d = list(dst_cell["connections"]["D"])
            if len(q) != len(d):
                self.report.fail("SYNC_CHAIN", f"{src} width {len(q)} != {dst} width {len(d)}")
                continue
            for k, net in enumerate(q):
                if d[k] != net:
                    self.report.fail("SYNC_CHAIN", f"{dst} D bit {k} is driven by {top.net_label(d[k])}, "
                                                   f"expected {src}[{k}]")
                # only the first stage must have no other load; s2 is the copy functional logic uses
                if src == "s1":
                    loads = top.loads.get(net, [])
                    unexpected = [p for p in loads if not (p.inst == dst_inst and p.port == "D" and p.bit == k)]
                    for pin in unexpected:
                        self.report.fail("SYNC_CHAIN", f"{src}[{k}] has an extra load: {pin.label(top)}")
            extra = "" if src == "s1" else f"; {sum(len(top.loads.get(n, ())) for n in q) - len(q)} other loads allowed"
            self.report.note("SYNC_CHAIN", f"{src} -> {dst}: {len(q)} bits, bit-to-bit{extra}")
        sp_q = top.net_bits("sp")
        n = sum(len(top.loads.get(net, [])) for net in sp_q)
        self.report.note("SYNC_CHAIN", f"sp (third stage) has {n} loads")

    # ---------------------------------------------------------------------------------------------- resets
    def reset_closure(self, module: Module, nets: list[int]) -> tuple[list[tuple[Pin, str]], int, int]:
        """All terminals reachable from `nets` through combinationally-transparent cells.

        Returns (terminals with category, number of comb cells traversed, number of transparent latches entered).
        """
        seen: set[int] = set()
        queue = list(nets)
        terms: list[tuple[Pin, str]] = []
        comb_cells = 0
        latch_entries = 0
        while queue:
            net = queue.pop()
            if net in seen:
                continue
            seen.add(net)
            for pin in module.loads.get(net, ()):
                if pin.inst is None:
                    terms.append((pin, "output_port"))
                    continue
                cell = module.cells[pin.inst]
                cls = cell_class(module, cell["type"])
                if cls == "dff":
                    role = self.seq_role(module, pin.inst, pin.port)
                    terms.append((pin, role))
                elif cls == "latch":
                    latch_entries += 1
                    terms.append((pin, "latch_data"))
                elif cls == "comb":
                    comb_cells += 1
                    queue.extend(module.cell_output_nets(pin.inst))
                elif cls == "cellmodel":
                    role = self.seq_role(module, pin.inst, pin.port)
                    terms.append((pin, "async_clear" if role == "async_clear" else role))
                elif cls == "module":
                    sub = self.modules[cell["type"]]
                    terms.append((pin, "reset_port" if is_reset_port(sub, pin.port) else "module_data"))
                elif cls == "sink":
                    terms.append((pin, "sink"))
                elif cls == "source":
                    terms.append((pin, "source"))
                else:                                    # pragma: no cover - cell_class raises first
                    raise AuditError(f"unclassified {cell['type']}")
        return terms, comb_cells, latch_entries

    def check_reset(self) -> None:
        top = self.modules[TOP]
        rstn = top.port_net("rst_n")
        terms, comb_cells, latch_entries = self.reset_closure(top, [rstn])
        async_only = [p for p, role in terms if role == "async_reset"]
        bad = [(p, role) for p, role in terms if role != "async_reset"]
        if comb_cells or latch_entries or bad:
            for pin, role in bad:
                self.report.fail("RSTN_FANOUT", f"rst_n reaches {pin.label(top)} as {role}")
            if comb_cells:
                self.report.fail("RSTN_FANOUT", f"rst_n traverses {comb_cells} combinational cell input(s)")
        # exactly the two reset-synchroniser flops, active low
        sync_names = []
        for name, expected_d in (("rst_m", ["1"]), ("rst_q", top.net_bits("rst_m"))):
            inst, cell = self.register_for(top, name)
            sync_names.append((name, inst, cell))
            arst = cell["connections"].get("ARST")
            polarity = cell["parameters"].get("ARST_POLARITY")
            ok = arst == [rstn] and isinstance(polarity, str) and int(polarity, 2) == 0
            if not ok:
                self.report.fail("RSTN_FANOUT", f"{name} is not an active-low async-reset flop on rst_n: "
                                                 f"ARST={arst} polarity={polarity}")
            if (cell["type"] != "$adff" or cell["connections"].get("D") != expected_d or
                    cell["connections"].get("CLK") != [top.port_net("clk")] or
                    int(cell["parameters"]["CLK_POLARITY"], 2) != 1 or
                    int(cell["parameters"]["ARST_VALUE"], 2) != 0):
                self.report.fail("RSTN_FANOUT", f"{name} does not clear to 0 and shift a 1 on rising clk")
        got = sorted({pin.inst for pin in async_only})
        want = sorted({inst for _, inst, _ in sync_names})
        if got != want:
            self.report.fail("RSTN_FANOUT", f"rst_n reaches {got}, expected exactly the reset synchroniser {want}")
        if not bad and not comb_cells and not latch_entries and got == want:
            names = {inst: name for name, inst, _ in sync_names}
            self.report.note("RSTN_FANOUT", f"rst_n reaches exactly {len(terms)} pins: "
                                            f"{', '.join(f'{names[p.inst]}.ARST (active low, {p.inst})' for p in async_only)}; "
                                            "no combinational cell, latch, data pin or output port")
        self.report.note("RSTN_FANOUT", "config latches (cfg_dlhrq_beh async clear) are cleared by the synchronised "
                                        "rise-through of rst_q, not by the raw pin (see RESET_NETS)")

        # derived resets: top rst_q and every module reset input port
        targets: list[tuple[Module, str]] = [(top, "rst_q")]
        for name, module in sorted(self.modules.items()):
            for port in module.ports:
                if module.ports[port]["direction"] == "input" and is_reset_port(module, port):
                    if name == TOP and port == "rst_n":
                        continue                     # the raw pin itself, checked above
                    targets.append((module, port))
        for module, port in targets:
            net = module.net_bits(port) if port != "rst_q" else module.net_bits("rst_q")
            terms, comb_cells, latch_entries = self.reset_closure(module, net)
            groups: collections.Counter = collections.Counter()
            bad = []
            for pin, role in terms:
                if role in RESET_TERMINALS:
                    cell = module.cells.get(pin.inst) if pin.inst else None
                    pol = ""
                    if cell is not None:
                        for key, value in cell["parameters"].items():
                            if key.endswith("POLARITY") and (role == "sync_reset" and key.startswith("SRST")
                                                             or role == "async_reset" and key.startswith("ARST")):
                                pol = f", {'active low' if int(value, 2) == 0 else 'active high'}"
                    groups[(role, cell["type"] if cell else pin.port, pol)] += 1
                elif role == "sink":
                    groups[("observe-only", module.cells[pin.inst]["type"], "")] += 1
                else:
                    bad.append((pin, role))
            for pin, role in bad:
                self.report.fail("RESET_NETS", f"{module.name}.{port} reaches {pin.label(module)} as {role}")
            detail = ", ".join(f"{count}x {kind}{typ and ' ' + typ}{pol}"
                               for (kind, typ, pol), count in sorted(groups.items()))
            self.report.note("RESET_NETS", f"{module.name}.{port}: {detail or 'no loads'}"
                                           + (f"; via {comb_cells} comb cell(s)" if comb_cells else ""))

    # ---------------------------------------------------------------------------------------------- comb paths
    def raw_trace(self, start_net: int) -> tuple[list[Pin], list[Pin]]:
        """Combinational reach from one net in the top module: (output-port pins, transparent-latch pins)."""
        top = self.modules[TOP]
        dep = self.comb_input_to_output(top)
        seen: set[int] = set()
        queue = [start_net]
        outputs: list[Pin] = []
        latches: list[Pin] = []
        while queue:
            net = queue.pop()
            if net in seen:
                continue
            seen.add(net)
            for pin in top.loads.get(net, ()):
                if pin.inst is None:
                    if pin.port in OUTPUT_PORTS:
                        outputs.append(pin)
                    continue
                cell = top.cells[pin.inst]
                cls = cell_class(top, cell["type"])
                if cls == "comb":
                    queue.extend(top.cell_output_nets(pin.inst))
                elif cls == "latch":
                    latches.append(pin)
                elif cls in ("module", "cellmodel"):
                    sub = self.modules[cell["type"]]
                    subrel = self.comb_input_to_output(sub, (TOP,))
                    for out_name, out_bit in subrel.get((pin.port, pin.bit), ()):
                        for j, net2 in enumerate(cell["connections"].get(out_name, [])):
                            if j == out_bit and isinstance(net2, int):
                                queue.append(net2)
                # dff / sink / source terminate
        return outputs, latches

    def check_no_raw_comb_path(self) -> None:
        top = self.modules[TOP]
        for port in RAW_NETS:
            if port not in top.ports:
                continue
            for i in range(len(top.ports[port]["bits"])):
                outputs, latches = self.raw_trace(top.port_net(port, i))
                for pin in outputs:
                    self.report.fail("NO_RAW_COMB_PATH", f"{port}[{i}] reaches output port {pin.label(top)} "
                                                         "combinationally")
                for pin in latches:
                    self.report.fail("NO_RAW_COMB_PATH",
                                     f"{port}[{i}] reaches transparent latch pin {pin.label(top)}")
        if not any(f.check == "NO_RAW_COMB_PATH" for f in self.report.findings):
            self.report.note("NO_RAW_COMB_PATH", "ui_in, uio_in, rst_n and ena have no combinational path to "
                                                 "uo_out/uio_out/uio_oe and reach no transparent latch")

    # ---------------------------------------------------------------------------------------------- driver
    def run(self) -> Report:
        self.check_cell_types()
        self.check_raw_fanout()
        self.check_sync_chain()
        self.check_reset()
        self.check_no_raw_comb_path()
        return self.report


# ---------------------------------------------------------------------------------------------------- Yosys driver
def yosys_bin() -> str:
    exe = shutil.which("yosys")
    if exe:
        return exe
    suite = Path(os.environ.get("OSS_CAD_SUITE", r"C:\Users\b_yee23\tools\oss-cad-suite"))
    for candidate in (suite / "bin/yosys.exe", suite / "bin/yosys"):
        if candidate.exists():
            return str(candidate)
    raise AuditError("yosys not found (source code/tools/env.sh or set OSS_CAD_SUITE)")


def source_files(src: Path, ihp_sram: bool = True) -> tuple[list[Path], dict[str, int]]:
    files = [Path(src) / name for name in rtl_sources.SOURCES]
    missing = [str(f) for f in files if not f.exists()]
    if missing:
        raise AuditError(f"missing RTL sources: {missing}")
    defines = {"SIM": 1, "COCOTB_SIM": 1}
    if ihp_sram:
        files = list(rtl_sources.SRAM_MODEL) + files
        defines.update({"FUNCTIONAL": 1, "USE_IHP_SRAM": 1})
    return files, defines


def elaborate(src: Path, out_json: Path, ihp_sram: bool = True, keep: bool = False) -> Path:
    """Run Yosys and write the JSON netlist used by the audit.

    Sources are staged in a scratch directory with bare file names: Yosys's script parser splits `-I`/file arguments
    on spaces, and this repository's path contains one.
    """
    files, defines = source_files(src, ihp_sram)
    yosys = yosys_bin()
    env = dict(os.environ)
    env_lib = str(Path(yosys).parent.parent / "lib")
    if Path(env_lib).is_dir():
        env["PATH"] = env_lib + os.pathsep + env.get("PATH", "")
    with tempfile.TemporaryDirectory(prefix="cdc_audit_") as work:
        stage = Path(work) / "src"
        stage.mkdir()
        names = []
        for f in files:
            target = stage / Path(f).name
            if target.exists() and target.resolve() != Path(f).resolve():
                raise AuditError(f"duplicate source basename {Path(f).name}")
            shutil.copyfile(f, target)
            names.append(Path(f).name)
        headers = sorted(Path(src).glob("*.vh")) + sorted(Path(src).glob("*.svh"))
        for header in headers:
            shutil.copyfile(header, stage / header.name)
        if not headers:
            raise AuditError(f"no .vh headers in {src} (md2_defs.vh/md2_map.vh are required)")
        script = ["read_verilog -sv " + " ".join(f"-D{k}" for k in defines) + " -I. " + " ".join(names),
                  f"hierarchy -top {TOP}",
                  "proc", "opt", "opt_clean",
                  f'write_json "{Path(out_json).resolve()}"']
        ys = stage / "audit.ys"
        ys.write_text("\n".join(script) + "\n", encoding="ascii")
        proc = subprocess.run([yosys, "-q", "-s", "audit.ys"], cwd=stage, capture_output=True, text=True, env=env)
        if proc.returncode != 0 or not Path(out_json).exists():
            raise AuditError(f"yosys failed ({proc.returncode}):\n{proc.stdout}\n{proc.stderr}")
        if keep:
            Path(out_json).with_suffix(".ys").write_text("\n".join(script) + "\n", encoding="ascii")
        return Path(out_json)


def run_audit(src: Path, json_out: Path | None = None, ihp_sram: bool = True) -> Report:
    files, defines = source_files(src, ihp_sram)
    note = (f"source list from {Path(rtl_sources.__file__).name}, defines "
            + "/".join(sorted(defines)) + f" ({len(files)} files)")
    with tempfile.TemporaryDirectory(prefix="cdc_netlist_") as work:
        path = Path(work) / "netlist.json"
        elaborate(src, path, ihp_sram=ihp_sram)
        report = Audit(path, note=note).run()
        if json_out is not None:
            Path(json_out).write_text(json.dumps(report.as_dict(), indent=2), encoding="utf-8")
        return report


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--src", type=Path, default=Path(rtl_sources.SRC), help="RTL source directory")
    ap.add_argument("--json-out", type=Path, help="write the report (and findings) as JSON")
    ap.add_argument("--no-ihp-sram", action="store_true", help="elaborate md2_pmem/md2_dmem arrays instead of the "
                                                               "IHP SRAM models (faster; CDC boundary unchanged)")
    args = ap.parse_args(argv)
    try:
        report = run_audit(args.src, args.json_out, ihp_sram=not args.no_ihp_sram)
    except AuditError as exc:
        print(f"structural CDC audit: ERROR {exc}", file=sys.stderr)
        return 2
    print(report.text())
    return 0 if report.passed else 1


if __name__ == "__main__":
    sys.exit(main())
