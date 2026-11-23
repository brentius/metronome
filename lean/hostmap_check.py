"""Check the elaborated host write decode against `Metronome.HostMap`.

The host link hands the register file a 16-bit address `ha`, a write strobe
`h_wr` and a data byte `h_wd`.  SPEC_V2 §9 and the generated `src/md2_map.vh`
say which block each address belongs to and which register byte a write
reaches.  This cut closes that decode:

1. **Regions.**  For all 65536 addresses the elaborated `in_prog`, `in_data`,
   `in_cfg`, `in_ctl`, `in_lrt`, `in_trt`, `in_srt` and `in_dbg` flags equal the
   independent block table of `Metronome.HostMap`; the eight regions are
   pairwise disjoint (a region counter stays at or below one); and each `a_*`
   offset net equals `ha - base` for the map's base.
2. **Write enables.**  Every register write enable (the six `ctrl` strobes, the
   seven `dbg` strobes, the line/thread/stream strobes of each instance, the
   two program-memory core strobes with their byte-lane one-hot, the data-RAM
   host set and the configuration-window strobe) is proved equal to "a host
   write at exactly that register's address" (or, for the memories, at an
   address inside that memory's window).  The generated family theorem shows at
   most one enable fires for any host write, and concrete read-only or unmapped
   addresses are shown to enable nothing.
3. **Write data.**  Three local next-state contracts are proved from the flop
   input cones: `CTRL.STICKY` write-1-to-clear for the three sticky bits, the
   `DOORBELL` pulse (one cycle, held while frozen), and `HOSTIN` setting `INV`
   and loading the mailbox byte.

Extraction is fail-closed: an unsupported cell, an undriven net, a second
driver, a wrong port connection, a wrong subtraction base or a wrong span fails
the run before Lean starts.  The generated Lean is checked by Lean, and the
`#print axioms` audit rejects `sorryAx`.

Run it from the repository root:

    python lean/hostmap_check.py
    python lean/hostmap_check.py --mutations

`run_mutations()` plants four regressions on temporary copies of `src/` (never
the repository): an overlapping block base, a thread `STAT` write to the wrong
instance, an inverted program-memory byte lane, and a write enable moved onto a
read-only register byte.
"""

import argparse
from collections import OrderedDict
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

from rtlil import UnsupportedRTL, require
from corectl_check import VectorCone, axiom_audit
from verify import HERE, ROOT, TOP, run, run_lean


DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_hostmap_v4_20261120"
TEMPLATE = HERE / "HostMapEquivalence.lean.in"

# Blocks in map order: (BlockId as used by Metronome.HostMap, base name, span name).
BLOCKS = (
    ("Prog", "HA_PROG_BASE", "HSPAN_PROG"),
    ("Data", "HA_DATA_BASE", "HSPAN_DATA"),
    ("Cfg", "CFG_LO", "HSPAN_CFG"),
    ("Ctrl", "HA_CTRL_BASE", "HSPAN_CTRL"),
    ("Lrt", "HA_LRT_BASE", "HSPAN_LRT"),
    ("Trt", "HA_TRT_BASE", "HSPAN_TRT"),
    ("Srt", "HA_SRT_BASE", "HSPAN_SRT"),
    ("Dbg", "HA_DBG_BASE", "HSPAN_DBG"),
)

# Register offsets and instance strides the enable table uses.
OFFSETS = (
    "HO_CTRL_RUN", "HO_CTRL_STICKY", "HO_CTRL_IRQEN", "HO_CTRL_DOORBELL",
    "HO_CTRL_HOSTIN", "HO_CTRL_HOSTSTAT",
    "HO_LRT_PHASE", "HO_LRT_CTL", "HO_LRT_STAT",
    "HO_TRT_PC", "HO_TRT_STAT",
    "HO_SRT_CTL",
    "HO_DBG_DBG", "HO_DBG_MCTL", "HO_DBG_ECTL", "HO_DBG_EMASK", "HO_DBG_RLV",
)
STRIDES = ("HS_LRT", "HS_TRT", "HS_SRT")
COUNTS = ("MD_N_LINES", "MD_N_THREADS", "MD_N_STREAMS")

# Blocks whose offset and region nets are not spelled `a_<block>` /
# `in_<block>`.
OFFSET_NET = {"Prog": "a_prg", "Data": "a_dat", "Ctrl": "a_ctl"}
REGION_NET = {"Prog": "in_prg", "Ctrl": "in_ctl"}


def offset_net(suffix):
    """The elaborated offset bus of a block."""
    return OFFSET_NET.get(suffix, f"a_{suffix.lower()}")


def region_net(suffix):
    """The elaborated region flag of a block."""
    return REGION_NET.get(suffix, f"in_{suffix.lower()}")

# Read-only or unmapped addresses that must enable nothing.  The list mirrors
# `Metronome.HostMap.readOnlyAddrs`.
READ_ONLY = (
    (0x2405, "ctrl hostout"), (0x2407, "ctrl id"), (0x2408, "ctrl errsum"),
    (0x240F, "ctrl padding"), (0x2413, "lrt sym"), (0x2414, "lrt ins"),
    (0x2464, "dbg misr"), (0x2465, "dbg misr+1"), (0x246A, "dbg acc"),
    (0x246B, "dbg aflg"), (0x246C, "dbg flags"), (0x246D, "dbg flags+1"),
    (0x2470, "dbg fpc"), (0x2471, "dbg fpc+1"), (0x1800, "data end"),
    (0x1FFF, "gap below cfg"), (0x21E0, "cfg end"), (0x21FF, "gap"),
    (0x2480, "unmapped"), (0x24FF, "unmapped"), (0xFFFF, "top"),
)


class HostMapRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated decode."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


class HostCone(VectorCone):
    """A `VectorCone` that also decodes `$shl` and raw sub-nets.

    `pm_be = 8'd1 << a_prg[2:0]` lowers to `$shl`, which no existing cone
    indexes; the configuration-live leaf is a nameless net bit, so it is bound
    directly.  Everything else is inherited, including the fail-closed shapes.
    """

    def __init__(self, name, module):
        super().__init__(name, module)
        for cell_name, cell in module["cells"].items():
            if cell["type"] != "$shl":
                continue
            pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
            where = f"{name}.{cell_name} ($shl)"
            require(set(pins) == {"A", "B", "Y"},
                    f"{where}: unexpected ports {sorted(pins)}")
            require(len(pins["A"]) == int(cell["parameters"]["A_WIDTH"], 2) and
                    len(pins["B"]) == int(cell["parameters"]["B_WIDTH"], 2) and
                    len(pins["Y"]) == int(cell["parameters"]["Y_WIDTH"], 2),
                    f"{where}: operand widths disagree")
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = ("$shl", pins, cell["parameters"], where)

    def bind_bits(self, bits, value):
        """Bind raw net bits (possibly unnamed) as one opaque free value."""
        bits = tuple(bits)
        require(bits, f"{self.name}: empty bind")
        require(bits not in self.bound, f"{self.name}: bits already bound")
        if bits in self.drivers:
            del self.drivers[bits]
        for output in tuple(self.drivers) + tuple(self.registers) + tuple(self.bound):
            require(not (set(output) & set(bits)),
                    f"{self.name}: the bound bits overlap {output}")
        require(set(bits) <= self.claimed or set(bits).isdisjoint(self.claimed),
                f"{self.name}: partially claimed bits")
        self.claimed.difference_update(bits)
        self.bound[bits] = value
        return bits

    def expression(self, bits):
        driver = self.drivers.get(bits)
        if driver is not None and driver[0] == "$shl":
            _, pins, _, where = driver
            width = len(bits)
            require(width == int(driver[2]["Y_WIDTH"], 2),
                    f"{where}: unexpected result width")
            source = self.expression(pins["A"])
            amount = self.expression(pins["B"])
            expression = (f"(BitVec.shiftLeft (BitVec.setWidth {width} {source}) "
                          f"({amount}).toNat)")
            wire = f"{self.name}{len(self.lines)}"
            self.lines.append(f"  let {wire} := {expression}")
            self.bound[bits] = wire
            return wire
        return super().expression(bits)


# --------------------------------------------------------------------- sources


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
        raise HostMapRejected(f"Yosys elaboration failed: {result.stdout.strip()}")
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


# ---------------------------------------------------------------- the host map


def header_params(snapshot):
    """Read the host map's bases, spans, strides and register offsets."""
    headers = "".join(snapshot[name].decode("latin-1") for name in sorted(snapshot)
                      if name.endswith(".vh"))

    def number(name, base=10):
        match = re.search(
            r"localparam\s+(?:\[[^\]]+\]\s+)?(?:integer\s+)?" + name +
            r"\s*=\s*(16'h[0-9A-Fa-f]+|\d+)\s*;", headers)
        require(match is not None, f"{name}: constant pattern changed in the headers")
        text = match.group(1)
        return int(text.split("h", 1)[1], 16) if text.startswith("16'h") else int(text)

    values = {"base_" + suffix.lower(): number(base) for suffix, base, _ in BLOCKS}
    values.update({"span_" + suffix.lower(): number(span) for suffix, _, span in BLOCKS})
    values.update({name.lower(): number(name) for name in OFFSETS + STRIDES + COUNTS})
    for suffix, _, span in BLOCKS:
        require(values["span_" + suffix.lower()] > 0, f"{span}: empty block span")
    for name in ("lrt", "trt", "srt"):
        stride = values["hs_" + name]
        require(stride > 0 and stride & (stride - 1) == 0,
                f"HS_{name.upper()} is not a power of two")
        values["shift_" + name] = stride.bit_length() - 1
    require(values["ho_lrt_phase"] + 1 < values["hs_lrt"], "LRT PHASE leaves its stride")
    require(values["ho_ctrl_hoststat"] < values["span_ctrl"], "HOSTSTAT leaves ctrl")
    require(values["ho_dbg_rlv"] + 1 < values["span_dbg"], "DBG RLV leaves dbg")
    return values


def enable_table(params):
    """The 43 register write enables, in `Metronome.HostMap.regAddrs` order.

    Each entry is `(Lean name, probe, address, human label)`, where `probe` is
    one of `("net", name)`, `("port", cell, port)` or
    `("portbit", cell, port, index)`.
    """
    p = params
    table = []

    def add(name, probe, address, label):
        table.append((name, probe, address & 0xFFFF, label))

    base = p["base_ctrl"]
    add("CtrlRun", ("net", "c_wr_run"), base + p["ho_ctrl_run"], "CTRL.RUN")
    add("CtrlSticky", ("net", "c_wr_stk"), base + p["ho_ctrl_sticky"], "CTRL.STICKY")
    add("CtrlIrqen", ("net", "c_wr_irqen"), base + p["ho_ctrl_irqen"], "CTRL.IRQEN")
    add("CtrlDoorbell", ("net", "c_wr_db"), base + p["ho_ctrl_doorbell"],
        "CTRL.DOORBELL")
    add("CtrlHostIn", ("net", "c_wr_hin"), base + p["ho_ctrl_hostin"], "CTRL.HOSTIN")
    add("CtrlHostStat", ("net", "c_wr_hst"), base + p["ho_ctrl_hoststat"],
        "CTRL.HOSTSTAT")
    for k in range(p["md_n_lines"]):
        cell = f"g_ln[{k}].u"
        start = p["base_lrt"] + p["hs_lrt"] * k
        add(f"Line{k}Phase0", ("portbit", cell, "h_ph_we", 0),
            start + p["ho_lrt_phase"], f"LRT[{k}].PHASE low")
        add(f"Line{k}Phase1", ("portbit", cell, "h_ph_we", 1),
            start + p["ho_lrt_phase"] + 1, f"LRT[{k}].PHASE high")
        add(f"Line{k}Ctl", ("portbit", cell, "h_ctl_we", 0),
            start + p["ho_lrt_ctl"], f"LRT[{k}].CTL")
        add(f"Line{k}Stat", ("portbit", cell, "h_stat_we", 0),
            start + p["ho_lrt_stat"], f"LRT[{k}].STAT")
    for k in range(p["md_n_threads"]):
        cell = f"g_thr[{k}].u"
        start = p["base_trt"] + p["hs_trt"] * k
        add(f"Thread{k}Pc", ("portbit", cell, "h_pc_we", 0),
            start + p["ho_trt_pc"], f"TRT[{k}].PC")
        add(f"Thread{k}Stat", ("portbit", cell, "h_stat_we", 0),
            start + p["ho_trt_stat"], f"TRT[{k}].STAT")
    for k in range(p["md_n_streams"]):
        add(f"Stream{k}Ctl", ("net", f"g_s[{k}].hctl"),
            p["base_srt"] + p["hs_srt"] * k + p["ho_srt_ctl"], f"SRT[{k}].CTL")
    base = p["base_dbg"]
    add("DbgDbg", ("net", "d_wr_dbg"), base + p["ho_dbg_dbg"], "DBG.DBG")
    add("DbgMctl", ("net", "d_wr_mctl"), base + p["ho_dbg_mctl"], "DBG.MCTL")
    add("DbgEctl", ("net", "h_ectl"), base + p["ho_dbg_ectl"], "DBG.ECTL")
    add("DbgEmask0", ("net", "h_em0"), base + p["ho_dbg_emask"], "DBG.EMASK low")
    add("DbgEmask1", ("net", "h_em1"), base + p["ho_dbg_emask"] + 1, "DBG.EMASK high")
    add("DbgRlv0", ("net", "h_rlv0"), base + p["ho_dbg_rlv"], "DBG.RLV low")
    add("DbgRlv1", ("net", "h_rlv1"), base + p["ho_dbg_rlv"] + 1, "DBG.RLV high")
    addresses = [address for _, _, address, _ in table]
    require(len(set(addresses)) == len(addresses),
            "the host map assigns two registers the same address")
    return table


def probe_bits(top, probe):
    """Resolve an enable probe to its net bits."""
    kind = probe[0]
    if kind == "net":
        entry = top["netnames"].get(probe[1])
        require(entry is not None, f"{probe[1]}: missing net")
        bits = tuple(entry["bits"])
        require(len(bits) == 1, f"{probe[1]}: expected a scalar enable")
        return bits
    cell = top["cells"].get(probe[1])
    require(cell is not None, f"{probe[1]}: missing instance")
    require(probe[2] in cell["connections"], f"{probe[1]}.{probe[2]}: missing port")
    bits = tuple(cell["connections"][probe[2]])
    index = probe[3] if len(probe) > 3 else 0
    require(index < len(bits), f"{probe[1]}.{probe[2]}: short port")
    return (bits[index],)


def net(top, name, width):
    entry = top["netnames"].get(name)
    require(entry is not None, f"{TOP}.{name}: missing net")
    bits = tuple(entry["bits"])
    require(len(bits) == width, f"{TOP}.{name}: expected {width} bits")
    return bits


def port(top, cell, name, width):
    entry = top["cells"].get(cell)
    require(entry is not None, f"{TOP}.{cell}: missing instance")
    require(name in entry["connections"], f"{TOP}.{cell}.{name}: missing port")
    bits = tuple(entry["connections"][name])
    require(len(bits) == width, f"{TOP}.{cell}.{name}: expected {width} bits")
    return bits


def driver_index(top):
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


def driver_cell(top, index, bits, label):
    """The single cell pin driving this whole bus, as `(name, cell)`."""
    require(bits, f"{label}: empty bus")
    owners = set()
    for bit in bits:
        owner = index.get(bit)
        require(owner is not None, f"{label}: undriven net bit {bit}")
        owners.add(owner)
    require(len(owners) == 1, f"{label}: the bus is not driven by one cell pin")
    name, _ = owners.pop()
    return name, top["cells"][name]


def constant(bits):
    """A constant bus (little-endian) as an integer, or `None`."""
    if not bits or not all(bit in ("0", "1") for bit in bits):
        return None
    return int("".join(reversed(bits)), 2)


def reduce_of(top, bits, label):
    """The scalar `|bits` reduction cell's output, as a free leaf candidate."""
    bits = tuple(bits)
    for name, cell in top["cells"].items():
        if cell["type"] in ("$reduce_or", "$reduce_bool", "$logic_not") and \
                tuple(cell["connections"]["A"]) == bits:
            require(len(cell["connections"]["Y"]) == 1,
                    f"{label}: the reduction is not scalar")
            return tuple(cell["connections"]["Y"])
    raise UnsupportedRTL(f"{label}: no scalar reduction of the bus")


# ------------------------------------------------------------- the extraction


def check_ports(top):
    """Check the host and memory instance connections the cut relies on."""
    index = driver_index(top)
    ha, h_wr, h_wd = net(top, "ha", 16), net(top, "h_wr", 1), net(top, "h_wd", 8)
    require(port(top, "u_host", "addr", 16) == ha, "u_host.addr is not ha")
    require(port(top, "u_host", "wr", 1) == h_wr, "u_host.wr is not h_wr")
    require(port(top, "u_host", "wdata", 8) == h_wd, "u_host.wdata is not h_wd")

    a_prg = net(top, "a_prg", 16)
    fadr = net(top, "fadr", 16)
    pm_be = net(top, "pm_be", 8)
    for core, we_name in ((0, "pm_we0"), (1, "pm_we1")):
        cell = f"u_pmem{core}"
        we = net(top, we_name, 1)
        require(port(top, cell, "we", 1) == we, f"{cell}.we is not {we_name}")
        require(port(top, cell, "be", 8) == pm_be, f"{cell}.be is not pm_be")
        _, mux = driver_cell(top, index, port(top, cell, "addr", 8),
                             f"{cell}.addr")
        require(mux["type"] == "$mux", f"{cell}.addr is not a mux")
        require(tuple(mux["connections"]["S"]) == we, f"{cell}.addr select is not {we_name}")
        require(tuple(mux["connections"]["B"]) == a_prg[3:11],
                f"{cell}.addr does not take the program word address when writing")
        require(tuple(mux["connections"]["A"]) == fadr[8 * core:8 * core + 8],
                f"{cell}.addr does not take the fetch address otherwise")

    require(port(top, "u_mem", "h_wr", 1) == h_wr, "u_mem.h_wr is not h_wr")
    require(port(top, "u_mem", "h_d", 8) == h_wd, "u_mem.h_d is not h_wd")
    require(port(top, "u_mem", "h_addr", 11) == net(top, "a_dat", 16)[:11],
            "u_mem.h_addr is not a_dat[10:0]")
    return index


def check_block_decodes(top, index):
    """Check the shape of every block decode and record its constants.

    Every `a_*` must be a subtraction of `ha` from a constant, and every `in_*`
    a comparison of that offset against a constant.  The constants themselves
    are recorded but not required to match the map here: the generated Lean
    proves each region and offset equal to `Metronome.HostMap`'s table, so a
    drifted base or span is a proof failure rather than an adapter failure.
    """
    ha = net(top, "ha", 16)
    offsets, bases, spans = {}, {}, {}
    for suffix, _, _ in BLOCKS:
        key = suffix.lower()
        offset_bits = net(top, offset_net(suffix), 16)
        name, sub = driver_cell(top, index, offset_bits, f"a_{key}")
        require(sub["type"] == "$sub", f"a_{key}: not a subtraction")
        require(tuple(sub["connections"]["A"]) == ha, f"a_{key}: does not subtract from ha")
        value = constant(sub["connections"]["B"])
        require(value is not None, f"a_{key}: the base is not a constant")
        bases[key] = value
        span_bits = net(top, region_net(suffix), 1)
        _, lt = driver_cell(top, index, span_bits, f"in_{key}")
        require(lt["type"] == "$lt", f"in_{key}: not a span comparison")
        require(tuple(lt["connections"]["A"]) == offset_bits,
                f"in_{key}: does not compare the offset")
        value = constant(lt["connections"]["B"])
        require(value is not None, f"in_{key}: the span is not a constant")
        spans[key] = value
        offsets[key] = offset_bits
    return {"offsets": offsets, "bases": bases, "spans": spans}


def check_cfg_host_now(top, index):
    """Check `cfg_host_now = h_wr & in_cfg & live` and return the live net."""
    h_wr = net(top, "h_wr", 1)
    in_cfg = net(top, "in_cfg", 1)
    probe = net(top, "cfg_host_now", 1)
    name, root = driver_cell(top, index, probe, "cfg_host_now")
    require(root["type"] in ("$and", "$logic_and"), "cfg_host_now: not an AND")
    left = tuple(root["connections"]["A"])
    right = tuple(root["connections"]["B"])
    left_name, left_cell = driver_cell(top, index, left, "cfg_host_now left")
    require(left_cell["type"] in ("$and", "$logic_and"),
            "cfg_host_now: the write filter is not an AND")
    operands = {tuple(left_cell["connections"]["A"]),
                tuple(left_cell["connections"]["B"])}
    require(operands == {h_wr, in_cfg},
            "cfg_host_now: the filter is not h_wr & in_cfg")
    require(left_name != name, "cfg_host_now: unexpected cell reuse")
    return right


def extract(modules, probe_bits, free, leaves, name):
    """Extract one cone as a Lean function of the named free values.

    A named net is bound as a leaf even when combinational logic drives it, so
    an enable or an event term becomes an opaque per-cycle input; the cut then
    says what the flop does with it.
    """
    top = modules[TOP]
    cone = HostCone(name, top)
    for net_name, width, value in free:
        entry = top["netnames"].get(net_name)
        require(entry is not None, f"{net_name}: missing net")
        bits = tuple(entry["bits"])
        require(len(bits) == width, f"{net_name}: expected {width} bits")
        if bits in cone.drivers:
            cone.leaf(net_name, width, value)
        else:
            cone.free(net_name, width, value)
    for bits, value in leaves:
        cone.bind_bits(bits, value)
    expression = cone.expression(probe_bits)
    require(expression not in ("true", "false"),
            f"{name}: the enable is a constant")
    return list(cone.lines), expression


def extract_register(modules, flop, width, free, leaves, name, current="q"):
    """Extract a register's reset-released input cone.

    The chip top wraps every register in `if (!rst_q) ... else ...`, so the
    `D` bus is a mux on `rst_q`.  The adapter checks that the mux's reset branch
    is all zero and extracts the other branch, which is the next state when
    reset is released.  The register's own `Q` bus is bound as `current`.
    """
    top = modules[TOP]
    cone = HostCone(name, top)
    for net_name, net_width, value in free:
        entry = top["netnames"].get(net_name)
        require(entry is not None, f"{net_name}: missing net")
        bits = tuple(entry["bits"])
        require(len(bits) == net_width, f"{net_name}: expected {net_width} bits")
        cone.leaf(net_name, net_width, value)
    for bits, value in leaves:
        cone.bind_bits(bits, value)
    data = cone.register(flop, width, current)
    driver = cone.drivers.get(data)
    if driver is not None and driver[0] == "$mux":
        pins = driver[1]
        if tuple(pins["S"]) == net(top, "rst_q", 1):
            require(len(pins["A"]) == len(pins["B"]) == width,
                    f"{name}: the reset mux has inconsistent widths")
            require(all(bit == "0" for bit in pins["A"]),
                    f"{name}: the reset branch is not zero")
            data = pins["B"]
    require(driver is None or driver[0] != "$mux" or
            tuple(driver[1]["S"]) == net(top, "rst_q", 1),
            f"{name}: the register has an unexpected input mux")
    expression = cone.expression(data)
    return list(cone.lines), expression


def extract_all(modules, table):
    """Extract the region, offset and enable cones."""
    top = modules[TOP]
    index = check_ports(top)
    decode = check_block_decodes(top, index)

    regions, offsets = {}, {}
    for suffix, _, _ in BLOCKS:
        key = suffix.lower()
        for kind, target in (("region", region_net(suffix)), ("offset", offset_net(suffix))):
            bits = net(top, target, 1 if kind == "region" else 16)
            lines, expression = extract(modules, bits, [("ha", 16, "a")], [],
                                        f"rtl{kind.title()}{suffix}")
            (regions if kind == "region" else offsets)[key] = (lines, expression)

    enables = OrderedDict()
    for name, probe, address, label in table:
        bits = probe_bits(top, probe)
        lines, expression = extract(modules, bits,
                                    [("h_wr", 1, "w"), ("ha", 16, "a")], [],
                                    f"en{name}")
        enables[name] = {"lines": lines, "expression": expression,
                         "address": address, "label": label}

    # Program memory: two core strobes, the byte-lane one-hot and the word.
    mem = {}
    for name in ("pm_we0", "pm_we1"):
        lines, expression = extract(modules, net(top, name, 1),
                                    [("h_wr", 1, "w"), ("ha", 16, "a")], [],
                                    f"en{name.title().replace('_', '')}")
        mem[name] = (lines, expression)
    lines, expression = extract(modules, net(top, "pm_be", 8),
                                [("ha", 16, "a")], [], "pmBe")
    mem["pm_be"] = (lines, expression)
    lines, expression = extract(modules, net(top, "a_prg", 16)[3:11],
                                [("ha", 16, "a")], [], "progWord")
    mem["prog_word"] = (lines, expression)
    lines, expression = extract(modules, net(top, "a_dat", 16)[:11],
                                [("ha", 16, "a")], [], "dataAddr")
    mem["data_addr"] = (lines, expression)

    # Data RAM: the host set strobe, with the read strobe free.
    lines, expression = extract(modules, port(top, "u_mem", "h_set", 1),
                                [("h_wr", 1, "w"), ("h_rd", 1, "r"), ("ha", 16, "a")],
                                [], "hSet")
    mem["h_set"] = (lines, expression)

    # Configuration window: the live-byte leaf is a nameless decoded net.
    live = check_cfg_host_now(top, index)
    lines, expression = extract(modules, net(top, "cfg_host_now", 1),
                                [("h_wr", 1, "w"), ("ha", 16, "a")],
                                [(live, "live")], "enCfg")
    mem["cfg"] = (lines, expression, live)

    # Write data: three sticky bits, the doorbell, the mailbox and INV.
    data = OrderedDict()
    h_wd = net(top, "h_wd", 8)
    for name, flop, event, bit in (("StickyConflict", "conflict", "conflict_ev", 0),
                                   ("StickyMemhaz", "memhaz", "memhaz_ev", 1)):
        lines, expression = extract_register(
            modules, flop, 1,
            [("c_wr_stk", 1, "stk"), (event, 1, "ev")],
            [(h_wd[bit:bit + 1], "bit")], f"rtl{name}")
        data[name] = {"lines": lines, "expression": expression,
                      "sig": "ev q stk bit : Bool",
                      "ret": "Bool",
                      "rhs": "HostMap.stickyNext ev q stk bit",
                      "tactic": ("simp only [rtl" + name + ", HostMap.stickyNext] <;> "
                                 "cases ev <;> cases q <;> cases stk <;> cases bit <;> rfl"),
                      "doc": f"The `{flop}` sticky-bit next state."}
    lines, expression = extract_register(
        modules, "cw_overrun", 1,
        [("c_wr_stk", 1, "stk"), ("cw_write_data", 1, "wd"),
         ("cw_accept", 1, "acc")],
        [(h_wd[2:3], "bit")], "rtlStickyOverrun")
    data["StickyOverrun"] = {"lines": lines, "expression": expression,
                             "sig": "wd acc q stk bit : Bool",
                             "ret": "Bool",
                             "rhs": "HostMap.stickyNext (wd && !acc) q stk bit",
                             "tactic": ("simp only [rtlStickyOverrun, HostMap.stickyNext] <;> "
                                        "cases wd <;> cases acc <;> cases q <;> cases stk <;> "
                                        "cases bit <;> rfl"),
                             "doc": "The `cw_overrun` sticky-bit next state."}

    lines, expression = extract_register(
        modules, "db", 6, [("c_wr_db", 1, "wr"), ("frz", 1, "frz")],
        [(h_wd, "d")], "rtlDoorbell")
    data["Doorbell"] = {"lines": lines, "expression": expression,
                        "sig": "(wr frz : Bool) (q : BitVec 6) (d : BitVec 8)",
                        "ret": "BitVec 6",
                        "rhs": "HostMap.doorbellNext wr frz (d.truncate 6) q",
                        "tactic": ("simp only [rtlDoorbell, HostMap.doorbellNext]\n"
                                   "  bv_decide"),
                        "doc": "The doorbell word next state."}

    lines, expression = extract_register(
        modules, "inv", 1, [("c_wr_hin", 1, "wr")],
        [(reduce_of(top, net(top, "rd_hin", 6), "rd_hin"), "rd")], "rtlInv")
    data["Inv"] = {"lines": lines, "expression": expression,
                   "sig": "(wr : Bool) (q rd : Bool)",
                   "ret": "Bool",
                   "rhs": "HostMap.invNext wr rd q",
                   "tactic": ("simp only [rtlInv, HostMap.invNext] <;> "
                              "cases wr <;> cases rd <;> cases q <;> rfl"),
                   "doc": "The `HOSTIN` input-valid flag next state."}

    lines, expression = extract_register(
        modules, "inb", 8, [("c_wr_hin", 1, "wr")], [(h_wd, "d")], "rtlMailbox")
    data["Mailbox"] = {"lines": lines, "expression": expression,
                       "sig": "(wr : Bool) (q d : BitVec 8)",
                       "ret": "BitVec 8",
                       "rhs": "HostMap.mailboxNext wr d q",
                       "tactic": ("simp only [rtlMailbox, HostMap.mailboxNext] <;> "
                                  "cases wr <;> rfl"),
                       "doc": "The `HOSTIN` mailbox byte next state."}
    return {"regions": regions, "offsets": offsets, "enables": enables,
            "mem": mem, "data": data, "table": table, "decode": decode}


# ------------------------------------------------------------ generated Lean


def lean_regions(info):
    chunks = ["/-! ## Region decode and per-block offsets -/\n"]
    for suffix, _, _ in BLOCKS:
        key = suffix.lower()
        lines, expression = info["regions"][key]
        body = "\n".join(lines + [f"  {expression}"])
        chunks.append(f"""
/-- The elaborated `in_{key}` flag for the `{key}` block. -/
def rtlIn{suffix} (a : BitVec 16) : Bool :=
{body}

/-- `in_{key}` is exactly membership in the map's `{key}` window. -/
theorem rtlIn{suffix}_spec (a : BitVec 16) :
    rtlIn{suffix} a = HostMap.inRegion .{key} a := by
  unfold rtlIn{suffix} HostMap.inRegion HostMap.base HostMap.span
  bv_decide
""")
        lines, expression = info["offsets"][key]
        body = "\n".join(lines + [f"  {expression}"])
        chunks.append(f"""
/-- The elaborated `a_{key}` offset bus. -/
def rtlOff{suffix} (a : BitVec 16) : BitVec 16 :=
{body}

/-- The offset is `ha` minus the map's `{key}` base. -/
theorem rtlOff{suffix}_spec (a : BitVec 16) :
    rtlOff{suffix} a = a - HostMap.base .{key} := by
  unfold rtlOff{suffix} HostMap.base
  bv_decide
""")

    flags = ", ".join(f"rtlIn{suffix} a" for suffix, _, _ in BLOCKS)
    rewrites = ", ".join(f"rtlIn{suffix}_spec" for suffix, _, _ in BLOCKS)
    chunks.append(f"""
/-- Two block windows never both claim one address: the eight elaborated
region flags are pairwise exclusive, hence a host address has one block. -/
theorem regions_exclusive (a : BitVec 16) :
    HostMap.bitCount [{flags}] ≤ 1 := by
  simp only [{rewrites}]
  exact HostMap.blockCount_le_one a
""")
    return "".join(chunks)


def lean_enables(info):
    chunks = ["/-! ## Register write enables -/\n"]
    names, calls = [], []
    for name, entry in info["enables"].items():
        body = "\n".join(entry["lines"] + [f"  {entry['expression']}"])
        address = entry["address"]
        chunks.append(f"""
/-- Host write enable of `{entry['label']}`. -/
def en{name} (w : Bool) (a : BitVec 16) : Bool :=
{body}

/-- `{entry['label']}` is written exactly by a host write at `0x{address:04X}`. -/
theorem en{name}_spec (w : Bool) (a : BitVec 16) :
    en{name} w a = (w && (a == 0x{address:04X})) := by
  unfold en{name}
  bv_decide
""")
        names.append(f"en{name}")
        calls.append(f"en{name}_spec")

    for name in ("enProg0", "enProg1", "enData"):
        lines, expression = info["mem"][{"enProg0": "pm_we0", "enProg1": "pm_we1",
                                         "enData": "h_set"}[name]]
        if name == "enData":
            chunks.append(f"""
/-- The data-RAM host set strobe, with the read strobe free. -/
def hSet (w r : Bool) (a : BitVec 16) : Bool :=
{chr(10).join(lines + ['  ' + expression])}

/-- The host set strobe is `(write | read) & in_data`. -/
theorem hSet_spec (w r : Bool) (a : BitVec 16) :
    hSet w r a = ((w || r) && HostMap.inRegion .data a) := by
  unfold hSet
  simp only [HostMap.inRegion, HostMap.base, HostMap.span]
  bv_decide

/-- The data-RAM host **write** strobe is exactly a host write in the data
window, for either value of the (mutually exclusive) read strobe. -/
theorem dataWe_spec (w r : Bool) (a : BitVec 16) :
    (hSet w r a && w) = (w && HostMap.inRegion .data a) := by
  rw [hSet_spec]
  cases w <;> simp

/-- The data-RAM host write enable, as a member of the uniform enable list. -/
def enData (w : Bool) (a : BitVec 16) : Bool := hSet w true a && w

/-- The data RAM is written exactly by a host write in the data window. -/
theorem enData_spec (w : Bool) (a : BitVec 16) :
    enData w a = (w && HostMap.inRegion .data a) :=
  dataWe_spec w true a
""")
            names.append("enData")
            calls.append("enData_spec")
            continue
        body = "\n".join(lines + [f"  {expression}"])
        core = "0" if name == "enProg0" else "1"
        chunks.append(f"""
/-- The program-memory core-{core} host write strobe. -/
def {name} (w : Bool) (a : BitVec 16) : Bool :=
{body}

/-- Core {core}'s program memory is written exactly by a host write in its half
of the program window. -/
theorem {name}_spec (w : Bool) (a : BitVec 16) :
    {name} w a = (w && HostMap.progCore{core} a) := by
  unfold {name}
  simp only [HostMap.progCore{core}]
  bv_decide
""")
        names.append(name)
        calls.append(f"{name}_spec")

    lines, expression, _live = info["mem"]["cfg"]
    chunks.append(f"""
/-- The configuration-window write strobe, with the live-byte mask free. -/
def enCfg (w live : Bool) (a : BitVec 16) : Bool :=
{chr(10).join(lines + ['  ' + expression])}

/-- A configuration byte is written exactly by a host write at a live window
address; `cfgSel` keeps the mask decode (the separate address-decode cut)
symbolic. -/
theorem enCfg_spec (w live : Bool) (a : BitVec 16) :
    enCfg w live a = (w && HostMap.cfgSel live a) := by
  unfold enCfg
  simp only [HostMap.cfgSel, HostMap.inRegion, HostMap.base, HostMap.span]
  bv_decide
""")
    calls.append("enCfg_spec")
    lines, expression = info["mem"]["pm_be"]
    chunks.append(f"""
/-- The program-memory byte-lane select. -/
def pmBe (a : BitVec 16) : BitVec 8 :=
{chr(10).join(lines + ['  ' + expression])}

/-- The byte lane is the one-hot `1 << address[2:0]` of the map's program
offset, so a byte write selects exactly its byte of the 64-bit word. -/
theorem pmBe_spec (a : BitVec 16) :
    pmBe a = HostMap.laneOneHot (HostMap.progLane a) := by
  unfold pmBe
  simp only [HostMap.laneOneHot, HostMap.progLane, HostMap.base]
  bv_decide
""")

    lines, expression = info["mem"]["prog_word"]
    chunks.append(f"""
/-- The program-memory word address. -/
def rtlProgWord (a : BitVec 16) : BitVec 8 :=
{chr(10).join(lines + ['  ' + expression])}

/-- The program write addresses the map's word offset `[10:3]`. -/
theorem rtlProgWord_spec (a : BitVec 16) :
    rtlProgWord a = HostMap.progWord a := by
  unfold rtlProgWord
  simp only [HostMap.progWord, HostMap.base]
  bv_decide
""")

    lines, expression = info["mem"]["data_addr"]
    chunks.append(f"""
/-- The data-RAM host byte address. -/
def rtlDataAddr (a : BitVec 16) : BitVec 11 :=
{chr(10).join(lines + ['  ' + expression])}

/-- The data write addresses the map's offset `[10:0]`. -/
theorem rtlDataAddr_spec (a : BitVec 16) :
    rtlDataAddr a = HostMap.dataAddr a := by
  unfold rtlDataAddr
  simp only [HostMap.dataAddr, HostMap.base]
  bv_decide
""")

    entries = ",\n".join(f"    {name}" for name in names)
    rewrites = ", ".join(calls)
    chunks.append(f"""
/-- Every host write enable of the design, in `HostMap.regAddrs` order. -/
def enables : List (Bool → BitVec 16 → Bool) :=
  [{entries}]

/-- The extracted enable list evaluates to the specification's selection list
with the write strobe applied, then the configuration strobe on the end. -/
theorem enables_snoc_spec (w : Bool) (live : Bool) (a : BitVec 16) :
    enables.map (fun f => f w a) ++ [enCfg w live a] = HostMap.enabledSels live w a := by
  simp [enables, HostMap.enabledSels, HostMap.selList, HostMap.selListRegs,
    HostMap.regAddrs, HostMap.base, HostMap.span, HostMap.progCore0,
    HostMap.progCore1, HostMap.inRegion, HostMap.cfgSel, {rewrites}]

/-- **At most one write enable fires per host write**, counting the
configuration-window strobe. -/
theorem at_most_one (w live : Bool) (a : BitVec 16) :
    HostMap.bitCount (enables.map (fun f => f w a) ++ [enCfg w live a]) ≤ 1 := by
  rw [enables_snoc_spec]
  exact HostMap.enabledSels_le_one live w a
""")

    chunks.append("\n/-! ## Read-only and unmapped addresses -/\n")
    for address, label in READ_ONLY:
        chunks.append(f"""
/-- A host write at `0x{address:04X}` (`{label}`) enables nothing. -/
theorem no_write_{address:04X} (w live : Bool) :
    HostMap.bitCount
      (enables.map (fun f => f w 0x{address:04X}) ++ [enCfg w live 0x{address:04X}]) = 0 := by
  rw [enables_snoc_spec]
  refine HostMap.enabledSels_eq_zero live w 0x{address:04X} ?_
  have h := (List.all_eq_true.mp (HostMap.readOnly_no_sel live))
    0x{address:04X} (by simp [HostMap.readOnlyAddrs])
  simpa using h
""")
    return "".join(chunks)


def lean_semantics(info):
    """The write-data cones; the corollaries live in the template."""
    chunks = ["/-! ## Write data -/\n"]
    for name, entry in info["data"].items():
        body = "\n".join(entry["lines"] + [f"  {entry['expression']}"])
        chunks.append(f"""
/-- {entry['doc']} -/
def rtl{name} {_sig(entry['sig'])} : {entry['ret']} :=
{body}
""")
    for name, entry in info["data"].items():
        chunks.append(f"""
/-- The extracted next state is the specification's. -/
theorem rtl{name}_spec {_sig(entry['sig'])} :
    rtl{name} {_args(entry['sig'])} = {entry['rhs']} := by
  {entry['tactic']}
""")
    return "".join(chunks)


def _sig(sig):
    """One binder group: parenthesise a bare `a b : T` signature."""
    return sig if sig.lstrip().startswith("(") else f"({sig})"


def _args(sig):
    """The argument names of a generated Lean signature."""
    groups = re.findall(r"\(([^)]*)\)", sig) or [sig]
    names = []
    for group in groups:
        for part in group.split(","):
            names.extend(part.split(":")[0].split())
    return " ".join(names)


def lean_axioms(info):
    """The `#print axioms` audit list, over the theorems this run generated."""
    names = (["regions_exclusive"] +
             [f"rtlIn{suffix}_spec" for suffix, _, _ in BLOCKS] +
             [f"rtlOff{suffix}_spec" for suffix, _, _ in BLOCKS] +
             [f"en{name}_spec" for name in info["enables"]] +
             ["hSet_spec", "dataWe_spec", "enData_spec", "enProg0_spec",
              "enProg1_spec", "enCfg_spec", "pmBe_spec", "rtlProgWord_spec",
              "rtlDataAddr_spec", "enables_snoc_spec", "at_most_one"] +
             [f"no_write_{address:04X}" for address, _ in READ_ONLY] +
             ["rtlStickyConflict_spec", "rtlStickyMemhaz_spec",
              "rtlStickyOverrun_spec", "rtlDoorbell_spec", "rtlInv_spec",
              "rtlMailbox_spec", "sticky_conflict_cleared",
              "sticky_memhaz_cleared", "sticky_overrun_cleared",
              "doorbell_write_pulse", "doorbell_write_idle",
              "doorbell_frozen_hold", "doorbell_frozen_adds",
              "hostin_sets_inv", "hostin_loads_mailbox"])
    return "\n".join(f"#print axioms {name}" for name in names)


def lean_hostmap(info, fingerprint):
    """Emit the generated Lean module for the extracted decode."""
    template = TEMPLATE.read_text(encoding="utf-8")
    values = {
        "FINGERPRINT": fingerprint,
        "REGIONS": lean_regions(info),
        "ENABLES": lean_enables(info),
        "SEMANTICS": lean_semantics(info),
        "AXIOMS": lean_axioms(info),
    }
    for name, value in values.items():
        require("{{" + name + "}}" in template,
                f"HostMapEquivalence.lean.in: missing {{{{{name}}}}} placeholder")
        template = template.replace("{{" + name + "}}", value)
    require("{{" not in template, "HostMapEquivalence.lean.in: unsubstituted placeholder")
    return template


# ------------------------------------------------------------------- the check


def check_hostmap(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the elaborated host write decode and its generated Lean proofs.

    `rtlil_or_json` is a parsed Yosys design, a path to `design.json`, or a
    Verilog source directory to elaborate.  Evidence is written to `out_dir` as
    `<case>.lean` and `<case>.log`.  Returns a result dictionary; a rejected
    decode raises `HostMapRejected` (proof or audit) or `UnsupportedRTL`
    (extraction).
    """
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-hostmap-{case}-") as tmp:
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
            table = enable_table(params)
            info = extract_all(modules, table)
            decode = info["decode"]
            for suffix, _, _ in BLOCKS:
                key = suffix.lower()
                log.append(f"  {key}: base 0x{decode['bases'][key]:04X} "
                           f"span 0x{decode['spans'][key]:04X}\n")
            log.append(f"Host map: {len(table)} register enables, "
                       f"{len(BLOCKS)} block windows, "
                       f"{params['md_n_lines']} line / {params['md_n_threads']} thread / "
                       f"{params['md_n_streams']} stream instances\n")
            source = lean_hostmap(info, fingerprint)
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the extraction: {exc}\n")
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise
        try:
            result = run_lean(source, "HostMapProof.lean", f"{case}.lean",
                             lake, work, out_dir)
        except subprocess.TimeoutExpired as exc:
            raise HostMapRejected(f"{case}: Lean timed out: {exc}")
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
            "enables": len(table),
            "blocks": len(BLOCKS),
            "fingerprint": fingerprint,
            "source": out_dir / f"{case}.lean",
            "log": out_dir / f"{case}.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            first = next((line.strip() for line in result.stdout.splitlines()
                          if "error:" in line), outcome)
            first = first.split("HostMapProof.lean:", 1)[-1]
            raise HostMapRejected(f"{case}: {outcome}\n" + "".join(log),
                                  reason=f"{outcome}: {first[:200]}",
                                  code=result.returncode)
    return report


# ------------------------------------------------------------------ mutations


def hostmap_mutations():
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
        # The stream block is decoded from the byte before the DBG base, so its
        # window overlaps DBG: one address is claimed by two blocks.
        ("hostmap_overlap", replace(
            "project.v",
            "wire [15:0] a_srt = ha - HA_SRT_BASE;",
            "wire [15:0] a_srt = ha - (HA_DBG_BASE - 16'd1);")),
        # Thread 0's STAT write lands on the next thread instance.
        ("hostmap_thread_instance", replace(
            "project.v",
            ".h_pc_we(ht & (o_trt == HO_TRT_PC)), .h_stat_we(ht & (o_trt == HO_TRT_STAT)), .h_d(h_wd),",
            ".h_pc_we(ht & (o_trt == HO_TRT_PC)), .h_stat_we("
            "w_trt & (i_trt == ((k + 1) % NT)) & (o_trt == HO_TRT_STAT)), .h_d(h_wd),")),
        # The program-memory byte lane counts down instead of up.
        ("hostmap_pm_lane", replace(
            "project.v",
            "wire [7:0]   pm_be = 8'd1 << a_prg[2:0];",
            "wire [7:0]   pm_be = 8'd1 << (3'd7 - a_prg[2:0]);")),
        # A read-only DBG byte (`MISR`) gains MCTL's write enable.
        ("hostmap_readonly_write", replace(
            "project.v",
            "wire d_wr_mctl  = w_dbg & (o_dbg == HO_DBG_MCTL);",
            "wire d_wr_mctl  = w_dbg & (o_dbg == HO_DBG_MISR);")),
    ))


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted host-map regression is rejected.

    Returns one `(case, rejected, stage, exit)` record per mutation and raises
    `HostMapRejected` if any mutant is accepted.
    """
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-hostmap-mutants-") as tmp:
        for case, transform in hostmap_mutations().items():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_hostmap(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"extraction: {exc}", 1))
                continue
            except HostMapRejected as exc:
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
                        help="also check the planted host-map regressions")
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
            raise HostMapRejected("tool version query failed")

        build = run([lake, "build", "Metronome.HostMap"], HERE)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise HostMapRejected("lake build Metronome.HostMap failed")

        snapshot = snapshot_of(ROOT / "src")
        try:
            report = check_hostmap(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        except HostMapRejected as exc:
            emit(f"baseline: {exc.reason}")
            records.append(("baseline", exc.reason, exc.code, False))
            return 1
        emit(f"baseline: {report['outcome']} ({report['enables']} write enables, "
             f"{report['blocks']} block windows)")
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
        raise SystemExit(f"Host-map check failed: {exc}") from exc
