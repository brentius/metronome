"""Check the Metronome v4 thread cuts (SPEC_V2 sections 4, 5, 9 and 12.3).

Two cuts:

* **Module cut.**  The elaborated `md2_thread` module's seven registers (`pc`,
  `en`, `ready`, `running`, `armed`, `late`, `ovr`) are extracted next-state by
  next-state through `rtlil.DffCone`, and the generated Lean proves the
  extracted transition equal to `Metronome.Thread.step`, an independent statement
  of SPEC_V2 section 4 (thread state and priorities), section 5 (dispatch and
  pause) and section 9 (the host `PC`/`STAT` writes).  A trace lift carries the
  equality through any finite sampled input sequence.

* **Chip-top cut.**  For each of the six `g_thr[k].u` instances of
  [the chip top](../src/project.v) this module checks the instance wiring
  and extracts the combinational cones of its inputs.  Upstream nets (`frz`,
  the line event sources, the move bus, the core pipeline outputs, the host
  decode) are bound as free per-cycle leaves, and the generated Lean proves:

  * `clk` is the top clock and `rst_n` is the reset synchronizer's `rst_q`
    (structural check);
  * `ev` and `db` are gated by `~frz` (SPEC 12.3) and the `ev` decode is the
    SPEC section 4 event table: `ev_g[TRIG]`, the thread's line pin edges,
    `ALWAYS = !READY && !RUNNING`, and `NONE` never;
  * `disp`, `pause`, `npc`, `stop`, `late_set` and `line_beat` are the SPEC
    quantities of sections 4, 5 and 3.2/3.4;
  * `h_pc_we`/`h_stat_we` are `w_trt & i_trt == k & o_trt == offset` with the
    host data byte (section 9), tied to `Metronome.HostMap`'s `trt` window.

Run it from the repository root:

    python lean/thread_check.py
    python lean/thread_check.py --mutations

`run_mutations()` plants the required regressions on temporary copies of `src/`
(never the repository): three thread-register priority changes, an ungated `ev`,
a thread reading another line's `BEAT`, and an `ALWAYS` trigger that ignores
`RUNNING`.  Every one must be rejected.
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
from verify import HERE, ROOT, TOP, run


THREAD_MODULE = "md2_thread"
NTHREADS = 6
DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_thread_v4_20261121"
TEMPLATE = HERE / "ThreadEquivalence.lean.in"
AXIOM_LINE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)
LEAN_TIMEOUT = 900

# SPEC_V2 section 4 event codes, cross-checked against `code/md2/machine.json`
# (`triggers`) and the `T_*` constants of `src/md2_defs.vh`.
TRIGGERS = [
    "NONE",
    "L0.BEAT", "L0.TAP0", "L0.TAP1", "L0.TAP2",
    "L1.BEAT", "L1.TAP0", "L1.TAP1", "L1.TAP2",
    "L2.BEAT", "L2.TAP0", "L2.TAP1", "L2.TAP2",
    "L3.BEAT", "L3.TAP0", "L3.TAP1", "L3.TAP2",
    "FLAG0.RISE", "FLAG1.RISE", "FLAG2.RISE", "FLAG3.RISE",
    "FLAG4.RISE", "FLAG5.RISE", "FLAG6.RISE", "FLAG7.RISE",
    "PINA.RISE", "PINA.FALL", "PINA.EDGE",
    "HOST.INV",
    "ALWAYS",
]

# The host-map constants this cut relies on (`src/md2_map.vh`, SPEC_V2 §9).
HOST_CONSTANTS = {
    "HA_TRT_BASE": 0x2440,
    "HSPAN_TRT": 0x000C,
    "HS_TRT": 2,
    "HO_TRT_PC": 0,
    "HO_TRT_STAT": 1,
}
MAP_CONSTANTS = {"DG_L_SYM": 0, "DG_T_STOP": 1}

# The free per-cycle leaves of the chip-top cut.  Each entry is
# (net name in the elaborated top, width, Lean expression).
LEAVES = (
    ("l_beat", 4, "(L.beat)"),
    ("l_tap", 12, "(L.tap)"),
    ("fl", 16, "(L.flag)"),
    ("flp", 16, "(L.flagPrev)"),
    ("inv", 1, "(L.inv)"),
    ("invp", 1, "(L.invPrev)"),
    ("l_parise", 4, "(L.parise)"),
    ("l_pafall", 4, "(L.pafall)"),
    ("t_ready", 6, "(L.ready)"),
    ("t_running", 6, "(L.running)"),
    ("t_armed", 6, "(L.armed)"),
    ("db", 6, "(L.doorbell)"),
    ("dsp", 2, "(L.dispatchCore)"),
    ("disp_e", 6, "(L.dispatchThread)"),
    ("pse", 2, "(L.pauseCore)"),
    ("xt", 6, "(L.execThread)"),
    ("npc", 16, "(L.nextPc)"),
    ("grp_v", 30, "(L.groups)"),
    ("mv_valid", 6, "(L.valid)"),
    ("h_wr", 1, "(L.hostWrite)"),
    ("ha", 16, "(L.hostAddr)"),
    ("h_wd", 8, "(L.hostData)"),
    ("frz", 1, "(L.frz)"),
)

# The instance inputs checked by the chip-top cut, and the generated Lean name
# of each extracted cone.
TOP_INPUTS = (
    ("ev", "Ev", "Bool"),
    ("db", "Db", "Bool"),
    ("disp", "Disp", "Bool"),
    ("pause", "Pause", "Bool"),
    ("npc", "Npc", "BitVec 8"),
    ("stop", "Stop", "Bool"),
    ("late_set", "Late", "Bool"),
    ("line_beat", "Beat", "Bool"),
    ("h_pc_we", "PcWe", "Bool"),
    ("h_stat_we", "StatWe", "Bool"),
)


class ThreadRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated thread cut."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


class ThreadCrashed(RuntimeError):
    """The Lean process died without a proof verdict; the evidence is unusable."""

    def __init__(self, message, code):
        super().__init__(message)
        self.code = code


class ThreadCone(DffCone):
    """A `DffCone` with the extra cell shapes the thread cones need.

    Yosys lowers a bus-wide `== 0` test to `$logic_not` and a reduction `|bus`
    to `$reduce_or` / `$reduce_bool`; the wide `$and` / `$or` / `$not` of the
    six-bit move vectors need bitwise `BitVec` operations.  All three shapes are
    decoded here rather than in `rtlil.py`, which every other cut shares.  They
    stay fail-closed: a `$logic_not` must be one scalar result of a whole bus, a
    reduction must be a scalar result of a whole bus, a wide logic cell must be
    equal-width, and anything else raises `UnsupportedRTL`.
    """

    EXTRA = ("$logic_not", "$reduce_or", "$reduce_bool")

    # Cell shapes whose extracted expression is a Lean `Bool`.  A one-bit bus
    # driven by anything else (`$mux`, arithmetic) is a `BitVec 1` and has to be
    # compared with zero.
    BOOL_KINDS = ("$and", "$logic_and", "$or", "$logic_or", "$not", "$eq",
                  "$ne", "$ge", "$lt", "$shiftx", "$logic_not", "$reduce_or",
                  "$reduce_bool")

    def __init__(self, name, module):
        super().__init__(name, module)
        for cell_name, cell in module["cells"].items():
            kind = cell["type"]
            if kind not in self.EXTRA:
                continue
            pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
            where = f"{name}.{cell_name} ({kind})"
            require(set(pins) == {"A", "Y"} and len(pins["Y"]) == 1,
                    f"{where}: expected one scalar result")
            require(len(pins["A"]) == int(cell["parameters"]["A_WIDTH"], 2) and
                    int(cell["parameters"]["Y_WIDTH"], 2) == 1 and
                    len(pins["A"]) > 0, f"{where}: unexpected widths")
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = (kind, pins, cell["parameters"], where)

    def opaque(self, name, width, value):
        """Bind a driven net as an opaque free per-cycle input.

        Unlike `leaf` this accepts a net that is a slice of a wider driven bus
        (the thread configuration byte `tc` inside `cfg`): the binding is
        checked by the caller and the Lean theorem states the formula in terms
        of it, so the over-approximation is explicit.  Overlapping leaves fail.
        """
        net = self.module["netnames"].get(name)
        require(net is not None, f"{self.name}.{name}: missing net")
        bits = tuple(net["bits"])
        require(len(bits) == width, f"{self.name}.{name}: expected {width} bits")
        require(bits not in self.bound, f"{self.name}.{name}: already bound")
        require(any(isinstance(bit, int) for bit in bits),
                f"{self.name}.{name}: tied-off net")
        for key in self.bound:
            require(not (set(key) & set(bits)),
                    f"{self.name}.{name}: overlaps the bound bus {key}")
        self.bound[bits] = value
        return bits

    def bool_of(self, bits):
        """Express a one-bit bus as a Lean `Bool`.

        The RTLIL adapter's `_bit_bool` handles the same shapes, but a one-bit
        `$mux`/arithmetic result is a `BitVec 1`, and mixing a `BitVec 1` branch
        with a `Bool` branch in one `if` does not typecheck.  This method builds
        every `$mux` recursively in `Bool`, wraps other data cells in a zero
        test and returns the `Bool` expressions of logic cells directly.
        Fail-closed: an undriven bit raises `UnsupportedRTL`.
        """
        require(len(bits) == 1, f"{self.name}: expected one bit")
        if bits in self.bound:
            return self.bound[bits]
        bit = bits[0]
        if bit == "0":
            return "false"
        if bit == "1":
            return "true"
        for key, value in self.bound.items():
            if bit in key:
                index = key.index(bit)
                if len(key) == 1:
                    return value
                return (f"((BitVec.truncate 1 (BitVec.ushiftRight {value} "
                        f"{index})) != 0)")
        driver = self.drivers.get(bits)
        require(driver is not None,
                f"{self.name}: unsupported, sliced or undriven bit {bits}")
        kind, pins, params, where = driver
        if kind == "$mux":
            require(len(pins["A"]) == 1 and len(pins["B"]) == 1 and
                    len(pins["S"]) == 1, f"{where}: expected a one-bit mux")
            expr = (f"(if {self._bit_bool(pins['S'][0])} then "
                    f"{self.bool_of(pins['B'])} else {self.bool_of(pins['A'])})")
            wire = f"{self.name}{len(self.lines)}"
            self.lines.append(f"  let {wire} := {expr}")
            self.bound[bits] = wire
            return wire
        if kind in self.BOOL_KINDS:
            return self.expression(bits)
        return f"({self.expression(bits)} != 0)"

    def expression(self, bits):
        driver = self.drivers.get(bits)
        if driver is not None and driver[0] == "$logic_not":
            _, pins, params, where = driver
            width = int(params["A_WIDTH"], 2)
            require(len(bits) == 1 and len(pins["A"]) == width,
                    f"{where}: unexpected result bus")
            source = self.expression(pins["A"])
            expr = f"({source} == (0 : BitVec {width}))"
            wire = f"{self.name}{len(self.lines)}"
            self.lines.append(f"  let {wire} := {expr}")
            self.bound[bits] = wire
            return wire
        if driver is not None and driver[0] in ("$reduce_or", "$reduce_bool"):
            _, pins, params, where = driver
            width = int(params["A_WIDTH"], 2)
            require(len(bits) == 1 and len(pins["A"]) == width,
                    f"{where}: unexpected result bus")
            source = self.expression(pins["A"])
            expr = f"({source} != (0 : BitVec {width}))"
            wire = f"{self.name}{len(self.lines)}"
            self.lines.append(f"  let {wire} := {expr}")
            self.bound[bits] = wire
            return wire
        if driver is not None and driver[0] in ("$and", "$or", "$not"):
            _, pins, params, where = driver
            width = int(params["Y_WIDTH"], 2)
            if width > 1:
                require(int(params["A_WIDTH"], 2) == width and len(pins["A"]) == width,
                        f"{where}: unexpected A width")
                left = self.expression(pins["A"])
                if driver[0] == "$not":
                    expr = f"(~~~{left})"
                else:
                    require(int(params["B_WIDTH"], 2) == width and
                            len(pins["B"]) == width, f"{where}: unexpected B width")
                    operator = "&&&" if driver[0] == "$and" else "|||"
                    expr = f"({left} {operator} {self.expression(pins['B'])})"
                wire = f"{self.name}{len(self.lines)}"
                self.lines.append(f"  let {wire} := {expr}")
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
    result = run([yosys, "-Q", "-q", "-p", commands], work)
    if result.returncode != 0:
        raise ThreadRejected(f"Yosys elaboration failed: {result.stdout.strip()}")
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
    """The ordered bits of a named net, requiring its width."""
    net = module["netnames"].get(name)
    require(net is not None, f"{module.get('name', '?')}.{name}: missing net")
    require("init" not in net["attributes"],
            f"{name}: unexpected initial value")
    bits = tuple(net["bits"])
    require(len(bits) == width, f"{name}: expected {width} bits")
    return bits


def header_constants(directory):
    """Read the host-map and destination constants this cut states."""
    directory = Path(directory)
    map_text = (directory / "md2_map.vh").read_text(encoding="utf-8")
    defs_text = (directory / "md2_defs.vh").read_text(encoding="utf-8")

    def read(text, name, base=10):
        match = re.search(
            rf"\b{name}\s*=\s*(?:(\d+)'([hdbo])([0-9A-Fa-f_]+)|(\d+))", text)
        require(match is not None, f"{name}: missing from the headers")
        if match.group(3) is not None:
            digits = match.group(3).replace("_", "")
            return int(digits, {"h": 16, "d": 10, "b": 2, "o": 8}[match.group(2)])
        return int(match.group(4))

    constants = {name: read(map_text, name) for name in HOST_CONSTANTS}
    constants.update({name: read(map_text, name) for name in MAP_CONSTANTS})
    for name, value in HOST_CONSTANTS.items():
        require(constants[name] == value,
                f"{name}: expected {value}, header says {constants[name]}")
    for name, value in MAP_CONSTANTS.items():
        require(constants[name] == value,
                f"{name}: expected {value}, header says {constants[name]}")
    codes = {}
    for index, name in enumerate(TRIGGERS):
        local = "T_" + name.replace(".", "_")
        codes[name] = read(defs_text, local)
        require(codes[name] == index,
                f"{local}: expected {index}, header says {codes[name]}")
    machine = ROOT / "code" / "md2" / "machine.json"
    require(machine.is_file(), f"{machine}: missing machine description")
    triggers = json.loads(machine.read_text(encoding="utf-8"))["triggers"]
    require(triggers == TRIGGERS,
            "code/md2/machine.json triggers do not match the SPEC_V2 table")
    return constants, codes


# ---------------------------------------------------------------- module check


def check_thread_top(modules):
    """Check the six thread instances and their clock/reset/output wiring."""
    top = modules[TOP]
    require(NTHREADS == 6, "SPEC_V2 section 4 fixes six threads")
    for k in range(NTHREADS):
        name = f"g_thr[{k}].u"
        require(name in top["cells"], f"{TOP}.{name}: missing thread instance")
        cell = top["cells"][name]
        module = modules[cell["type"]]
        require(cell["type"] == THREAD_MODULE or
                module["attributes"].get("hdlname") == THREAD_MODULE,
                f"{name}: unexpected thread module")
        pins = cell["connections"]
        require(tuple(pins["clk"]) == tuple(top["ports"]["clk"]["bits"]),
                f"{name}: unexpected clock")
        require(tuple(pins["rst_n"]) == tuple(top["netnames"]["rst_q"]["bits"]),
                f"{name}: unexpected reset")
        require(tuple(pins["h_d"]) == tuple(top["netnames"]["h_wd"]["bits"]),
                f"{name}: host data is not h_wd")
        for port, net, width in (("pc", "t_pc", 8), ("en", "t_en", 1),
                                 ("ready", "t_ready", 1), ("running", "t_running", 1),
                                 ("armed", "t_armed", 1), ("late", "t_late", 1),
                                 ("ovr", "t_ovr", 1)):
            base = 8 * k if width == 8 else k
            expect = tuple(top["netnames"][net]["bits"])[base:base + width]
            require(tuple(pins[port]) == expect,
                    f"{name}.{port}: unexpected output connection")
    modules_used = set()
    for cell in top["cells"].values():
        if cell["type"] == THREAD_MODULE:
            modules_used.add(cell["type"])
        elif cell["type"] in modules and \
                modules[cell["type"]].get("attributes", {}).get("hdlname") == THREAD_MODULE:
            modules_used.add(cell["type"])
    require(len(modules_used) == 1, "the six threads must share one elaborated module")
    return modules[modules_used.pop()]


def extract_thread_module(module):
    """Extract the seven-register thread transition from the elaborated module."""
    cone = ThreadCone("thread", module)
    for name, width, value in (
        ("rst_n", 1, "input.resetN"),
        ("ev", 1, "input.ev"),
        ("db", 1, "input.db"),
        ("disp", 1, "input.disp"),
        ("pause", 1, "input.pause"),
        ("npc", 8, "input.npc"),
        ("stop", 1, "input.stop"),
        ("late_set", 1, "input.lateSet"),
        ("line_beat", 1, "input.lineBeat"),
        ("h_pc_we", 1, "input.hPcWe"),
        ("h_stat_we", 1, "input.hStatWe"),
        ("h_d", 8, "input.hD"),
    ):
        cone.input(name, width, value)
    fields = {}
    data = {}
    for name, width, current in (
        ("pc", 8, "state.pc"),
        ("en", 1, "state.en"),
        ("ready", 1, "state.ready"),
        ("running", 1, "state.running"),
        ("armed", 1, "state.armed"),
        ("late", 1, "state.late"),
        ("ovr", 1, "state.ovr"),
    ):
        data[name] = cone.register(name, width, current)
    for name, bits in data.items():
        fields[name] = cone.expression(bits) if len(bits) > 1 else cone.bool_of(bits)
    require(not cone.registers, "unmodeled thread state")
    return {"lets": "\n".join(cone.lines), "fields": fields}


def lean_thread_module(info, fingerprint):
    """Emit the extracted thread transition as a Lean definition."""
    fields = info["fields"]
    return f"""import Metronome.Thread
import Metronome.HostMap

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {fingerprint}
-- Module: the elaborated `{THREAD_MODULE}` instance shared by
-- `{TOP}.g_thr[0..5].u`.  Every register is sampled; `rst_n` is a synchroniser
-- input of the cut, so the reset branch is part of the extracted transition.

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Metronome.Thread

/-- The elaborated thread transition.  `state` is the cycle's register value and
`input` the sampled cycle inputs. -/
def rtlStep (state : State) (input : Input) : State :=
{info['lets']}
  ⟨{fields['pc']}, {fields['en']}, {fields['ready']}, {fields['running']},
   {fields['armed']}, {fields['late']}, {fields['ovr']}⟩

end Metronome.Thread

"""


# ------------------------------------------------------------------- top check


def extract_thread_inputs(modules, k, constants):
    """Extract the ten input cones of instance `k` with free leaves.

    Returns a dict of Lean definitions (name -> (signature, body, lines)) and the
    number of gates used per input.
    """
    top = modules[TOP]
    cell = top["cells"][f"g_thr[{k}].u"]
    pins = cell["connections"]
    defs = {}
    counts = {}
    for pin, lean, _ in TOP_INPUTS:
        cone = ThreadCone(f"th{k}{lean}", top)
        for name, width, value in LEAVES:
            cone.opaque(name, width, value)
        cone.opaque(f"g_thr[{k}].tc", 8, "(tc)")
        bits = tuple(pins[pin])
        expression = cone.expression(bits) if len(bits) > 1 else cone.bool_of(bits)
        defs[lean] = {"lets": "\n".join(cone.lines), "body": expression}
        counts[pin] = len(cone.lines)
    return defs, counts


def lean_top_defs(extracted, fingerprint):
    """Emit the six instances' extracted input cones."""
    lines = [f"""-- Chip top: `{TOP}.g_thr[k].u` for k = 0..5 (SPEC_V2 4, 5, 9, 12.3).
-- Upstream nets are free per-cycle leaves (`Leaves`); the generated theorems
-- state each extracted cone in terms of them."""]
    for k, defs in enumerate(extracted):
        group = [f"\n/-! ### Instance {k} -/"]
        for pin, lean, kind in TOP_INPUTS:
            info = defs[lean]
            group.append(f"""
/-- The extracted `{pin}` input of `g_thr[{k}].u`. -/
def rtl{lean}{k} (L : Leaves) (tc : BitVec 8) : {kind} :=
{info['lets']}
  {info['body']}""")
        lines.extend(group)
    return "\n".join(lines) + "\n"


def lean_top_theorems(extracted, codes):
    """Emit the per-instance chip-top theorems."""
    leaves = ("frz, beat, tap, flag, flagPrev, inv, invPrev, parise, pafall, "
              "ready, running, armed, doorbell, dispatchCore, dispatchThread, "
              "pauseCore, execThread, nextPc, groups, valid, hostWrite, "
              "hostAddr, hostData")
    def bind():
        return ("  obtain \u27e8" + leaves + "\u27e9 := L")

    parts = []
    for k in range(NTHREADS):
        parts.append(f"""
/-! ### Instance {k}: the SPEC inputs -/

/-- The extracted `ev` input is the SPEC section 4 event decode gated by
`~frz` (section 12.3). -/
theorem rtlEvIn{k}_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlEv{k} L tc = (evRaw L tc (bitAt L.ready {k}) (bitAt L.running {k}) && !L.frz) := by
{bind()}
  simp only [rtlEv{k}, evRaw, evTable, flagRise, bitAt, mux4, ln, ts]
  bv_decide

/-- The extracted `db` input is the thread's doorbell bit gated by `~frz`
(section 12.3; a frozen doorbell is held and delivered later). -/
theorem rtlDbIn{k}_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlDb{k} L tc = (bitAt L.doorbell {k} && !L.frz) := by
{bind()}
  simp only [rtlDb{k}, bitAt]
  bv_decide

/-- The extracted `disp` input is "a core dispatches this thread": the dispatch
strobe of a core whose selected thread is this one (section 5). -/
theorem rtlDisp{k}_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlDisp{k} L tc = ((bitAt L.dispatchCore 0 && blk L.dispatchThread 0 == ({k} : BitVec 3)) ||
      (bitAt L.dispatchCore 1 && blk L.dispatchThread 3 == ({k} : BitVec 3))) := by
{bind()}
  simp only [rtlDisp{k}, bitAt, blk]
  bv_decide

/-- The extracted `pause` input is "the core executing this thread retires a
pausing instruction" (section 5). -/
theorem rtlPause{k}_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlPause{k} L tc = ((bitAt L.pauseCore 0 && blk L.execThread 0 == ({k} : BitVec 3)) ||
      (bitAt L.pauseCore 1 && blk L.execThread 3 == ({k} : BitVec 3))) := by
{bind()}
  simp only [rtlPause{k}, bitAt, blk]
  bv_decide

/-- The extracted `npc` input is the pausing core's next PC: core 1's high byte
when core 1 pauses this thread, core 0's low byte otherwise (section 5). -/
theorem rtlNpc{k}_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlNpc{k} L tc =
      selectedPc L (bitAt L.pauseCore 1 && blk L.execThread 3 == ({k} : BitVec 3)) := by
{bind()}
  simp only [rtlNpc{k}, selectedPc, bitAt, blk]
  bv_decide

/-- The extracted `stop` input is one of this thread's own enabled moves to
`T.STOP` (sections 4 and 6). -/
theorem rtlStop{k}_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlStop{k} L tc = stopSpec L (blk L.execThread 0 == ({k} : BitVec 3))
      (blk L.execThread 3 == ({k} : BitVec 3)) := by
{bind()}
  simp only [rtlStop{k}, stopSpec, bitAt, blk, grp]
  bv_decide

/-- The extracted `late_set` input is one of this thread's own enabled symbol
moves while it is not armed (sections 4 and 6). -/
theorem rtlLate{k}_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlLate{k} L tc = lateSpec L (blk L.execThread 0 == ({k} : BitVec 3))
      (blk L.execThread 3 == ({k} : BitVec 3)) (bitAt L.armed {k}) := by
{bind()}
  simp only [rtlLate{k}, lateSpec, bitAt, blk, grp]
  bv_decide

/-- The extracted `line_beat` input is the configured line's `BEAT`
(sections 3.2 and 4). -/
theorem rtlBeat{k}_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlBeat{k} L tc = mux4 L.beat (ln tc) := by
{bind()}
  simp only [rtlBeat{k}, mux4, bitAt, ln]
  bv_decide

/-- The extracted `PC` write enable is `w_trt & i_trt == k & o_trt == 0`, the
`TRT.PC` byte of the host map (section 9). -/
theorem rtlPcWe{k}_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlPcWe{k} L tc = hostPcWe {k} L.hostWrite L.hostAddr := by
{bind()}
  simp only [rtlPcWe{k}, hostPcWe, hostBase, hostSpan, threadIndex, threadOffset]
  bv_decide

/-- The extracted `STAT` write enable is `w_trt & i_trt == k & o_trt == 1`, the
`TRT.STAT` byte of the host map (section 9). -/
theorem rtlStatWe{k}_eq_spec (L : Leaves) (tc : BitVec 8) :
    rtlStatWe{k} L tc = hostStatWe {k} L.hostWrite L.hostAddr := by
{bind()}
  simp only [rtlStatWe{k}, hostStatWe, hostBase, hostSpan, threadIndex, threadOffset]
  bv_decide
""")
    return "\n".join(parts).replace("\n  bv_decide\n", "\n  all_goals bv_decide\n")


def lean_hostmap():
    """Emit the HostMap tie for the two `TRT` byte addresses of each thread."""
    base = HOST_CONSTANTS["HA_TRT_BASE"]
    stride = HOST_CONSTANTS["HS_TRT"]
    parts = ["""
-- The axiom audit of the chip-top equalities.  `thread_check.py` parses these
-- records and rejects `sorryAx`.
#print axioms rtlEvIn0_eq_spec
#print axioms rtlDbIn0_eq_spec
#print axioms rtlStop0_eq_spec
#print axioms rtlLate0_eq_spec
#print axioms rtlBeat0_eq_spec
#print axioms rtlPcWe0_eq_spec
#print axioms rtlStatWe5_eq_spec
"""]
    for k in range(NTHREADS):
        for off, name in ((HOST_CONSTANTS["HO_TRT_PC"], "PC"),
                          (HOST_CONSTANTS["HO_TRT_STAT"], "STAT")):
            addr = base + stride * k + off
            parts.append(f"""
/-- `{addr:#06x}` is thread {k}'s `TRT.{name}` byte inside `HostMap`'s `trt`
window, and its window offset decodes to instance {k}, offset {off}. -/
theorem hostMap_trt_{k}_{name} :
    Metronome.HostMap.inRegion .trt {addr:#06x} = true ∧
      (({addr:#06x} : BitVec 16) - Metronome.HostMap.base .trt) == {stride * k + off} ∧
      (((({addr:#06x} : BitVec 16) - Metronome.HostMap.base .trt) >>> 1) == {k}) ∧
      (((({addr:#06x} : BitVec 16) - Metronome.HostMap.base .trt) &&& 1) == {off}) := by
  decide
""")
    return "\n".join(parts)


# ---------------------------------------------------------------------- runner


def axiom_audit(text):
    """Collect the `#print axioms` records from a Lean run."""
    return {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
            for name, axioms in AXIOM_LINE.findall(text)}


def run_lean(source, filename, artifact, lake, work, evidence):
    """Run Lean with a 900 s timeout; retry a crashed process once.

    Lean exits 0 on success and 1 on a failed proof.  Windows cold starts have
    been observed to kill a Lean process without output, so one abnormal exit is
    retried; a second abnormal exit raises `ThreadCrashed`, because a crash is
    not a proof verdict and must not be counted as a rejected mutant.
    """
    path = Path(work) / filename
    path.write_text(source, encoding="utf-8")
    if evidence:
        (Path(evidence) / artifact).write_text(source, encoding="utf-8")
    result = None
    for _ in range(2):
        result = run([lake, "env", "lean", "-j1", "-DwarningAsError=true", str(path)],
                     HERE, timeout=LEAN_TIMEOUT)
        if result.returncode in (0, 1, 2):
            return result
    raise ThreadCrashed(f"the Lean process failed twice (last exit {result.returncode})",
                        result.returncode)


def check_thread(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the thread module cut and the chip-top input cut.

    `rtlil_or_json` is a parsed Yosys design, a path to `design.json`, or a
    Verilog source directory to elaborate.  Evidence is written to `out_dir` as
    `<case>.thread.lean` and `<case>.log`.  Returns a result dictionary; a
    rejected cut raises `ThreadRejected` (proof or audit) or `UnsupportedRTL`
    (structure or wiring).
    """
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-thread-{case}-") as tmp:
        work = Path(tmp)
        is_json = isinstance(rtlil_or_json, dict) or (
            isinstance(rtlil_or_json, (str, Path)) and Path(rtlil_or_json).suffix == ".json")
        if is_json:
            modules = load_modules(rtlil_or_json)
            fingerprint = "not recorded: parsed design JSON"
            constants, codes = header_constants(ROOT / "src")
        else:
            snapshot = snapshot_of(rtlil_or_json)
            modules, fingerprint, commands, yosys_log = elaborate(
                snapshot, work / "rtl", yosys)
            log.append(f"RTL snapshot SHA-256: {fingerprint}\n")
            log.append(f"Yosys command: {commands}\n")
            log.append(yosys_log)
            constants, codes = header_constants(rtlil_or_json)

        try:
            module = check_thread_top(modules)
            info = extract_thread_module(module)
            log.append("Thread module cut: 7 registers extracted\n")
            extracted = []
            counts = {}
            for k in range(NTHREADS):
                defs, per_pin = extract_thread_inputs(modules, k, constants)
                extracted.append(defs)
                counts[k] = per_pin
            log.append("Chip-top cut: inputs extracted for 6 instances: "
                       + ", ".join(f"k={k}:{sum(v.values())} gates"
                                   for k, v in counts.items()) + "\n")
            source = lean_thread_module(info, fingerprint)
            source += TEMPLATE.read_text(encoding="utf-8").replace(
                "-- @CONSTANTS@", constant_block(constants, codes))
            source += lean_top_defs(extracted, fingerprint)
            source += lean_top_theorems(extracted, codes)
            source += lean_hostmap()
            source += "\nend Metronome.Thread.Top\n"
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the structural thread check: {exc}\n")
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise

        result = run_lean(source, "ThreadProof.lean", f"{case}.thread.lean",
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
            "registers": 7,
            "instances": NTHREADS,
            "fingerprint": fingerprint,
            "source": out_dir / f"{case}.thread.lean",
            "log": out_dir / f"{case}.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            first = next((line.strip() for line in result.stdout.splitlines()
                          if "error:" in line), outcome)
            first = first.split("ThreadProof.lean:", 1)[-1]
            raise ThreadRejected(f"{case}: {outcome}\n" + "".join(log),
                                 reason=f"{outcome}: {first[:150]}",
                                 code=result.returncode)
    return report


def constant_block(constants, codes):
    """Emit the header constants the chip-top statements are written with."""
    values = {
        "TRIG_PINA_RISE": (codes["PINA.RISE"], 5),
        "TRIG_PINA_FALL": (codes["PINA.FALL"], 5),
        "TRIG_PINA_EDGE": (codes["PINA.EDGE"], 5),
        "TRIG_ALWAYS": (codes["ALWAYS"], 5),
        "DG_L_SYM": (MAP_CONSTANTS["DG_L_SYM"], 5),
        "DG_T_STOP": (MAP_CONSTANTS["DG_T_STOP"], 5),
        "HA_TRT_BASE": (HOST_CONSTANTS["HA_TRT_BASE"], 16),
        "HSPAN_TRT": (HOST_CONSTANTS["HSPAN_TRT"], 16),
    }
    return "\n".join(f"abbrev {name} : BitVec {width} := {value}"
                     for name, (value, width) in values.items())


# ------------------------------------------------------------------- mutations


def thread_mutations():
    """The planted thread regressions, as snapshot transformers."""
    def replace(before, after, filename="md2_thread.v"):
        def apply(snapshot):
            require(filename in snapshot, f"mutation: missing {filename}")
            data = snapshot[filename]
            require(data.count(before.encode()) == 1,
                    f"mutation: anchor changed in {filename}: {before}")
            return {**snapshot,
                    filename: data.replace(before.encode(), after.encode(), 1)}
        return apply

    return [
        # Dispatch beats a pause for RUNNING; SPEC_V2 has the two cases target
        # different threads, so the resolution is only visible to this cut.
        ("thread_pause_dispatch", replace(
            "            if (pause)     running <= 1'b0;\n"
            "            else if (disp) running <= 1'b1;",
            "            if (disp)      running <= 1'b1;\n"
            "            else if (pause) running <= 1'b0;")),
        # A pause beats a host PC write: SPEC_V2 section 4 says the host write
        # wins.
        ("thread_pc_pause_wins", replace(
            "            if (h_pc_we)    pc <= h_d;\n"
            "            else if (pause) pc <= npc;",
            "            if (pause)      pc <= npc;\n"
            "            else if (h_pc_we) pc <= h_d;")),
        # A host STAT clear beats a same-cycle overrun: SPEC_V2 section 9 keeps
        # a sticky flag set in the cycle it is cleared.
        ("thread_ovr_clear_wins", replace(
            "            ovr  <= (trig & busy) | (ovr & ~(h_stat_we & h_d[5]));",
            "            ovr  <= ((trig & busy) | ovr) & ~(h_stat_we & h_d[5]);")),
        # The event and doorbell inputs are no longer gated by the freeze.
        ("thread_ev_not_frozen", replace(
            ".ev(ev & ~frz), .db(db[k] & ~frz)",
            ".ev(ev), .db(db[k])", "project.v")),
        # Thread 3 reads line 2's BEAT (and pin edges) instead of its own line.
        ("thread3_line2_beat", replace(
            "            wire [1:0] ln = tc[2:1];",
            "            wire [1:0] ln = (k == 3) ? 2'd2 : tc[2:1];",
            "project.v")),
        # ALWAYS ignores RUNNING, so a running thread re-triggers.
        ("thread_always_ignores_running", replace(
            "((ts == T_ALWAYS) & ~t_ready[k] & ~t_running[k])",
            "((ts == T_ALWAYS) & ~t_ready[k])", "project.v")),
    ]


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted thread regression is rejected.

    Returns one `(case, rejected, stage, exit)` record per mutation and raises
    `ThreadRejected` if any mutant is accepted.
    """
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-thread-mutants-") as tmp:
        for case, transform in thread_mutations():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_thread(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"structural check: {exc}", 0))
                continue
            except ThreadRejected as exc:
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
    Path(path).write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mutations", action="store_true",
                        help="also check the planted thread regressions")
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
            raise ThreadRejected("tool version query failed")

        build = run([lake, "build", "Metronome.Thread", "Metronome.HostMap"], HERE,
                    timeout=LEAN_TIMEOUT)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise ThreadRejected("lake build Metronome.Thread Metronome.HostMap failed")

        snapshot = snapshot_of(ROOT / "src")
        report = check_thread(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        emit(f"baseline: {report['outcome']} ({report['registers']} registers, "
             f"{report['instances']} instances)")
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
        raise SystemExit(f"Thread check failed: {exc}") from exc
