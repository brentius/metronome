"""Check the chip-top glue of the Metronome chip top against SPEC_V2.

The glue is the combinational and registered logic of `src/project.v` that no
other cut covers:

* **sources and guards** (SPEC_V2 §6, §7): the 512-bit source vector `srcs`
  (64 slots, `machine.SRC`), the 64-bit guard vector `guards`
  (`machine.GUARD_CONDS`) and the per-line `g_line` bundle;
* **control, flags, mailbox and sticky errors** (SPEC_V2 §6.1, §9, §12.3):
  `RUN_global`, `IRQEN`, `IRQ`, `ERR`, the doorbell `DB`, the flag pair
  `F`/`FP`, and the mailbox `INB`/`INV`/`INVP`/`OUTB`/`OUTV`;
* **output pins** (SPEC_V2 §8, §12.1, §12.3): the per-output
  `BIND`/`SEL`/`LUT` decode, the `OUT`/`OEN` registers and the three
  top-level pin buses.

This module re-elaborates the chip top with `verify.py`'s Yosys recipe, cuts
each cone out of the elaborated cells, emits Lean that proves one equality per
register, per output field and **per vector slot** against
`Metronome/Glue.lean`, and lifts the register equalities to traces.

Run it from the repository root:

    python code/tests/lean/glue_check.py
    python code/tests/lean/glue_check.py --mutations
    python code/tests/lean/glue_check.py --mutations --artifacts-dir data/raw/lean_glue_v4_20261121

`run_mutations()` plants the regressions on temporary copies of `src/` (never
the repository): a swapped source slot, an inverted guard, an `ERR` that misses
`CWOVR`, an `IRQ` that ignores `IRQEN[1]`, an `FP` that updates while frozen, a
doorbell that is not held while frozen, an `OUT` register that updates while
frozen, and a `uo_out` that does not put `IRQ` on bit 1.
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
from moves_check import lean_case, write_status
import corectl_check as corectl
import moves_check as moves


DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_glue_v4_20261121"
TEMPLATE = HERE / "GlueEquivalence.lean.in"
GLUE_LEAN = HERE / "Metronome" / "Glue.lean"
MACHINE_JSON = ROOT / "code" / "md2" / "machine.json"
AXIOM_START = re.compile(r"^'([^']+)' depends on axioms: \[(.*)$")
NO_AXIOM_START = re.compile(r"^'([^']+)' does not depend on any axioms$")
ERROR_LINE = re.compile(r"^.*?:(\d+):\d+: error", re.MULTILINE)
DECL_LINE = re.compile(r"^(?:theorem|def) (\S+)")

# Header constants the extraction checks and reports.
HEADER_PARAMS = (
    ("cfg_lo_i", r"localparam integer CFG_LO_I = (\d+);", 10),
    ("cfg_bytes", r"localparam integer CFG_BYTES = (\d+);", 10),
    ("out_base", r"localparam integer HAI_OUT_BASE = (\d+);", 10),
    ("out_stride", r"localparam integer HS_OUT = (\d+);", 10),
    ("out_bind", r"localparam integer HO_OUT_BIND = (\d+);", 10),
    ("out_sel", r"localparam integer HO_OUT_SEL = (\d+);", 10),
    ("out_lut", r"localparam integer HO_OUT_LUT = (\d+);", 10),
    ("out_oe", r"localparam integer HO_OUT_OE = (\d+);", 10),
    ("flags_set", r"localparam \[5:0\] D_FLAGS_SET = 6'd(\d+);", 10),
)

# The free leaves of the source vector: (net, width, Lean value).
SRC_FREE = (
    ("fl", 16, "fl"), ("pins_level", 13, "pins"), ("acc_a", 8, "accA"),
    ("acc_r", 32, "accR"), ("sh_d", 16, "shD"), ("sh_o", 2, "shO"),
    ("cn_v", 48, "cnV"), ("lf_s", 64, "lfS"), ("p_dat", 8, "pDat"),
    ("s_bit", 2, "sBit"), ("s_byte", 16, "sByte"), ("inb", 8, "inB"),
)

# The free leaves of the guard vector.
GUARD_FREE = (
    ("fl", 16, "fl"), ("sh_done", 2, "shDone"), ("sh_o", 2, "shOut"),
    ("cn_z", 3, "cntZ"), ("acc_z", 1, "accZ"), ("acc_c", 1, "accC"),
    ("acc_n", 1, "accN"), ("lf_s", 64, "lfS"), ("inv", 1, "inv"),
    ("outv", 1, "outv"), ("p_rdy", 1, "pRdy"), ("s_end", 2, "sEnd"),
    ("s_mark", 2, "sMark"), ("s_bb", 2, "sByte"), ("s_bit", 2, "sBit"),
    ("pins_level", 13, "pins"), ("l_run", 4, "lRun"),
)

# The free leaves of the per-line guard bundle.
LINE_FREE = (("l_in", 8, "inn"), ("l_sp", 4, "sp"),
             ("l_pina", 4, "pinA"), ("l_pinb", 4, "pinB"))

# The reset leaf every register cone reads.
RESET = ("rst_q", 1, "resetN")

SRC_PARAMS = "(s : Sources)"
SRC_ARGS = ("s.fl s.pins s.accA s.accR s.shD s.shO s.cnV s.lfS s.pDat s.sBit "
            "s.sByte s.inB")
GUARD_PARAMS = "(g : Guards)"
GUARD_ARGS = ("g.fl g.shDone g.shOut g.cntZ g.accZ g.accC g.accN g.lfS g.inv "
              "g.outv g.pRdy g.sEnd g.sMark g.sByte g.sBit g.pins g.lRun")
LINE_PARAMS = "(g : LineGuards)"
LINE_ARGS = "g.inn g.sp g.pinA g.pinB"

SRC_DEF_PARAMS = ("(fl : BitVec 16) (pins : BitVec 13) (accA : BitVec 8) "
                  "(accR : BitVec 32) (shD : BitVec 16) (shO : BitVec 2) "
                  "(cnV : BitVec 48) (lfS : BitVec 64) (pDat : BitVec 8) "
                  "(sBit : BitVec 2) (sByte : BitVec 16) (inB : BitVec 8)")
SRC_DEF_ARGS = "fl pins accA accR shD shO cnV lfS pDat sBit sByte inB"
GUARD_DEF_PARAMS = ("(fl : BitVec 16) (shDone : BitVec 2) (shOut : BitVec 2) "
                    "(cntZ : BitVec 3) (accZ accC accN : Bool) (lfS : BitVec 64) "
                    "(inv outv pRdy : Bool) (sEnd sMark sByte sBit : BitVec 2) "
                    "(pins : BitVec 13) (lRun : BitVec 4)")
GUARD_DEF_ARGS = ("fl shDone shOut cntZ accZ accC accN lfS inv outv pRdy sEnd "
                  "sMark sByte sBit pins lRun")
LINE_DEF_PARAMS = "(inn : BitVec 8) (sp : BitVec 4) (pinA : BitVec 4) (pinB : BitVec 4)"
LINE_DEF_ARGS = "inn sp pinA pinB"

OUT_IDX_DEF_PARAMS = ("(bind sel : BitVec 8) (comm : BitVec 16) "
                      "(pinA pinB : BitVec 4) (seg : BitVec 8)")
OUT_IDX_ARGS = "bind sel comm pinA pinB seg"


class GlueRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated glue cut."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


class GlueCone(moves.MovesCone):
    """A cone that decodes the shapes this glue needs.

    On top of the shared adapter, `corectl_check.VectorCone` (wide `$and`/`$or`,
    `$reduce_or`, `$logic_not`, one-bit muxes) and `moves_check.MovesCone`
    (`$mul` with a constant operand, constant `$shl`/`$shr`, wide `$shiftx`,
    wide `$not`), this cone decodes

    * a wide `$mux` whose select is a slice of a bound bus: the shared adapter
      asks for the select as a bus, which is a `BitVec 1`; it is read as a
      `Bool` here;
    * Yosys's indexed-bit-write lowering `$shift(A, $neg(zext(idx)))`, which is
      `A << idx`.  The shift is admitted only when its amount is the negation of
      a bus whose top bit is the constant zero (so the amount is non-positive
      and the shift is a left shift), and the emitted term is
      `BitVec.shiftLeft` with the low bits' `Nat` value;
    * Yosys's `x` bits, bound as free `Bool` inputs.  That over-approximates the
      circuit: a cone whose value depends on one fails its equality instead of
      proving something weaker.

    Everything stays fail-closed: an unsupported cell, an undriven net bit, a
    partial bus overlap or a second register driver raises `UnsupportedRTL`.
    """

    EXTRA2 = ("$shift", "$neg")

    def __init__(self, name, module):
        super().__init__(name, module)
        self.dontcare = {}
        for cell_name, cell in module["cells"].items():
            kind = cell["type"]
            if kind not in self.EXTRA2:
                continue
            pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
            where = f"{name}.{cell_name} ({kind})"
            require(set(pins) == ({"A", "Y"} if kind == "$neg" else {"A", "B", "Y"}),
                    f"{where}: unexpected ports")
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = (kind, pins, cell["parameters"], where)

    def _bit_bool(self, bit):
        """A one-bit net as a Lean `Bool`; Yosys's `x` bits are free inputs."""
        if bit in ("x", "z"):
            if bit not in self.dontcare:
                self.dontcare[bit] = f"x{len(self.dontcare)}"
            return self.dontcare[bit]
        return super()._bit_bool(bit)

    def expression(self, bits):
        if bits in self.bound:
            return self.bound[bits]
        driver = self.drivers.get(bits)
        if driver is not None and driver[0] == "$mux" and len(bits) > 1:
            _, pins, params, where = driver
            require(len(pins["A"]) == len(pins["B"]) == len(bits) ==
                    int(params["WIDTH"], 2) and len(pins["S"]) == 1,
                    f"{where}: inconsistent mux widths")
            require(bits not in self.resolving, f"{where}: combinational loop")
            self.resolving.add(bits)
            expression = (f"(if {self._bit_bool(pins['S'][0])} then "
                          f"{self.expression(pins['B'])} "
                          f"else {self.expression(pins['A'])})")
            self.resolving.remove(bits)
            return self._bind(bits, expression)
        if driver is not None and driver[0] == "$shift":
            _, pins, params, where = driver
            width = int(params["Y_WIDTH"], 2)
            require(width == len(bits), f"{where}: unexpected result bus")
            require(int(params["A_SIGNED"], 2) == 0, f"{where}: unexpected signed operand")
            require(int(params["B_SIGNED"], 2) == 1, f"{where}: expected a signed amount")
            neg = self.drivers.get(pins["B"])
            require(neg is not None and neg[0] == "$neg",
                    f"{where}: the shift amount is not a negated bus")
            npins, nparams = neg[1], neg[2]
            require(int(nparams["A_SIGNED"], 2) == 1 and
                    len(npins["A"]) == len(pins["B"]) == int(nparams["A_WIDTH"], 2),
                    f"{where}: unexpected negated amount")
            require(npins["A"][-1] == "0",
                    f"{where}: the negated amount is not known non-negative")
            amount = pins["A"]
            if len(amount) == 1:
                value = (f"(if {self._bit_bool(amount[0])} then "
                         f"(1 : BitVec {width}) else 0)")
            else:
                value = f"(BitVec.setWidth {width} {self.expression(amount)})"
            index = self._index(npins["A"][:-1])
            return self._bind(bits, f"(BitVec.shiftLeft {value} {index})")
        return super().expression(bits)


# --------------------------------------------------------------------------- tables


def machine_tables(path=MACHINE_JSON):
    """The `machine.SRC` and `machine.GUARD_CONDS` orders."""
    machine = json.loads(Path(path).read_text(encoding="utf-8"))
    sources = list(machine["src"])
    guards = list(machine["guard_conds"])
    require(len(sources) == 39, f"{path}: expected 39 sources, found {len(sources)}")
    require(len(guards) == 62, f"{path}: expected 62 guard conditions, found {len(guards)}")
    require(guards[0] == "TRUE", f"{path}: guard 0 is not TRUE")
    return sources, guards


def header_constants(snapshot):
    """The generated headers' `S_*`/`G_*` slot constants and the output map."""
    text = "".join(snapshot[name].decode("latin-1") for name in sorted(snapshot)
                   if name.endswith(".vh"))
    values = {}
    for name, pattern, base in HEADER_PARAMS:
        match = re.search(pattern, text)
        require(match is not None, f"{name}: constant pattern changed in the headers")
        values[name] = int(match.group(1), base)
    sources = {m.group(1): int(m.group(2))
               for m in re.finditer(r"localparam \[5:0\] S_(\w+) = 6'd(\d+);", text)}
    guards = {m.group(1): int(m.group(2))
              for m in re.finditer(r"localparam \[5:0\] G_(\w+) = 6'd(\d+);", text)}
    require(len(sources) == 39, f"md2_defs.vh: {len(sources)} S_* constants, expected 39")
    require(len(guards) == 62, f"md2_defs.vh: {len(guards)} G_* constants, expected 62")
    values["sources"] = sources
    values["guards"] = guards
    return values


def flags_set_code(path=GLUE_LEAN):
    """The `D_FLAGS_SET` literal transcribed in `Metronome/Glue.lean`."""
    text = Path(path).read_text(encoding="utf-8")
    match = re.search(r"def flagsSetDst : BitVec 6 := (\d+)", text)
    require(match is not None, f"{path}: flagsSetDst pattern changed")
    return int(match.group(1), 10)


def lean_table(path, function, count):
    """The slot order of `srcAt`/`guardAt`, read from its arm comments."""
    text = Path(path).read_text(encoding="utf-8")
    start = text.index(f"def {function} ")
    end = text.index("\n\n", text.index("| _ =>", start))
    block = text[start:end]
    arms = re.findall(r"^\s*\| (\d+) => .*?-- (\S+)", block, re.MULTILINE)
    indices = [int(index) for index, _ in arms]
    require(indices == list(range(count)),
            f"{path}: {function} arms are {indices}, expected 0..{count - 1}")
    return [name for _, name in arms]


def check_tables(snapshot, lean_path=GLUE_LEAN, machine_path=MACHINE_JSON):
    """The ISA table, the header constants and the Lean transcription agree."""
    sources, guards = machine_tables(machine_path)
    header = header_constants(snapshot)
    for index, name in enumerate(sources):
        key = name.replace(".", "_")
        require(header["sources"].get(key) == index,
                f"md2_defs.vh: S_{key} is {header['sources'].get(key)}, "
                f"machine.SRC says {index}")
    for index, name in enumerate(guards):
        key = name.replace(".", "_")
        require(header["guards"].get(key) == index,
                f"md2_defs.vh: G_{key} is {header['guards'].get(key)}, "
                f"machine.GUARD_CONDS says {index}")
    require(header["flags_set"] == flags_set_code(lean_path),
            f"md2_defs.vh: D_FLAGS_SET is {header['flags_set']}, "
            f"Metronome/Glue.lean says {flags_set_code(lean_path)}")
    spec_sources = lean_table(lean_path, "srcAt", 39)
    spec_guards = lean_table(lean_path, "guardAt", 62)
    require(spec_sources == sources,
            f"{lean_path}: srcAt's slot comments are {spec_sources}, not machine.SRC")
    require(spec_guards == guards,
            f"{lean_path}: guardAt's slot comments are {spec_guards}, "
            "not machine.GUARD_CONDS")
    return {**header, "sources": sources, "guards": guards}


# --------------------------------------------------------------------------- extraction


def net(top, name, width):
    return corectl.net(top, name, width)


def bind(cone, name, width, value):
    """Bind a named net (port, register output or driven net) as a free leaf."""
    return cone.overwrite(name, width, value)


def fresh(name, root, roots):
    cone = GlueCone(name, root)
    for leaf, width, value in roots:
        bind(cone, leaf, width, value)
    return cone


def root_expr(cone, bits):
    """A root bus as a Lean term: a scalar root is a `Bool`, as everywhere else."""
    if len(bits) == 1:
        return cone._bit_bool(bits[0])
    return cone.expression(tuple(bits))


def def_text(name, params, rtype, lines, expr, doc=""):
    body = "\n".join(lines)
    return (f"/-- {doc} -/\ndef {name} {params} : {rtype} :=\n"
            f"{body}\n  {expr}\n")


def theorem_text(name, params, statement, tactic):
    return (f"/-- `{name}` is the specification's. -/\n"
            f"theorem {name}_spec {params} :\n    {statement} := by\n{tactic}\n")


SLOT_TACTIC = "  simp only [{defs}]\n  all_goals bv_decide"


def emit_sources(modules, table):
    """One definition and theorem per source slot."""
    top = modules[TOP]
    roots = net(top, "srcs", 512)
    defs, theorems, names = [], [], []
    for k in range(64):
        cone = fresh(f"src{k}", top, SRC_FREE)
        expr = cone.expression(tuple(roots[8 * k:8 * k + 8]))
        name = f"rtlSrc{k}"
        label = table[k] if k < len(table) else "unused"
        defs.append(def_text(name, SRC_DEF_PARAMS, "BitVec 8", cone.lines, expr,
                             f"`srcs[{8 * k} +: 8]` (slot `S_{label}`, index {k})."))
        theorems.append(theorem_text(
            name, SRC_PARAMS, f"{name} {SRC_ARGS} = srcAt {k} s",
            SLOT_TACTIC.format(defs=f"{name}, srcAt, slice, bitAt, bitByte")))
        names.append(f"{name}_spec")
    return "\n".join(defs), "\n".join(theorems), names


def emit_guards(modules, table):
    """One definition and theorem per guard slot."""
    top = modules[TOP]
    roots = net(top, "guards", 64)
    defs, theorems, names = [], [], []
    for k in range(64):
        cone = fresh(f"grd{k}", top, GUARD_FREE)
        expr = root_expr(cone, (roots[k],))
        name = f"rtlGuard{k}"
        label = table[k] if k < len(table) else "unused"
        defs.append(def_text(name, GUARD_DEF_PARAMS, "Bool", cone.lines, expr,
                             f"`guards[{k}]` (slot `G_{label}`, index {k})."))
        theorems.append(theorem_text(
            name, GUARD_PARAMS, f"{name} {GUARD_ARGS} = guardAt {k} g",
            SLOT_TACTIC.format(defs=f"{name}, guardAt, slice, bitAt")))
        names.append(f"{name}_spec")
    return "\n".join(defs), "\n".join(theorems), names


def emit_lines(modules):
    """The four `g_line` bundles."""
    top = modules[TOP]
    roots = net(top, "g_line", 20)
    defs, theorems, names = [], [], []
    for k in range(4):
        cone = fresh(f"gln{k}", top, LINE_FREE)
        expr = cone.expression(tuple(roots[5 * k:5 * k + 5]))
        name = f"rtlGLine{k}"
        defs.append(def_text(name, LINE_DEF_PARAMS, "BitVec 5", cone.lines, expr,
                             f"`g_line[{5 * k} +: 5]`, line {k}'s guard bundle."))
        theorems.append(theorem_text(
            name, LINE_PARAMS, f"{name} {LINE_ARGS} = lineGuard {k} g",
            SLOT_TACTIC.format(defs=f"{name}, lineGuard, slice, bitAt")))
        names.append(f"{name}_spec")
    return "\n".join(defs), "\n".join(theorems), names


# The control registers: (elaborated net, Lean name, field, width, free leaves,
# the definition's parameters, the definition's arguments, the specification).
def control_cases():
    err_leaves = (
        ("conflict", 1, "conflict"), ("memhaz", 1, "memhaz"),
        ("cw_overrun", 1, "cwOverrun"), ("t_late", 6, "tLate"),
        ("t_ovr", 6, "tOvr"), ("l_tapmiss", 4, "lTapmiss"),
        ("s_starved", 2, "sStarved"),
    )
    err_params = [("conflict", "Bool"), ("memhaz", "Bool"), ("cwOverrun", "Bool"),
                  ("tLate", "BitVec 6"), ("tOvr", "BitVec 6"),
                  ("lTapmiss", "BitVec 4"), ("sStarved", "BitVec 2")]
    err_args = "i.conflict i.memhaz i.cwOverrun i.tLate i.tOvr i.lTapmiss i.sStarved"
    return (
        dict(net="run_g", name="rtlRunG", field="runG", width=1,
             leaves=(("c_wr_run", 1, "wrRun"), ("h_wd", 8, "hWd"), RESET),
             params=[("cur", "Bool"), ("wrRun", "Bool"), ("hWd", "BitVec 8"),
                     ("resetN", "Bool")],
             args="s.runG i.wrRun i.hWd i.resetN", spec="(step s i).runG",
             next="runG_next",
             doc="`RUN_global`: a `CTRL.RUN` write loads bit 0 (§9)."),
        dict(net="irqen", name="rtlIrqEn", field="irqEn", width=2,
             leaves=(("c_wr_irqen", 1, "wrIrqEn"), ("h_wd", 8, "hWd"), RESET),
             params=[("cur", "BitVec 2"), ("wrIrqEn", "Bool"), ("hWd", "BitVec 8"),
                     ("resetN", "Bool")],
             args="s.irqEn i.wrIrqEn i.hWd i.resetN", spec="(step s i).irqEn",
             next="irqEn_next",
             doc="`IRQEN[1:0]`: a `CTRL.IRQEN` write loads bits 1:0 (§9)."),
        dict(net="err", name="rtlErr", field=None, width=1, leaves=err_leaves,
             params=err_params, args=err_args, spec="err i", next=None,
             doc="`ERR`: the §9 error list, `CWOVR` included (§13.1)."),
        dict(net="irq", name="rtlIrq", field="irq", width=1,
             leaves=(("irqen", 2, "irqEn"), ("outv", 1, "outv")) + err_leaves + (RESET,),
             params=[("irqEn", "BitVec 2"), ("outv", "Bool")] + err_params +
                    [("resetN", "Bool")],
             args=("s.irqEn s.outv i.conflict i.memhaz i.cwOverrun i.tLate i.tOvr "
                   "i.lTapmiss i.sStarved i.resetN"),
             spec="(step s i).irq", next="irq_next",
             doc="`IRQ = (IRQEN[0] && OUTV) || (IRQEN[1] && ERR)` (§9)."),
        dict(net="db", name="rtlDb", field="db", width=6,
             leaves=(("c_wr_db", 1, "wrDb"), ("h_wd", 8, "hWd"),
                     ("frz", 1, "frz"), RESET),
             params=[("cur", "BitVec 6"), ("wrDb", "Bool"), ("hWd", "BitVec 8"),
                     ("frz", "Bool"), ("resetN", "Bool")],
             args="s.db i.wrDb i.hWd i.frz i.resetN", spec="(step s i).db",
             next="db_next",
             doc="`DB`: a `CTRL.DOORBELL` write loads bits 5:0 and a frozen cycle"
                 " holds it (§9, §12.3)."),
        dict(net="fl", name="rtlFl", field="fl", width=16,
             leaves=(("w_flags", 15, "wFlags"), RESET),
             params=[("cur", "BitVec 16"), ("wFlags", "BitVec 15"), ("resetN", "Bool")],
             args="s.fl i.wFlags i.resetN", spec="(step s i).fl", next="fl_next",
             doc="`F`: a `FLAGS` move sets or clears one bit (§6.1)."),
        dict(net="flp", name="rtlFlp", field="flp", width=16,
             leaves=(("fl", 16, "fl"), ("frz", 1, "frz"), RESET),
             params=[("cur", "BitVec 16"), ("fl", "BitVec 16"), ("frz", "Bool"),
                     ("resetN", "Bool")],
             args="s.flp s.fl i.frz i.resetN", spec="(step s i).flp", next="flp_next",
             doc="`FP`: `F` of the previous cycle, held while frozen (§6.1, §12.3)."),
        dict(net="inb", name="rtlInB", field="inB", width=8,
             leaves=(("c_wr_hin", 1, "wrHin"), ("h_wd", 8, "hWd"), RESET),
             params=[("cur", "BitVec 8"), ("wrHin", "Bool"), ("hWd", "BitVec 8"),
                     ("resetN", "Bool")],
             args="s.inB i.wrHin i.hWd i.resetN", spec="(step s i).inB", next="inB_next",
             doc="`INB`: a `CTRL.HOSTIN` write loads the mailbox byte (§9)."),
        dict(net="inv", name="rtlInv", field="inv", width=1,
             leaves=(("c_wr_hin", 1, "wrHin"), ("h_wd", 8, "hWd"),
                     ("rd_hin", 6, "rdHin"), RESET),
             params=[("cur", "Bool"), ("wrHin", "Bool"), ("hWd", "BitVec 8"),
                     ("rdHin", "BitVec 6"), ("resetN", "Bool")],
             args="s.inv i.wrHin i.hWd i.rdHin i.resetN", spec="(step s i).inv",
             next="inv_next",
             doc="`INV`: `HOSTIN` sets it and a `HOST.IN` read clears it (§6, §9)."),
        dict(net="invp", name="rtlInvp", field="invp", width=1,
             leaves=(("inv", 1, "inv"), ("frz", 1, "frz"), RESET),
             params=[("cur", "Bool"), ("inv", "Bool"), ("frz", "Bool"),
                     ("resetN", "Bool")],
             args="s.invp s.inv i.frz i.resetN", spec="(step s i).invp", next="invp_next",
             doc="`INVP`: `INV` of the previous cycle, held while frozen (§12.3)."),
        dict(net="outb", name="rtlOutB", field="outB", width=8,
             leaves=(("w_hout", 15, "wHout"), RESET),
             params=[("cur", "BitVec 8"), ("wHout", "BitVec 15"), ("resetN", "Bool")],
             args="s.outB i.wHout i.resetN", spec="(step s i).outB", next="outB_next",
             doc="`OUTB`: a `HOST.OUT` move loads the mailbox byte (§6.1)."),
        dict(net="outv", name="rtlOutv", field="outv", width=1,
             leaves=(("w_hout", 15, "wHout"), ("c_wr_hst", 1, "wrHst"),
                     ("h_wd", 8, "hWd"), RESET),
             params=[("cur", "Bool"), ("wHout", "BitVec 15"), ("wrHst", "Bool"),
                     ("hWd", "BitVec 8"), ("resetN", "Bool")],
             args="s.outv i.wHout i.wrHst i.hWd i.resetN", spec="(step s i).outv",
             next="outv_next",
             doc="`OUTV`: `HOST.OUT` raises it and `HOSTSTAT` bit 1 clears it (§9)."),
    )


def lean_params(params, extra=()):
    """Render one parenthesised binder group per parameter."""
    groups = [f"({name} : {kind})" for name, kind in params]
    if extra:
        groups.append(f"({' '.join(extra)} : Bool)")
    return " ".join(groups)


def emit_control(modules):
    """The control registers: one definition and theorem each, then the step."""
    top = modules[TOP]
    defs, theorems, names, fields, goals = [], [], [], [], []
    simplifiers = ("slice, bitAt, anyRead, err, any2, any4, any6, doorbellBits, "
                   "flagsWrite, flagsIndex, flagsValue, flagsSetDst, hostOutWrite, "
                   "hostOutData, hostStatClear, setFlag")
    for case in control_cases():
        cone = fresh(case["name"], top, case["leaves"])
        if case["next"] is None:
            root = net(top, case["net"], case["width"])
        else:
            root = cone.register(case["net"], case["width"], "cur")
        expr = root_expr(cone, root)
        extra = [f"x{i}" for i in range(len(cone.dontcare))]
        width = "BitVec %d" % case["width"] if case["width"] > 1 else "Bool"
        defs.append(def_text(case["name"], lean_params(case["params"], extra), width,
                             cone.lines, expr, case["doc"]))
        if case["next"] is None:
            tactic = (f"  simp only [rtlErr, err, any2, any4, any6, bitAt]\n"
                      f"  all_goals bv_decide")
        else:
            tactic = (f"  rw [{case['next']}]\n"
                      f"  simp only [{case['name']}, {simplifiers}]\n"
                      f"  all_goals bv_decide")
        theorems.append(theorem_text(
            case["name"], lean_params([("s", "GlueState"), ("i", "GlueInput")], extra),
            f"{case['name']} {case['args']} {' '.join(extra)} = {case['spec']}", tactic))
        names.append(f"{case['name']}_spec")
        if case["field"] is None:
            continue
        if extra:
            call = f"{case['name']} {case['args']} {' '.join(['false'] * len(extra))}"
            goals.append(f"    ({case['name']}_spec s i {' '.join(['false'] * len(extra))})")
        else:
            call = f"{case['name']} {case['args']}"
            goals.append(f"    ({case['name']}_spec s i)")
        fields.append(f"    {case['field']} := {call}")
    return "\n".join(defs), "\n".join(theorems), names, fields, goals


# --------------------------------------------------------------------------- outputs


def check_output_config(modules, header):
    """Every output's config fields are the `cfg` window bytes the map names."""
    top = modules[TOP]
    cfg = net(top, "cfg", 8 * header["cfg_bytes"])
    for k in range(14):
        base = header["out_base"] - header["cfg_lo_i"] + header["out_stride"] * k
        for field, offset, width in (("obind", header["out_bind"], 8),
                                     ("sel", header["out_sel"], 8),
                                     ("lut", header["out_lut"], 32)):
            name = f"g_out[{k}].{field}"
            bits = net(top, name, width)
            expect = tuple(cfg[8 * (base + offset):8 * (base + offset) + width])
            require(bits == expect,
                    f"{name}: not configuration bytes {base + offset}+")
        if k < 8:
            bits = net(top, f"g_out[{k}].g_oe.oe", 32)
            offset = header["out_oe"]
            expect = tuple(cfg[8 * (base + offset):8 * (base + offset) + 32])
            require(bits == expect,
                    f"g_out[{k}].g_oe.oe: not configuration bytes {base + offset}+")


def find_register(top, bit):
    """The single register whose output is this one bit; returns its D bus."""
    matches = [cell for cell in top["cells"].values()
               if cell["type"] in ("$dff", "$adff") and
               tuple(cell["connections"]["Q"]) == (bit,)]
    require(len(matches) == 1, f"bit {bit}: expected exactly one register driver")
    require(matches[0]["type"] == "$dff", f"bit {bit}: expected a plain register")
    require(tuple(matches[0]["connections"]["CLK"]) ==
            tuple(top["ports"]["clk"]["bits"]), f"bit {bit}: unexpected clock")
    return tuple(matches[0]["connections"]["D"])


def emit_outputs(modules):
    """Per output: the index equality and the register equality (OUT, OEN)."""
    top = modules[TOP]
    idx_defs, idx_theorems, out_defs, out_theorems, names = [], [], [], [], []
    out_bits = net(top, "o_out", 14)
    oe_bits = net(top, "o_oe", 8)
    for k in range(14):
        leaves = (("l_comm", 16, "comm"), ("l_pina", 4, "pinA"),
                  ("l_pinb", 4, "pinB"), ("l_seg", 8, "seg"),
                  ("g_out[%d].obind" % k, 8, "bind"),
                  ("g_out[%d].sel" % k, 8, "sel"))
        cone = fresh(f"idx{k}", top, leaves)
        expr = cone.expression(net(top, f"g_out[{k}].idx", 5))
        idx_defs.append(def_text(f"rtlIdx{k}", OUT_IDX_DEF_PARAMS, "BitVec 5",
                                 cone.lines, expr,
                                 f"`g_out[{k}].idx`: the output table index."))
        idx_theorems.append(
            f"/-- `rtlIdx{k}` is §8/§12.1's table index. -/\n"
            f"theorem rtlIdx{k}_spec (c : OutCfg) :\n"
            f"    rtlIdx{k} c.bind c.sel c.comm c.pinA c.pinB c.seg = outIdx c := by\n"
            f"  simp only [rtlIdx{k}, outIdx, outBound, outB0, outB1, outB2, "
            f"outLiveB1, outLiveB2, outSeg, outComm, outLine, slice, bitAt]\n"
            f"  all_goals bv_decide\n")
        names.append(f"rtlIdx{k}_spec")

        # The OUT register: the index net is replaced by its specification, so
        # only the table read and the two holds remain in the cone.
        register = find_register(top, out_bits[k])
        cone = fresh(f"out{k}", top, [("g_out[%d].lut" % k, 32, "lut"),
                                      ("frz", 1, "frz"), RESET])
        cone.bound[(out_bits[k],)] = "cur"
        bind(cone, f"g_out[{k}].idx", 5, "idx")
        expr = root_expr(cone, register)
        out_defs.append(def_text(f"rtlOut{k}", "(cur frz resetN : Bool) (idx : BitVec 5) "
                                 "(lut : BitVec 32)", "Bool", cone.lines, expr,
                                 f"`o_out[{k}]`'."))
        out_theorems.append(
            f"/-- `o_out[{k}]`' is `outNext` at the table index `rtlIdx{k}`. -/\n"
            f"theorem rtlOut{k}_full (c : OutCfg) (cur frz resetN : Bool) :\n"
            f"    rtlOut{k} cur frz resetN (rtlIdx{k} c.bind c.sel c.comm c.pinA "
            f"c.pinB c.seg) c.lut = outNext c cur resetN frz := by\n"
            f"  rw [rtlIdx{k}_spec]\n"
            f"  simp only [rtlOut{k}, outNext, readBit]\n  all_goals bv_decide\n")
        names.append(f"rtlOut{k}_full")
        if k < 8:
            register = find_register(top, oe_bits[k])
            cone = fresh(f"oe{k}", top, [("g_out[%d].g_oe.oe" % k, 32, "oe"),
                                         ("frz", 1, "frz"), RESET])
            cone.bound[(oe_bits[k],)] = "cur"
            bind(cone, f"g_out[{k}].idx", 5, "idx")
            expr = root_expr(cone, register)
            out_defs.append(def_text(f"rtlOe{k}", "(cur frz resetN : Bool) "
                                     "(idx : BitVec 5) (oe : BitVec 32)", "Bool",
                                     cone.lines, expr, f"`o_oe[{k}]`'."))
            out_theorems.append(
                f"/-- `o_oe[{k}]`' is `oeNext` at the table index `rtlIdx{k}`. -/\n"
                f"theorem rtlOe{k}_full (c : OutCfg) (cur frz resetN : Bool) :\n"
                f"    rtlOe{k} cur frz resetN (rtlIdx{k} c.bind c.sel c.comm c.pinA "
                f"c.pinB c.seg) c.oe = oeNext c cur resetN frz := by\n"
                f"  rw [rtlIdx{k}_spec]\n"
                f"  simp only [rtlOe{k}, oeNext, readBit]\n  all_goals bv_decide\n")
            names.append(f"rtlOe{k}_full")
    return ("\n".join(idx_defs), "\n".join(idx_theorems), "\n".join(out_defs),
            "\n".join(out_theorems), names)


def check_pin_wiring(modules):
    """The three pin buses are exactly the registers' bits (SPEC_V2 §8)."""
    top = modules[TOP]
    uo = net(top, "uo_out", 8)
    uio = net(top, "uio_out", 8)
    uoe = net(top, "uio_oe", 8)
    out_bits = net(top, "o_out", 14)
    oe_bits = net(top, "o_oe", 8)
    require(tuple(uio) == tuple(out_bits[:8]), "uio_out is not o_out[7:0]")
    require(tuple(uoe) == tuple(oe_bits), "uio_oe is not o_oe")
    require("irq" in top["netnames"],
            "uo_out[1]: the IRQ register is not in the design "
            "(is bit 1 still IRQ?)")
    require("miso" in top["netnames"], "uo_out[0]: the MISO net is not in the design")
    require(uo[0] == net(top, "miso", 1)[0], "uo_out[0] is not miso")
    require(uo[1] == net(top, "irq", 1)[0], "uo_out[1] is not irq")
    require(tuple(uo[2:]) == tuple(out_bits[8:14]), "uo_out[7:2] is not o_out[13:8]")


def emit_pins(modules):
    """The three top-level pin buses."""
    top = modules[TOP]
    check_pin_wiring(modules)
    uo = net(top, "uo_out", 8)
    uio = net(top, "uio_out", 8)
    uoe = net(top, "uio_oe", 8)
    cone = fresh("pins", top, [("o_out", 14, "out"), ("o_oe", 8, "oe"),
                               ("irq", 1, "irq"), ("miso", 1, "miso")])
    parts = [cone.expression(uo), cone.expression(uio), cone.expression(uoe)]
    require(len(cone.dontcare) == 0, "pins: unexpected x bits")
    definition = (f"/-- The three top-level pin buses. -/\n"
                  f"def rtlPins (out : BitVec 14) (oe : BitVec 8) (irq miso : Bool) :\n"
                  f"    BitVec 8 × BitVec 8 × BitVec 8 :=\n"
                  + "\n".join(cone.lines) +
                  f"\n  ({parts[0]},\n   {parts[1]},\n   {parts[2]})\n")
    theorem = (f"/-- The pin buses are §8's: `uo_out = {{OUT[13:8], IRQ, MISO}}`, "
               f"`uio_out = OUT[7:0]`, `uio_oe = OEN`. -/\n"
               f"theorem rtlPins_spec (out : BitVec 14) (oe : BitVec 8) "
               f"(irq miso : Bool) :\n"
               f"    rtlPins out oe irq miso = pins out oe irq miso := by\n"
               f"  simp only [rtlPins, pins, bitByte, slice]\n"
               f"  all_goals bv_decide\n")
    return definition, theorem


def extract(modules, header, tables):
    """Every block of the cut, as Lean text and theorem names."""
    check_pin_wiring(modules)
    check_output_config(modules, header)
    src_defs, src_theorems, src_names = emit_sources(modules, tables["sources"])
    grd_defs, grd_theorems, grd_names = emit_guards(modules, tables["guards"])
    gln_defs, gln_theorems, gln_names = emit_lines(modules)
    ctl_defs, ctl_theorems, ctl_names, fields, goals = emit_control(modules)
    idx_defs, idx_theorems, out_defs, out_theorems, out_names = emit_outputs(modules)
    pins_def, pins_theorem = emit_pins(modules)
    return {
        "src_defs": src_defs, "src_theorems": src_theorems,
        "grd_defs": grd_defs, "grd_theorems": grd_theorems,
        "gln_defs": gln_defs, "gln_theorems": gln_theorems,
        "ctl_defs": ctl_defs, "ctl_theorems": ctl_theorems,
        "step_fields": "\n".join(fields), "step_goals": "\n".join(goals),
        "idx_defs": idx_defs, "idx_theorems": idx_theorems,
        "out_defs": out_defs, "out_theorems": out_theorems,
        "pins_def": pins_def, "pins_theorem": pins_theorem,
        "names": (src_names + grd_names + gln_names + ctl_names + out_names +
                  ["rtlPins_spec", "rtlStep_eq_step", "rtlStateAt_eq",
                   "rtl_trace_result", "rtl_trace_irq_quiet",
                   "rtl_trace_flp_frozen", "rtl_trace_db_frozen"]),
        "counts": {"sources": 64, "guards": 64, "lines": 4,
                   "control": len(ctl_names), "outputs": 14, "oe": 8},
    }


def lean_glue(info, fingerprint):
    template = TEMPLATE.read_text(encoding="utf-8")
    values = {"TOP": TOP, "FINGERPRINT": fingerprint,
              "AXIOMS": "\n".join(f"#print axioms {name}" for name in info["names"])}
    for key in ("src_defs", "src_theorems", "grd_defs", "grd_theorems",
                "gln_defs", "gln_theorems", "ctl_defs", "ctl_theorems",
                "step_fields", "step_goals", "idx_defs", "idx_theorems",
                "out_defs", "out_theorems", "pins_def", "pins_theorem"):
        values[key.upper()] = info[key]
    for name, value in values.items():
        require("{{" + name + "}}" in template,
                f"GlueEquivalence.lean.in: missing {{{{{name}}}}} placeholder")
        template = template.replace("{{" + name + "}}", str(value))
    require("{{" not in template, "GlueEquivalence.lean.in: unsubstituted placeholder")
    return template


# --------------------------------------------------------------------------- audit


def parse_axioms(text):
    """The `#print axioms` records, joining the pretty-printer's wrapped lines."""
    found = {}
    lines = text.splitlines()
    index = 0
    while index < len(lines):
        line = lines[index].strip()
        match = AXIOM_START.match(line)
        if match is not None:
            name, rest = match.group(1), match.group(2)
            while "]" not in rest and index + 1 < len(lines):
                index += 1
                rest += " " + lines[index].strip()
            rest = rest.split("]", 1)[0]
            found[name] = [entry.strip() for entry in rest.split(",") if entry.strip()]
        else:
            plain = NO_AXIOM_START.match(line)
            if plain is not None:
                found[plain.group(1)] = []
        index += 1
    return found


def failed_theorem(source, text, filename):
    """The generated declaration a rejected Lean run reported first."""
    first = ERROR_LINE.search(text.replace("\\", "/"))
    if first is None:
        return None
    line = int(first.group(1))
    name = None
    for index, declaration in enumerate(source.splitlines(), start=1):
        if index > line:
            break
        match = DECL_LINE.match(declaration)
        if match is not None:
            name = match.group(1)
    return f"{name} (line {line})" if name else f"line {line}"


# --------------------------------------------------------------------------- driver


def check_glue(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the elaborated glue cones and their generated Lean proofs.

    `rtlil_or_json` is a parsed Yosys design, a path to `design.json`, or a
    Verilog source directory to elaborate.  Evidence is written to `out_dir` as
    `<case>.glue.lean`, `<case>.log` and `<case>.axioms.txt`.  Returns a result
    dictionary; a rejected cut raises `GlueRejected` (proof or audit) or
    `UnsupportedRTL` (extraction or wiring).
    """
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-glue-{case}-") as tmp:
        work = Path(tmp)
        is_json = isinstance(rtlil_or_json, dict) or (
            isinstance(rtlil_or_json, (str, Path)) and Path(rtlil_or_json).suffix == ".json")
        if is_json:
            modules = corectl.load_modules(rtlil_or_json)
            fingerprint = "not recorded: parsed design JSON"
            base = Path(rtlil_or_json).parent if isinstance(
                rtlil_or_json, (str, Path)) else ROOT / "src"
            try:
                snapshot = corectl.snapshot_of(base)
            except UnsupportedRTL:
                snapshot = corectl.snapshot_of(ROOT / "src")
        else:
            snapshot = corectl.snapshot_of(rtlil_or_json)
            modules, fingerprint, commands, yosys_log = corectl.elaborate(
                snapshot, work / "rtl", yosys)
            log.append(f"RTL snapshot SHA-256: {fingerprint}\n")
            log.append(f"Yosys command: {commands}\n")
            log.append(yosys_log)

        try:
            tables = check_tables(snapshot)
            header = dict(tables)
            log.append(f"Sources: {len(tables['sources'])} slots, "
                       f"guards: {len(tables['guards'])} slots, "
                       f"D_FLAGS_SET = {tables['flags_set']}\n")
            info = extract(modules, header, tables)
            log.append(f"Extracted: {info['counts']}\n")
            source = lean_glue(info, fingerprint)
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the extraction: {exc}\n")
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise

        result = lean_case(source, f"GlueProof{case}.lean", f"{case}.glue.lean",
                          lake, work, out_dir)
        log.append(result.stdout)
        axioms = parse_axioms(result.stdout)
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
            "counts": info["counts"],
            "theorems": len(info["names"]),
            "fingerprint": fingerprint,
            "source": out_dir / f"{case}.glue.lean",
            "log": out_dir / f"{case}.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            first = next((line.strip() for line in result.stdout.splitlines()
                          if "error:" in line), outcome)
            first = first.split(f"GlueProof{case}.lean:", 1)[-1]
            failing = failed_theorem(source, result.stdout, f"GlueProof{case}.lean")
            raise GlueRejected(f"{case}: {outcome}\n" + "".join(log),
                               reason=f"{outcome}: {failing or first[:200]}",
                               code=result.returncode)
    return report


def glue_mutations():
    """The planted glue regressions, as snapshot transformers."""
    def replace(name, before, after):
        def apply(snapshot):
            require(name in snapshot, f"mutation: missing {name}")
            data = snapshot[name]
            require(data.count(before.encode()) == 1,
                    f"mutation: anchor changed in {name}: {before}")
            return {**snapshot, name: data.replace(before.encode(), after.encode(), 1)}
        return apply

    return (
        # The two flag bytes are swapped in the source vector.
        ("glue_source_slot", replace(
            "project.v",
            "sv[8*S_FLAGS_LO +: 8] = fl[7:0];\n        sv[8*S_FLAGS_HI +: 8] = fl[15:8];",
            "sv[8*S_FLAGS_LO +: 8] = fl[15:8];\n        sv[8*S_FLAGS_HI +: 8] = fl[7:0];")),
        # The accumulator zero guard is inverted.
        ("glue_guard_polarity", replace(
            "project.v",
            "gv[G_ACC_Z] = acc_z;",
            "gv[G_ACC_Z] = ~acc_z;")),
        # `ERR` misses the CWOVR term (§13.1).
        ("glue_err_misses_cwovr", replace(
            "project.v",
            "wire err = conflict | memhaz | cw_overrun | (|t_late) | (|t_ovr) | (|l_tapmiss) | (|s_starved);",
            "wire err = conflict | memhaz | (|t_late) | (|t_ovr) | (|l_tapmiss) | (|s_starved);")),
        # `IRQ` ignores `IRQEN[1]`: a present sticky error drives the interrupt
        # even when it is not enabled.
        ("glue_irq_ignores_err", replace(
            "project.v",
            "irq <= (irqen[0] & outv) | (irqen[1] & err);",
            "irq <= (irqen[0] & outv) | err;")),
        # `FP` updates in a frozen cycle (§12.3 violation).
        ("glue_flp_not_frozen", replace(
            "project.v",
            "if (!frz) flp <= fl;",
            "flp <= fl;")),
        # The doorbell is not held while frozen (§12.3 violation).
        ("glue_db_not_held", replace(
            "project.v",
            "db <= (c_wr_db ? h_wd[NT-1:0] : {NT{1'b0}}) | (frz ? db : {NT{1'b0}});",
            "db <= (c_wr_db ? h_wd[NT-1:0] : {NT{1'b0}});")),
        # The output registers update in a frozen cycle (§12.3 violation).
        ("glue_out_not_frozen", replace(
            "project.v",
            "else if (!frz) o_out[k] <= lut[idx];",
            "else o_out[k] <= lut[idx];")),
        # The IRQ pin is not bit 1 of `uo_out` (§8).
        ("glue_uo_out_irq", replace(
            "project.v",
            "assign uo_out  = {o_out[13:8], irq, miso};",
            "assign uo_out  = {o_out[13:8], outv, miso};")),
    )


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted glue regression is rejected.

    Returns one `(case, rejected, stage, exit)` record per mutation and raises
    `GlueRejected` if any mutant is accepted.
    """
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-glue-mutants-") as tmp:
        for case, transform in glue_mutations():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_glue(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"extraction: {exc}", 1))
                continue
            except GlueRejected as exc:
                records.append((case, True, f"generated Lean: {exc.reason}", exc.code))
                continue
            records.append((case, not report["ok"], report["outcome"], report["exit"]))
    accepted = [case for case, rejected, _, _ in records if not rejected]
    require(not accepted, f"mutants accepted: {', '.join(accepted)}")
    return records


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mutations", action="store_true",
                        help="also check the planted glue regressions")
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
            raise GlueRejected("tool version query failed")

        source_log = []
        for path in (GLUE_LEAN, Path(__file__).resolve(), TEMPLATE, MACHINE_JSON):
            digest = hashlib.sha256(Path(path).read_bytes()).hexdigest()
            source_log.append(f"{digest}  {Path(path).relative_to(ROOT)}")
        (artifacts / "sources.log").write_text("\n".join(source_log) + "\n",
                                              encoding="utf-8")

        build = run([lake, "build", "Metronome.Glue"], HERE)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise GlueRejected("lake build Metronome.Glue failed")

        snapshot = corectl.snapshot_of(ROOT / "src")
        try:
            report = check_glue(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        except GlueRejected as exc:
            emit(f"baseline: {exc.reason}")
            records.append(("baseline", exc.reason, exc.code, False))
            return 1
        except UnsupportedRTL as exc:
            emit(f"baseline: rejected by the extraction: {exc}")
            records.append(("baseline", f"extraction: {exc}", 1, False))
            return 1
        emit(f"baseline: {report['outcome']} ({report['theorems']} theorems, "
             f"{report['counts']})")
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
        raise SystemExit(f"Glue check failed: {exc}") from exc
