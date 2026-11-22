"""Check the elaborated configuration latch bank gate by gate.

The shared suite (`verify.py`) checks the latch bank structurally: every
non-zero mask byte has one clock gate and exactly its masked latch set, the
gate is enabled by `we1` and an `addr1`-only selector, and every latch samples
the right data bit. What it does not check is the gate's address comparator: a
selector that reads the wrong constant, or that ignores an address bit, is an
`addr1`-only cone and passes.

This module closes that hole. It elaborates the design with the same Yosys
recipe as `verify.py` and extracts the gate enable cone of every live byte as a
Lean function of `(we1, addr1)`. The generated Lean proves each cone equal to
`we1 && addr1 == offset` (`enable{k}_spec`, one `bv_decide` per live byte),
builds the family `enableAt` out of a list of those cones, and proves the whole
family statement for every index without a case split:

* `any_enable_spec` — a list induction: at index `k` the family opens exactly
  the gate whose offset is `k`, and any other index opens none;
* `enableAt_spec` — the same statement for the elaborated family (284 gates,
  480 offsets), with no hypothesis;
* `liveAt_addrOf` — the family's gate offsets are exactly the non-zero `MASK`
  bytes of the elaborated parameter, by kernel reduction over the 480 offsets.

`Metronome.Bank`'s independent specification is then instantiated
unconditionally (`bank_step_read`, `bank_write_exact_all`), which is what used
to need `∀ k, enable_k = gateOpen k` as a hypothesis. Extraction fails closed:
an unsupported cell, an undriven net or a register in the cone is an error.

Run it from the repository root:

    python code/tests/lean/bank_check.py
    python code/tests/lean/bank_check.py --mutations

`run_mutations()` plants five required regressions on temporary copies of `src/`
(never the repository): a wrong comparator constant for one byte, a comparator
that ignores address bit 0, two live bytes sharing one address, a gate enable
without `we1`, and an inverted `we1` strobe. The last two are caught by the
structural check because `we1` stops being a direct gate input; the first three
are caught by the generated Lean.
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
from verify import HERE, ROOT, TOP, check_bank_mask, run, run_lean


BANK_CELL = "u_cfg"
BANK_MODULE = "md2_cfg_cells"
GATE_NAME = re.compile(r"g_byte\[(\d+)\]\.g_used\.u_cg")
DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_bank_v4_20261119"
TEMPLATE = HERE / "BankEquivalence.lean.in"
AXIOM_LINE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)


class BankRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated bank."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


class BankVariant(DffCone):
    """A `DffCone` that also decodes Yosys's one-bit `$logic_not` of a bus.

    The generated comparator `addr1 == 0` is lowered to `$logic_not(addr1)`,
    which the shared adapter does not index. Everything else is inherited,
    including the fail-closed behaviour for unsupported or undriven nets.
    """

    def __init__(self, name, module):
        super().__init__(name, module)
        for cell_name, cell in module["cells"].items():
            if cell["type"] != "$logic_not":
                continue
            pins = {pin: tuple(bits) for pin, bits in cell["connections"].items()}
            where = f"{name}.{cell_name} ($logic_not)"
            require(set(pins) == {"A", "Y"} and len(pins["Y"]) == 1,
                    f"{where}: expected one scalar result")
            require(len(pins["A"]) == int(cell["parameters"]["A_WIDTH"], 2) and
                    int(cell["parameters"]["Y_WIDTH"], 2) == 1,
                    f"{where}: unexpected widths")
            self.claim(pins["Y"])
            self.drivers[pins["Y"]] = ("$logic_not", pins, cell["parameters"], where)

    def expression(self, bits):
        driver = self.drivers.get(bits)
        if driver is not None and driver[0] == "$logic_not":
            _, pins, params, where = driver
            width = int(params["A_WIDTH"], 2)
            require(len(bits) == 1 and width > 0, f"{where}: unexpected result bus")
            source = self.expression(pins["A"])
            expr = f"({source} == (0 : BitVec {width}))"
            wire = f"{self.name}{len(self.lines)}"
            self.lines.append(f"  let {wire} := {expr}")
            self.bound[bits] = wire
            return wire
        return super().expression(bits)


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
        raise BankRejected(f"Yosys elaboration failed: {result.stdout.strip()}")
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


def extract_bank(modules):
    """Check the bank structure and extract every live gate enable cone.

    Returns the window size, the elaborated mask, the live offsets, the number
    of latch bits and, per live byte, the Lean let-chain and result expression
    of its enable as a function of the free `we1` and `addr1` inputs.
    """
    top = modules[TOP]
    require(BANK_CELL in top["cells"], f"{TOP}.{BANK_CELL}: missing bank instance")
    cell = top["cells"][BANK_CELL]
    require(cell["type"] in modules, f"{BANK_CELL}: missing specialized module")
    module = modules[cell["type"]]
    require(module["attributes"].get("hdlname") == BANK_MODULE,
            f"{BANK_CELL}: unexpected bank module")

    bytes_n, mask = check_bank_mask(modules)
    live = [k for k in range(bytes_n) if (mask >> (8 * k)) & 0xFF]

    gates = {}
    for name in module["cells"]:
        match = GATE_NAME.fullmatch(name)
        if match:
            gates[int(match.group(1))] = name
    require(sorted(gates) == live,
            "u_cfg: clock-gate set does not match the live mask bytes")

    latch_bits = bin(mask).count("1")
    require(latch_bits > 0, "u_cfg: the bank has no latch")
    clk_bit = tuple(module["ports"]["clk"]["bits"])[0]

    enables = {}
    for k in live:
        gate = module["cells"][gates[k]]
        require(len(gate["connections"]["GATE"]) == 1,
                f"u_cfg: byte {k} gate enable is not scalar")
        require(tuple(gate["connections"]["CLK"]) == (clk_bit,),
                f"u_cfg: byte {k} gate has the wrong clock")
        cone = BankVariant(f"e{k}_", module)
        cone.free("we1", 1, "we1")
        cone.free("addr1", 9, "addr1")
        expression = cone.expression(tuple(gate["connections"]["GATE"]))
        enables[k] = (list(cone.lines), expression)

    return {"bytes": bytes_n, "mask": mask, "live": live,
            "latch_bits": latch_bits, "enables": enables}


def lean_bank(info, fingerprint):
    """Emit the Lean module for the extracted gate family.

    The generated part is data: the elaborated mask, one cone per live byte with
    its per-byte equivalence, and the gate list. The proofs that assemble the
    family live in `BankEquivalence.lean.in`; the template is inserted after the
    definitions with the two witness offsets substituted.
    """
    bytes_n = info["bytes"]
    mask = info["mask"]
    live = info["live"]
    holes = [k for k in range(bytes_n) if ((mask >> (8 * k)) & 0xFF) == 0]
    require(holes, "u_cfg: no mask-zero byte to use as a hole witness")
    live_bits = 0
    for k in live:
        live_bits |= 1 << k

    chunks = [f"""import Metronome.Bank
import Std.Tactic.BVDecide

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {fingerprint}
-- Bank: the `{BANK_MODULE}` instance `{TOP}.{BANK_CELL}`. The mask bytes come
-- from its elaborated `MASK` parameter; the enable cones come from the GATE net
-- of every `g_byte[k].g_used.u_cg` cell, with `we1` and `addr1` bound free.
-- {len(live)} of {bytes_n} mask bytes are non-zero ({info['latch_bits']} latch
-- bits), so the family has {len(live)} gates and {len(holes)} holes.
--
-- The proofs below close the family statement for all {bytes_n} offsets without
-- a case split: one `bv_decide` per live cone (`enable_k_spec`), one induction
-- over the gate list (`any_enable_spec`) and one kernel reduction that ties the
-- gate offsets to the elaborated mask bytes (`liveAt_addrOf`).

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 5000

namespace Metronome.BankEquivalence

/-- Window offsets in the elaborated bank. -/
abbrev cfgBytes : Nat := {bytes_n}

/-- The elaborated `{BANK_CELL}` `MASK` parameter, one byte per offset. -/
abbrev bankMask : BitVec {8 * bytes_n} := 0x{mask:0{2 * bytes_n}X}

/-- Bit `k` is set iff `MASK` byte `k` is non-zero: the offsets that own latches
and a clock gate. Same vector as the address-decode cut's `liveBytes`. -/
abbrev liveBytes : BitVec cfgBytes := 0x{live_bits:0{bytes_n // 4}X}

/-- The MASK byte of offset `k`, read from the elaborated parameter. -/
def paramMask (k : Fin cfgBytes) : BitVec 8 := (bankMask >>> (8 * k.val)).truncate 8

/-- The MASK byte of offset `k` is non-zero, so the byte owns latches. -/
def paramLive (k : Fin cfgBytes) : Bool := paramMask k != 0

/-- One live byte of the elaborated bank: its window offset, the enable cone of
its `g_byte[k].g_used.u_cg` clock gate as a function of the staged write word,
and the per-byte proof that the cone is that offset's comparison. -/
structure Gate where
  /-- The window offset this gate selects. -/
  off : Nat
  /-- The offset fits the nine-bit bank address. -/
  off_lt : off < 512
  /-- The extracted gate enable, from the GATE net of `u_cg`. -/
  fn : Bool → BitVec 9 → Bool
  /-- The extracted cone equals `we1 && addr1 == off` at every address. -/
  spec : ∀ we1 addr1, fn we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 off))
"""]

    for k in live:
        lines, expression = info["enables"][k]
        body = "\n".join(lines + [f"  {expression}"])
        chunks.append(f"""
/-- Gate enable of byte {k}, extracted from `g_byte[{k}].g_used.u_cg`. -/
def enable{k} (we1 : Bool) (addr1 : BitVec 9) : Bool :=
{body}

/-- The extracted gate of byte {k} equals `we1 && addr1 == {k}` at every one of
the 512 addresses, for either strobe value. -/
theorem enable{k}_spec (we1 : Bool) (addr1 : BitVec 9) :
    enable{k} we1 addr1 = (we1 && (addr1 == BitVec.ofNat 9 {k})) := by
  unfold enable{k}
  bv_decide
""")

    entries = ",\n".join(
        f"    ⟨{k}, by decide, enable{k}, enable{k}_spec⟩" for k in live)
    chunks.append(f"""
/-- Every live byte of the elaborated bank: its offset, its extracted enable
cone and its per-byte equivalence. -/
def gates : List Gate :=
  [{entries}]

/-- The offset `k` carries a gate: the extracted family's own live set. -/
def liveAt (k : BitVec 9) : Bool :=
  gates.any (fun g => k.toNat == g.off)

/-- The gate family of the elaborated bank as one function of the byte index and
the staged write word: the cone of the gate at offset `k`, `false` at a mask-zero
or out-of-window index. -/
def enableAt (k : BitVec 9) (we1 : Bool) (addr1 : BitVec 9) : Bool :=
  gates.any (fun g => k.toNat == g.off && g.fn we1 addr1)
""")

    template = TEMPLATE.read_text(encoding="utf-8")
    for placeholder in ("{{LIVE}}", "{{HOLE}}"):
        require(placeholder in template,
                f"BankEquivalence.lean.in: missing {placeholder} placeholder")
    chunks.append(template.replace("{{LIVE}}", str(live[0]))
                          .replace("{{HOLE}}", str(holes[-1])))
    return "".join(chunks)


def axiom_audit(text):
    """Collect the `#print axioms` records from a Lean run."""
    return {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
            for name, axioms in AXIOM_LINE.findall(text)}


def check_bank(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the elaborated bank and its generated Lean proofs.

    `rtlil_or_json` is a parsed Yosys design, a path to `design.json`, or a
    Verilog source directory to elaborate. Evidence is written to `out_dir` as
    `<case>.bank.lean` and `<case>.log`. Returns a result dictionary; a rejected
    bank raises `BankRejected` (proof or audit) or `UnsupportedRTL` (structure).
    """
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-bank-{case}-") as tmp:
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
            info = extract_bank(modules)
            log.append(f"Bank geometry: {info['bytes']} offsets, {len(info['live'])} live "
                       f"byte(s), {info['latch_bits']} latch bit(s)\n")
            source = lean_bank(info, fingerprint)
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the structural bank check: {exc}\n")
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise
        result = run_lean(source, "BankProof.lean", f"{case}.bank.lean",
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
            "bytes": info["bytes"],
            "live_bytes": len(info["live"]),
            "latch_bits": info["latch_bits"],
            "fingerprint": fingerprint,
            "source": out_dir / f"{case}.bank.lean",
            "log": out_dir / f"{case}.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            first = next((line.strip() for line in result.stdout.splitlines()
                          if "error:" in line), outcome)
            first = first.split("BankProof.lean:", 1)[-1]
            raise BankRejected(f"{case}: {outcome}\n" + "".join(log),
                               reason=f"{outcome}: {first[:150]}",
                               code=result.returncode)
    return report


def bank_mutations(info):
    """The planted bank regressions, as snapshot transformers."""
    live = info["live"]
    target = 7 if 7 in live and 7 + 1 < info["bytes"] else live[0]
    require(len(live) >= 2, "mutation: need two live bytes")
    shared_src, shared_dst = live[0], live[1]

    def replace(before, after):
        def apply(snapshot):
            require("md2_cfg_bank.v" in snapshot, "mutation: missing md2_cfg_bank.v")
            data = snapshot["md2_cfg_bank.v"]
            require(data.count(before.encode()) == 1,
                    f"mutation: anchor changed in md2_cfg_bank.v: {before}")
            return {**snapshot,
                    "md2_cfg_bank.v": data.replace(before.encode(), after.encode(), 1)}
        return apply

    return OrderedDict((
        # The comparator of one live byte selects its neighbour instead.
        ("bank_wrong_addr", replace(
            "localparam integer BYTE_ADDR = BASE + k;",
            f"localparam integer BYTE_ADDR = (k == {target}) ? (BASE + k + 1) : (BASE + k);")),
        # Every comparator ignores address bit 0, so each gate covers two offsets.
        ("bank_addr_bit", replace(
            "wire en = we1 && (addr1 == BYTE_ADDR[AW-1:0]);",
            "wire en = we1 && (addr1[AW-1:1] == BYTE_ADDR[AW-1:1]);")),
        # Two live bytes select the same offset. The gate count, the latch sets
        # and the enable shape are unchanged, so only the arithmetic family
        # theorem can see it: two gates would open for one address, and neither
        # matches its own offset.
        ("bank_shared_addr", replace(
            "localparam integer BYTE_ADDR = BASE + k;",
            f"localparam integer BYTE_ADDR = (k == {shared_dst}) ? (BASE + {shared_src}) : (BASE + k);")),
        # The strobe is dropped from every gate enable.
        ("bank_no_we1", replace(
            "wire en = we1 && (addr1 == BYTE_ADDR[AW-1:0]);",
            "wire en = (addr1 == BYTE_ADDR[AW-1:0]);")),
        # The strobe is inverted. `we1` is then no longer a direct input of the
        # gate AND, so the structural check rejects this one; the Boolean
        # equivalence below catches selectors that keep the shape but compute
        # the wrong address.
        ("bank_we1_polarity", replace(
            "wire en = we1 && (addr1 == BYTE_ADDR[AW-1:0]);",
            "wire en = (~we1) && (addr1 == BYTE_ADDR[AW-1:0]);")),
    ))


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted bank regression is rejected.

    Returns one `(case, rejected, stage, exit)` record per mutation and raises
    `BankRejected` if any mutant is accepted. `exit` is the case's own
    verification exit code: 1 for a Lean rejection, 0 when only the structural
    check ran.
    """
    out_dir = Path(out_dir)
    with tempfile.TemporaryDirectory(prefix="metronome-bank-base-") as tmp:
        modules, _, _, _ = elaborate(snapshot, Path(tmp) / "rtl", yosys)
        info = extract_bank(modules)

    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-bank-mutants-") as tmp:
        for case, transform in bank_mutations(info).items():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_bank(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"structural check: {exc}", 0))
                continue
            except BankRejected as exc:
                records.append((case, True, f"generated Lean: {exc.reason}", exc.code))
                continue
            records.append((case, not report["ok"], report["outcome"], report["exit"]))
    accepted = [case for case, rejected, _, _ in records if not rejected]
    require(not accepted, f"mutants accepted: {', '.join(accepted)}")
    return records


def write_status(path, records):
    """Write the run status from the actual per-case exit codes.

    `expectation` says whether the case behaved as required: the baseline must be
    accepted and every mutant must be rejected.
    """
    lines = ["case\toutcome\texit\texpectation"]
    for case, outcome, code, ok in records:
        lines.append(f"{case}\t{outcome}\t{code}\t{'ok' if ok else 'FAILED'}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mutations", action="store_true",
                        help="also check the planted bank regressions")
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
            raise BankRejected("tool version query failed")

        build = run([lake, "build", "Metronome.Bank"], HERE)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise BankRejected("lake build Metronome.Bank failed")

        snapshot = snapshot_of(ROOT / "src")
        report = check_bank(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        emit(f"baseline: {report['outcome']} "
             f"({report['live_bytes']}/{report['bytes']} live bytes, "
             f"{report['latch_bits']} latch bits)")
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
        raise SystemExit(f"Bank check failed: {exc}") from exc
