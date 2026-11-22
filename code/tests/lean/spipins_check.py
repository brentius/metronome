"""Check the SPI pin-layer cut of the Metronome chip top.

`Metronome.HostCmd` proves the host command machine from per-cycle sampled
inputs `sck`, `sckPrev`, `csN` and `mosi`; the shared suite and that cut leave
the pin synchronisers and the SPI pin waveform outside the proof.  This module
closes the layer below them.

It re-elaborates the chip top with the same Yosys recipe as `verify.py` and
extracts, fail-closed, from the elaborated design:

* the three 16-bit synchroniser registers `s1`, `s2`, `sp` of `src/project.v`
  (SPEC_V2 §2): each must be a plain `$dff` on `clk` with no initial value, and
  the reset register `rst_q` must be the asynchronously cleared synchroniser
  output that the always block samples (not the raw pin);
* the `u_host` port wiring: `sck = s2[8]`, `sck_p = sp[8]`, `cs_n = s2[9]`,
  `mosi = s2[10]` and `rst_n = rst_q`.

The extracted next-state logic is emitted as Lean and checked against
`Metronome.SpiPins`'s independent statement of SPEC_V2 §2 (component by
component, with `bv_decide`), together with the wiring equations.  Composed
with the pin-waveform theorems of `Metronome.SpiPins`, the result is that the
elaborated synchronisers, wired as the chip top wires them, turn each SCK pin
edge into exactly one `HostCmd` `SR` cycle at the stated latency.

Run it from the repository root:

    python code/tests/lean/spipins_check.py
    python code/tests/lean/spipins_check.py --mutations

`run_mutations()` plants the required regressions on temporary copies of
`src/` (never the repository): SCK taken from the first synchroniser stage, the
`CS_N`/`MOSI` connections swapped, `sck_p` taken from `s2` instead of `sp`, a
dropped `sp` pipeline stage, and a `s2` that bypasses `s1`.  Every one must be
rejected.
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

from rtlil import DffCone, UnsupportedRTL, require
from verify import HERE, ROOT, TOP, run, run_lean


HOST_CELL = "u_host"
HOST_MODULE = "md2_host"
SYNC_NAMES = ("s1", "s2", "sp")
DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_spipins_v4_20261121"
TEMPLATE = HERE / "SpiPinsEquivalence.lean.in"
AXIOM_LINE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)


class SpiPinsRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the elaborated pin cut."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


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
        raise SpiPinsRejected(f"Yosys elaboration failed: {result.stdout.strip()}")
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
    require(net is not None, f"{TOP}.{name}: missing net")
    require("init" not in net["attributes"], f"{TOP}.{name}: unexpected initial value")
    bits = tuple(net["bits"])
    require(len(bits) == width, f"{TOP}.{name}: expected {width} bits")
    return bits


def sync_register(module, name, width=16):
    """The D bus of the one plain register driving `name`, clocked by `clk`."""
    bits = net_bits(module, name, width)
    matches = [cell for cell in module["cells"].values()
               if cell["type"] in ("$dff", "$adff") and
               tuple(cell["connections"]["Q"]) == bits]
    require(len(matches) == 1, f"{TOP}.{name}: expected exactly one register driver")
    cell = matches[0]
    require(cell["type"] == "$dff",
            f"{TOP}.{name}: expected a register without an asynchronous reset")
    clk = tuple(module["ports"]["clk"]["bits"])
    require(tuple(cell["connections"]["CLK"]) == clk and
            int(cell["parameters"]["CLK_POLARITY"], 2) == 1,
            f"{TOP}.{name}: expected posedge clk")
    return bits, tuple(cell["connections"]["D"])


def reset_register(module):
    """The sampled reset register `rst_q`, as the cut abstracts it.

    The rest of the suite samples `resetN` once per cycle, so the cut binds
    `rst_q` as a free input.  To keep that sound the net must be the output of
    the asynchronously cleared reset synchroniser of `src/project.v` and not the
    `rst_n` pin itself.
    """
    bits = net_bits(module, "rst_q", 1)
    rst_n = tuple(module["ports"]["rst_n"]["bits"])
    require(len(rst_n) == 1, f"{TOP}.rst_n: expected one bit")
    matches = [cell for cell in module["cells"].values()
               if cell["type"] in ("$dff", "$adff") and
               tuple(cell["connections"]["Q"]) == bits]
    require(len(matches) == 1, f"{TOP}.rst_q: expected exactly one register driver")
    cell = matches[0]
    require(cell["type"] == "$adff",
            f"{TOP}.rst_q: expected the asynchronously cleared reset register")
    require(tuple(cell["connections"]["ARST"]) == rst_n and
            int(cell["parameters"]["ARST_POLARITY"], 2) == 0 and
            int(cell["parameters"]["ARST_VALUE"], 2) == 0,
            f"{TOP}.rst_q: expected the active-low asynchronous clear from rst_n")
    return bits


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
    return cell


def extract_pins(modules):
    """Extract the synchroniser next state and the host-link wiring.

    Returns the Lean let-chain, the three next-state field expressions, the four
    host-input field expressions and the layout facts the adapter relied on.
    Extraction is fail-closed: a missing or extra register driver, a wrong
    clock, a wrong asynchronous clear, or a `u_host` connection to any bit other
    than the specified synchroniser bit raises `UnsupportedRTL`.
    """
    top = modules[TOP]
    for port, width in (("clk", 1), ("rst_n", 1), ("ui_in", 8), ("uio_in", 8)):
        port_bits = top["ports"].get(port)
        require(port_bits is not None and
                len(port_bits["bits"]) == width and
                port_bits["direction"] == "input",
                f"{TOP}.{port}: expected a {width}-bit input")

    host = host_module(modules)
    rst_q = reset_register(top)
    require(tuple(host["connections"]["rst_n"]) == rst_q,
            f"{HOST_CELL}.rst_n is not the synchronised reset register rst_q")

    registers = {}
    for name in SYNC_NAMES:
        registers[name] = sync_register(top, name)
    buses = [bits for bits, _ in registers.values()]
    for index, bits in enumerate(buses):
        for other in buses[index + 1:]:
            require(set(bits).isdisjoint(other),
                    f"{TOP}: synchroniser registers share a bit")
    require(not set().union(*map(set, buses)) & set(rst_q),
            f"{TOP}: the synchroniser registers overlap rst_q")

    # The host-link connections, bit by bit.  SPEC_V2 §2: the host sees the
    # synchronised level (`s2`) and the previous level (`sp`).
    wiring = {
        "sck": (8, 1, "s2"),
        "sck_p": (8, 1, "sp"),
        "cs_n": (9, 1, "s2"),
        "mosi": (10, 1, "s2"),
    }
    for port, (bit, width, bus) in wiring.items():
        require(port in host["connections"], f"{HOST_CELL}.{port}: missing connection")
        pins = tuple(host["connections"][port])
        require(len(pins) == width, f"{HOST_CELL}.{port}: expected {width} bit")
        require(pins == (registers[bus][0][bit],),
                f"{HOST_CELL}.{port} is not {bus}[{bit}]")

    cone = DffCone("spipins", top)
    cone.input("ui_in", 8, "input.hi")
    cone.input("uio_in", 8, "input.lo")
    cone.free("rst_q", 1, "input.resetN")
    fields = {}
    for name in SYNC_NAMES:
        data = cone.register(name, 16, f"state.{name}")
        fields[name] = cone.expression(data)
    host_fields = {
        "hostSck": f"({cone.expression(tuple(host['connections']['sck']))} != 0)",
        "hostSckPrev": f"({cone.expression(tuple(host['connections']['sck_p']))} != 0)",
        "hostCsN": f"({cone.expression(tuple(host['connections']['cs_n']))} != 0)",
        "hostMosi": f"({cone.expression(tuple(host['connections']['mosi']))} != 0)",
    }
    return {
        "lets": "\n".join(cone.lines),
        "fields": fields,
        "host_fields": host_fields,
        "registers": len(SYNC_NAMES) + 1,
        "sck_bit": wiring["sck"][0],
    }


def lean_pins(info, fingerprint):
    """Emit the extracted synchroniser transition and host wiring as Lean."""
    fields = info["fields"]
    host_fields = info["host_fields"]
    host_defs = "\n\n".join(f"/-- The elaborated `u_host.{port}` connection. -/\n"
                            f"def {name} (state : Sync) : Bool := {expr}"
                            for name, expr, port in (
                                ("hostSck", host_fields["hostSck"], "sck"),
                                ("hostSckPrev", host_fields["hostSckPrev"], "sck_p"),
                                ("hostCsN", host_fields["hostCsN"], "cs_n"),
                                ("hostMosi", host_fields["hostMosi"], "mosi")))
    return f"""import Metronome.SpiPins

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {fingerprint}
-- Synchronisers: the top-level registers `s1`, `s2`, `sp` of `{TOP}`.
-- Host wiring: `{HOST_CELL}` gets `sck = s2[8]`, `sck_p = sp[8]`,
-- `cs_n = s2[9]`, `mosi = s2[10]` and `rst_n = rst_q`; the extraction checks
-- every one of those bit identities and rejects the design otherwise.

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Metronome.SpiPins

/-- The elaborated synchroniser transition of `{TOP}`: the next value of the
registers `s1`, `s2`, `sp`. -/
def rtlStep (state : Sync) (input : Input) : Sync :=
{info['lets']}
  ⟨{fields['s1']}, {fields['s2']}, {fields['sp']}⟩

{host_defs}

/-- The elaborated host-link input word: the four synchronised pin levels as the
`{HOST_CELL}` instance receives them, plus the free data-RAM inputs. -/
def hostWord (rst : Bool) (state : Sync) (rdData hland : Bool) : HostCmd.Input :=
  ⟨rst, hostSck state, hostSckPrev state, hostCsN state, hostMosi state, rdData, hland⟩

end Metronome.SpiPins

"""


def axiom_audit(text):
    """Collect the `#print axioms` records from a Lean run."""
    return {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
            for name, axioms in AXIOM_LINE.findall(text)}


def check_spipins(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the elaborated pin layer and its generated Lean proofs.

    `rtlil_or_json` is a parsed Yosys design, a path to `design.json`, or a
    Verilog source directory to elaborate.  Evidence is written to `out_dir` as
    `<case>.spipins.lean` and `<case>.log`.  Returns a result dictionary; a
    rejected cut raises `SpiPinsRejected` (proof or audit) or `UnsupportedRTL`
    (structure or wiring).
    """
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-spipins-{case}-") as tmp:
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
            info = extract_pins(modules)
            log.append(f"Pin cut: {info['registers']} registers extracted, "
                       f"host wiring sck = s2[{info['sck_bit']}]\n")
            source = lean_pins(info, fingerprint)
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the structural pin check: {exc}\n")
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise
        source += TEMPLATE.read_text(encoding="utf-8")
        result = run_lean(source, "SpiPinsProof.lean", f"{case}.spipins.lean",
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
            "fingerprint": fingerprint,
            "source": out_dir / f"{case}.spipins.lean",
            "log": out_dir / f"{case}.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            first = next((line.strip() for line in result.stdout.splitlines()
                          if "error:" in line), outcome)
            first = first.split("SpiPinsProof.lean:", 1)[-1]
            raise SpiPinsRejected(f"{case}: {outcome}\n" + "".join(log),
                                  reason=f"{outcome}: {first[:150]}",
                                  code=result.returncode)
    return report


def spipins_mutations():
    """The planted pin-layer regressions, as snapshot transformers."""
    def replace(before, after):
        def apply(snapshot):
            require("project.v" in snapshot, "mutation: missing project.v")
            data = snapshot["project.v"]
            require(data.count(before) == 1,
                    f"mutation: anchor changed in project.v: {before!r}")
            snapshot = dict(snapshot)
            snapshot["project.v"] = data.replace(before, after, 1)
            return snapshot
        return apply

    return (
        # The host samples SCK one stage too early: the second synchroniser
        # stage is bypassed for SCK only.
        ("spipins_sck_from_s1", replace(b".sck(s2[8])", b".sck(s1[8])")),
        # CS_N and MOSI reach the host on each other's pins.
        ("spipins_cs_mosi_swap",
         replace(b".cs_n(s2[9]), .mosi(s2[10])", b".cs_n(s2[10]), .mosi(s2[9])")),
        # The edge detector loses its third delay stage.
        ("spipins_sckp_from_s2", replace(b".sck_p(sp[8])", b".sck_p(s2[8])")),
        # `sp` no longer delays `s2` by one cycle: the edge detector would see
        # two synchroniser stages of SCK instead of three.
        ("spipins_sp_stage_dropped", replace(b"sp <= s2;", b"sp <= s1;")),
        # `s2` takes the raw pins: one synchroniser stage is gone for all pins.
        ("spipins_s2_bypass", replace(b"s2 <= s1;", b"s2 <= {ui_in, uio_in};")),
    )


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that every planted pin-layer regression is rejected.

    Returns one `(case, rejected, stage, exit)` record per mutation and raises
    `SpiPinsRejected` if any mutant is accepted.  `exit` is the case's own
    verification exit code: the Lean exit code when the generated proof rejects
    the mutant, 0 when only the structural check ran.
    """
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-spipins-mutants-") as tmp:
        for case, transform in spipins_mutations():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_spipins(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"structural check: {exc}", 0))
                continue
            except SpiPinsRejected as exc:
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
                        help="also check the planted pin-layer regressions")
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
            raise SpiPinsRejected("tool version query failed")

        build = run([lake, "build", "Metronome.SpiPins"], HERE, timeout=1800)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise SpiPinsRejected("lake build Metronome.SpiPins failed")

        snapshot = snapshot_of(ROOT / "src")
        report = check_spipins(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        emit(f"baseline: {report['outcome']} ({report['registers']} registers)")
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
    except (OSError, KeyError, RuntimeError, ValueError, subprocess.TimeoutExpired,
            UnsupportedRTL) as exc:
        raise SystemExit(f"SPI pin check failed: {exc}") from exc
