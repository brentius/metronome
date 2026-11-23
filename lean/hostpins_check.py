"""Check the composed pin-level host transactions of the Metronome chip top.

The three finished cuts this module composes are

* `Metronome.SpiPins` (`spipins_check.py`): the pin synchronisers and the
  `u_host` wiring, and the pin waveform of a mode-0 write transaction;
* `Metronome.HostCmd` (`hostcmd_check.py`): the byte/address state machine,
  including the `addr` next-state equation `HostCmd.rtlAddr` that the read path
  states as its `AddrOk` hypothesis;
* `Metronome.HostRead` (`hostread_check.py`): the response path (`TX`,
  `rackv`), the read map `rd_val` and the MISO pin.

`Metronome.HostPins` composes them at the pin level (write targets against the
host map, read slots against `rd_val`).  This script re-elaborates the chip top
with the shared recipe, reuses the three cuts' fail-closed extractors and their
proof templates, and emits one Lean file that

* discharges `HostRead.AddrOk` from the host command cut's `HostCmd.rtlAddr`
  through a checked bridge between the two extracted address cones, so the read
  path's trace theorem holds of the RTL without a hypothesis;
* lifts `HostPins.transaction_read_bytes` to the elaborated trace: the bit on
  the MISO pin in slot `k` is the `rdValSpec` of `{AH, AL} + k`;
* lifts the write-target statement to the elaborated strobe.

Run it from the repository root:

    python lean/hostpins_check.py
    python lean/hostpins_check.py --mutations

`check_hostpins(src_dir_or_json, out_dir, *, lake, yosys, case)` is importable
like the other cuts; `run_mutations(snapshot, out_dir, lake, yosys)` plants two
regressions on temporary copies of `src/` (never the repository).
"""

import argparse
from pathlib import Path
import re
import shutil
import sys
import tempfile

from rtlil import UnsupportedRTL, require
from verify import HERE, ROOT, run
import hostcmd_check as hostcmd
import hostread_check as hostread
import spipins_check as spipins

DEFAULT_ARTIFACTS = ROOT / "data" / "raw" / "lean_hostpins_v4_20261121"
TEMPLATE = HERE / "HostPinsEquivalence.lean.in"
AXIOM_LINE = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", re.MULTILINE)
LEAN_TIMEOUT = 900


class HostPinsRejected(RuntimeError):
    """The generated Lean, Yosys or the audit refused the composed cut."""

    def __init__(self, message, reason=None, code=1):
        super().__init__(message)
        self.reason = reason or str(message).splitlines()[0]
        self.code = code


def elaborate(snapshot, work, yosys):
    """Elaborate a source snapshot with the shared recipe."""
    return hostcmd.elaborate(snapshot, work, yosys)


def snapshot_of(directory):
    return hostcmd.snapshot_of(directory)


def load_modules(rtlil_or_json):
    return hostcmd.load_modules(rtlil_or_json)


def extract_read_noaddr(module):
    """The read extract without the address field.

    The composed cut takes the address register's next state from the host
    command cut, so the read extraction binds the other ten registers only.
    `hostread_check.check_address_increment` still runs on the same module: it
    pins `addr_i` to the `addr`/`addr + 1` mux selected by `wr | rack | hland`,
    which is exactly the equation `HostCmd.rtlAddr` proves of the command cut.
    Extraction stays fail-closed: the `byte_in` layout is required and an
    unmodelled register fails.
    """
    next_bits = {}
    for name, width in (("st", 3), ("bitc", 3), ("rx", 7), ("is_rd", 1), ("wr", 1),
                        ("wdata", 8), ("rd", 1), ("rack", 1), ("tx", 8), ("rackv", 8)):
        next_bits[name] = hostcmd.register_data(module, name, width)
    byte_in = hostcmd.net_bits(module, "byte_in", 8)
    mosi = module["ports"]["mosi"]["bits"]
    require(byte_in == (mosi[0],) + hostcmd.net_bits(module, "rx", 7),
            "md2_host.byte_in is not {rx, mosi}")
    hostread.check_address_increment(module)
    cone = hostread.HostReadCone("hostread", module)
    for name, width, value in (
        ("rst_n", 1, "input.resetN"), ("sck", 1, "input.sck"),
        ("sck_p", 1, "input.sckPrev"), ("cs_n", 1, "input.csN"),
        ("mosi", 1, "input.mosi"), ("rd_data", 1, "input.rdData"),
        ("rd_val", 8, "input.rdVal"), ("hland", 1, "input.hland"),
        ("hland_d", 8, "input.hlandD"),
    ):
        cone.input(name, width, value)
    cone.alias("byte_in", 8, "(HostCmd.byteIn (state.toHostCmd 0#8) input.toHostCmd)")
    for name, width, current in hostread.READ_REGISTERS:
        if name != "addr":
            cone.register(name, width, current)
    fields = {name: cone.expression(bits) for name, bits in next_bits.items()}
    require(not cone.registers, "unmodeled read-path state")
    return {"lets": "\n".join(cone.lines), "fields": fields}


def lean_source(parts, fingerprint):
    """The generated prelude: the three extracts, then the three templates."""
    pins, host, read = parts
    return f"""import Metronome.HostPins

-- Generated from Yosys RTLIL. SHA-256 of the RTL snapshot: {fingerprint}
-- Pin layer: the synchronisers `s1`, `s2`, `sp` and the `u_host` wiring
-- ({pins['registers']} registers).  Host command machine: the `md2_host`
-- instance `{hostcmd.HOST_CELL}` ({host['registers']} registers, the command-byte
-- history variable on {host['ghost_cells']} RTL gates).  Read path: the same
-- instance's `tx`/`rackv`, the elaborated `rd_val` mux ({read['registers']}
-- registers, {read['rdval_cells']} read-map cells) and the MISO cone.

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Metronome.SpiPins

/-- The elaborated synchroniser transition of the chip top. -/
def rtlStep (state : Sync) (input : Input) : Sync :=
{pins['lets']}
  \u27e8{pins['fields']['s1']}, {pins['fields']['s2']}, {pins['fields']['sp']}\u27e9

/-- The elaborated `u_host.sck` connection. -/
def hostSck (state : Sync) : Bool := {pins['host_fields']['hostSck']}

/-- The elaborated `u_host.sck_p` connection. -/
def hostSckPrev (state : Sync) : Bool := {pins['host_fields']['hostSckPrev']}

/-- The elaborated `u_host.cs_n` connection. -/
def hostCsN (state : Sync) : Bool := {pins['host_fields']['hostCsN']}

/-- The elaborated `u_host.mosi` connection. -/
def hostMosi (state : Sync) : Bool := {pins['host_fields']['hostMosi']}

/-- The elaborated host-link input word. -/
def hostWord (rst : Bool) (state : Sync) (rdData hland : Bool) : HostCmd.Input :=
  \u27e8rst, hostSck state, hostSckPrev state, hostCsN state, hostMosi state, rdData, hland\u27e9

end Metronome.SpiPins

namespace Metronome.HostCmd

/-- The elaborated host-link command-machine transition. -/
def rtlStep (state : State) (input : Input) : State :=
{host['lets']}
  \u27e8{host['fields']['st']}, {host['fields']['bitc']}, {host['fields']['rx']},
   {host['fields']['is_rd']}, {host['fields']['addr']}, {host['fields']['wr']},
   {host['fields']['wdata']}, {host['fields']['rd']}, {host['fields']['rack']},
   {host['fields']['cmd']}\u27e9

end Metronome.HostCmd

namespace Metronome.HostRead

/-- The elaborated read-path transition (`tx`, `rackv` and the nine shared
registers).  The address register's next state is the host command cut's
`rtlStep`: `extract_read_noaddr` checks that the read cone's `addr_i` is the
same `addr`/`addr + 1` mux, and `HostCmd.rtlAddr` proves that equation. -/
def rtlStep (state : State) (input : Input) : State :=
{read['noaddr']['lets']}
  \u27e8{read['noaddr']['fields']['st']}, {read['noaddr']['fields']['bitc']},
   {read['noaddr']['fields']['rx']}, {read['noaddr']['fields']['is_rd']},
   (HostCmd.rtlStep (state.toHostCmd 0#8) input.toHostCmd).addr,
   {read['noaddr']['fields']['wr']}, {read['noaddr']['fields']['wdata']},
   {read['noaddr']['fields']['rd']}, {read['noaddr']['fields']['rack']},
   {read['noaddr']['fields']['tx']}, {read['noaddr']['fields']['rackv']}\u27e9

/-- The elaborated `rd_val` mux. -/
def rtlRdVal (a : BitVec 16) (state : Regs) : BitVec 8 :=
{read['rdval'][0]}
  {read['rdval'][1]}

/-- Width of the free don't-care vector of `rtlRdValX`. -/
def xWidth : Nat := {read['rdvalx'][2]}

/-- The elaborated `rd_val` mux with every Yosys `x` bit read from `xs`. -/
def rtlRdValX (a : BitVec 16) (state : Regs) (xs : BitVec xWidth) : BitVec 8 :=
{read['rdvalx'][0]}
  {read['rdvalx'][1]}

/-- The elaborated MISO cone of the host module. -/
def rtlMiso (state : State) : Bool :=
{read['miso'][0]}
  {read['miso'][1]}

end Metronome.HostRead

"""


def check_hostpins(rtlil_or_json, out_dir, *, lake=None, yosys=None, case="baseline"):
    """Check the composed pin-level host cuts and their generated Lean proofs."""
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    lake = lake or shutil.which("lake")
    yosys = yosys or shutil.which("yosys")
    require(lake, "lake must be on PATH")
    require(yosys, "yosys must be on PATH")

    log = []
    with tempfile.TemporaryDirectory(prefix=f"metronome-hostpins-{case}-") as tmp:
        work = Path(tmp)
        is_json = isinstance(rtlil_or_json, dict) or (
            isinstance(rtlil_or_json, (str, Path)) and Path(rtlil_or_json).suffix == ".json")
        if is_json:
            modules = load_modules(rtlil_or_json)
            fingerprint = "not recorded: parsed design JSON"
        else:
            snapshot = snapshot_of(rtlil_or_json)
            modules, fingerprint, commands, yosys_log = elaborate(snapshot, work / "rtl", yosys)
            log.append(f"RTL snapshot SHA-256: {fingerprint}\n")
            log.append(f"Yosys command: {commands}\n")
            log.append(yosys_log)

        build = run([lake, "build", "Metronome.HostPins"], HERE, timeout=LEAN_TIMEOUT)
        log.append(build.stdout)
        if build.returncode != 0:
            raise HostPinsRejected(
                f"{case}: lake build Metronome.HostPins failed\n" + "".join(log))
        try:
            header = hostread.check_header()
            hostread.check_read_top(modules, header)
            hostread.check_rdval_cells(modules, header)
            pins = spipins.extract_pins(modules)
            host = hostcmd.extract_host(hostcmd.host_module(modules))
            read = hostread.extract_read(hostcmd.host_module(modules))
            read["noaddr"] = extract_read_noaddr(hostcmd.host_module(modules))
            read["rdval"] = hostread.extract_rdval(modules)
            read["rdvalx"] = hostread.extract_rdval_dontcare(modules, read["rdval"][3])
            read["rdval_cells"] = read["rdval"][2]
            read["miso"] = hostread.extract_miso(modules)
            log.append(f"Composed cut: {pins['registers']} synchroniser registers, "
                       f"{host['registers']} command registers ({host['ghost_cells']} history gates), "
                       f"{read['registers']} read registers, {read['rdval_cells']} read-map cells "
                       f"({read['rdval'][3]} don't-care bits), MISO {read['miso'][1]}\n")
            source = lean_source((pins, host, read), fingerprint)
        except UnsupportedRTL as exc:
            log.append(f"-- {case}: rejected by the structural check: {exc}\n")
            (out_dir / f"{case}.log").write_text("".join(log), encoding="utf-8")
            raise
        source += (HERE / "SpiPinsEquivalence.lean.in").read_text(encoding="utf-8")
        source += (HERE / "HostCmdEquivalence.lean.in").read_text(encoding="utf-8")
        source += "\nnamespace Metronome.HostRead\n\n"
        source += (HERE / "HostReadEquivalence.lean.in").read_text(encoding="utf-8")
        source += "\nend Metronome.HostRead\n\n"
        source += TEMPLATE.read_text(encoding="utf-8")
        proof = work / "HostPinsProof.lean"
        proof.write_text(source, encoding="utf-8")
        (out_dir / f"{case}.hostpins.lean").write_text(source, encoding="utf-8")
        result = run([lake, "env", "lean", "-j1", "-DwarningAsError=true", str(proof)],
                     HERE, timeout=LEAN_TIMEOUT)
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
            "fingerprint": fingerprint,
            "source": out_dir / f"{case}.hostpins.lean",
            "log": out_dir / f"{case}.log",
            "axioms": axioms,
        }
        if not report["ok"]:
            first = next((line.strip() for line in result.stdout.splitlines()
                          if "error:" in line), outcome)
            first = first.split("HostPinsProof.lean:", 1)[-1]
            raise HostPinsRejected(f"{case}: {outcome}\n" + "".join(log),
                                   reason=f"{outcome}: {first[:150]}",
                                   code=result.returncode)
    return report


def axiom_audit(text):
    """Collect the `#print axioms` records from a Lean run."""
    return {name: [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
            for name, axioms in AXIOM_LINE.findall(text)}


def hostpins_mutations():
    """The two planted composed-cut regressions, as snapshot transformers."""
    def replace(filename, before, after):
        def apply(snapshot):
            require(filename in snapshot, f"mutation: missing {filename}")
            data = snapshot[filename]
            require(data.count(before) == 1,
                    f"mutation: anchor changed in {filename}: {before!r}")
            return {**snapshot, filename: data.replace(before, after, 1)}
        return apply

    return [
        # The read response loads TX in the request cycle instead of the
        # acknowledge cycle: the composed slot would carry the wrong byte.
        ("hostpins_tx_early", replace(
            "md2_host.v", b"            tx    <= ack ? ackv : tx;",
            b"            tx    <= (rd | hland) ? ackv : tx;")),
        # The host samples SCK one synchroniser stage early: the pin-level
        # transaction no longer matches the elaborated wiring.
        ("hostpins_sck_from_s1", replace(
            "project.v", b".sck(s2[8])", b".sck(s1[8])")),
    ]


def run_mutations(snapshot, out_dir, lake, yosys):
    """Check that the planted regressions are rejected."""
    out_dir = Path(out_dir)
    records = []
    with tempfile.TemporaryDirectory(prefix="metronome-hostpins-mutants-") as tmp:
        for case, transform in hostpins_mutations():
            src = Path(tmp) / case / "src"
            src.mkdir(parents=True)
            for name, content in transform(snapshot).items():
                (src / name).write_bytes(content)
            try:
                report = check_hostpins(src, out_dir, lake=lake, yosys=yosys, case=case)
            except UnsupportedRTL as exc:
                records.append((case, True, f"structural check: {exc}", 0))
                continue
            except HostPinsRejected as exc:
                records.append((case, True, f"generated Lean: {exc.reason}", exc.code))
                continue
            records.append((case, not report["ok"], report["outcome"], report["exit"]))
    accepted = [case for case, rejected, _, _ in records if not rejected]
    require(not accepted, f"mutants accepted: {', '.join(accepted)}")
    return records


def write_status(path, records):
    lines = ["case\toutcome\texit\texpectation"]
    for case, outcome, code, ok in records:
        lines.append(f"{case}\t{outcome}\t{code}\t{'ok' if ok else 'FAILED'}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mutations", action="store_true",
                        help="also check the planted composed-cut regressions")
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
            raise HostPinsRejected("tool version query failed")

        build = run([lake, "build", "Metronome.SpiPins", "Metronome.HostRead",
                     "Metronome.HostMap", "Metronome.HostPins"], HERE, timeout=LEAN_TIMEOUT)
        (artifacts / "lake.log").write_text(build.stdout, encoding="utf-8")
        emit(build.stdout.rstrip())
        if build.returncode != 0:
            raise HostPinsRejected("lake build failed")

        snapshot = snapshot_of(ROOT / "src")
        report = check_hostpins(ROOT / "src", artifacts, lake=lake, yosys=yosys)
        emit(f"baseline: {report['outcome']}")
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
        raise SystemExit(f"Host pins check failed: {exc}") from exc
