"""Per-cycle lockstep of the Lean `machine-sim` against the Python cycle model on a lockstep_v2 pin scenario.

    python run_lockstep.py smoke [--out report.json] [--keys 'L0.*,A'] [--ignore 'DMEM.sum'] [--max-cycles N]
                                 [--max-keys 20] [--exe PATH] [--fake-model] [--fake-flip 500:A:0]

Exit code 0 = no mismatch, 1 = mismatch, 2 = harness/exe error.
"""
from __future__ import annotations

import argparse
import collections
import fnmatch
import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for p in (ROOT / "code/tests/lockstep_v2", ROOT / "sim/reference", HERE):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))

from dump_model import dump  # noqa: E402
from lean_proc import LeanError, LeanProc, fake_cmd  # noqa: E402
from metronome2.chip import Chip  # noqa: E402

CHUNK = 128


def _match(key, pats):
    return any(fnmatch.fnmatchcase(key, p) for p in pats)


def run(name, exe_cmd=None, keys=None, ignore=None, max_cycles=None, max_keys=20, check=True, timeout=60.0,
        verbose=True):
    """Returns the report dict (see README)."""
    import scenarios
    scen = scenarios.build(name)
    steps = scen.steps if max_cycles is None else scen.steps[:max_cycles]
    keys, ignore = keys or [], ignore or []
    chip = Chip()
    outs = (0, 0, 0)
    mism: "collections.OrderedDict[str, dict]" = collections.OrderedDict()
    frames = collections.deque(maxlen=6)
    first = None
    t0 = time.time()
    proc = LeanProc(exe_cmd, timeout=timeout)
    report = dict(scenario=name, cycles=len(steps), ok=None, first_mismatch_cycle=None, mismatching_keys=0, mismatches=[],
                  keys_compared=0, seconds=None, check=None)
    try:
        t = 0
        stop = False
        while t < len(steps) and not stop:
            batch = []
            for _ in range(min(CHUNK, len(steps) - t)):
                ui, hi, uio, rst_n = steps[t]
                uio = uio(t, outs) if callable(uio) else uio       # closed loop on the Python model's previous outputs
                hi = hi(t, outs) if callable(hi) else hi
                ui = (ui & 0x07) | (hi & 0xF8)
                uio &= 0xFF
                outs = tuple(chip.step(ui, uio, rst_n))
                batch.append((t, ui, uio, rst_n, dump(chip, outs)))
                proc.send(ui, uio, rst_n)
                t += 1
            proc.flush()
            for (tc, ui, uio, rst_n, exp) in batch:
                got = proc.recv()
                frames.append((tc, ui, uio, rst_n))
                ks = list(exp)
                extra = [k for k in got if k not in exp]
                ks += extra
                if keys:
                    ks = [k for k in ks if _match(k, keys)]
                if ignore:
                    ks = [k for k in ks if not _match(k, ignore)]
                report["keys_compared"] = len(ks)
                bad = [k for k in ks if exp.get(k) != got.get(k)]
                for k in bad:
                    if k not in mism:
                        mism[k] = dict(key=k, cycle=tc, python=exp.get(k), lean=got.get(k))
                if bad and first is None:
                    first = tc
                    if verbose:
                        print(f"FIRST MISMATCH {name} cycle {tc} (state after that cycle):")
                        for k in bad:
                            print(f"  {k:14s} python={exp.get(k)!r}  lean={got.get(k)!r}")
                        print("  last pin frames (cycle ui uio rst_n):")
                        for f in frames:
                            print("   ", *f)
                if len(mism) >= max_keys:
                    stop = True
                    break
        if check and scen.check is not None and not stop and max_cycles is None:
            try:
                scen.check(chip)
                report["check"] = "pass"
            except Exception as e:   # scenario's own post-condition on the Python model
                report["check"] = f"FAIL: {e!r}"
    finally:
        proc.close()
    report["first_mismatch_cycle"] = first
    report["mismatching_keys"] = len(mism)
    report["mismatches"] = list(mism.values())
    report["ok"] = not mism
    report["seconds"] = round(time.time() - t0, 2)
    if verbose:
        if mism:
            print(f"{name}: {len(mism)} distinct mismatching key(s) (first cycle each):")
            for v in mism.values():
                print(f"  cycle {v['cycle']:7d}  {v['key']:14s} python={v['python']!r} lean={v['lean']!r}")
        print(f"{name}: {'OK' if not mism else 'MISMATCH'}  {len(steps)} cycles, {report['keys_compared']} keys/cycle, "
              f"{report['seconds']} s" + (f", check {report['check']}" if report["check"] else ""))
    return report


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("scenario")
    ap.add_argument("--out", help="write the JSON report here")
    ap.add_argument("--keys", help="comma-separated key globs to compare (default all)")
    ap.add_argument("--ignore", help="comma-separated key globs to skip")
    ap.add_argument("--max-cycles", type=int)
    ap.add_argument("--max-keys", type=int, default=20, help="stop after this many distinct mismatching keys")
    ap.add_argument("--exe", help="machine-sim path (default: env MACHINE_SIM or code/tests/lean/.lake/build/bin)")
    ap.add_argument("--fake-model", action="store_true", help="use fake_sim.py (second Python model) as the Lean side")
    ap.add_argument("--fake-flip", help="with --fake-model: CYCLE:KEY:BIT planted difference")
    ap.add_argument("--timeout", type=float, default=60.0)
    a = ap.parse_args(argv)
    split = lambda s: [x for x in (s or "").split(",") if x]
    cmd = fake_cmd(a.fake_flip) if a.fake_model else ([a.exe] if a.exe else None)
    try:
        rep = run(a.scenario, cmd, split(a.keys), split(a.ignore), a.max_cycles, a.max_keys, timeout=a.timeout)
    except LeanError as e:
        print(f"HARNESS ERROR: {e}", file=sys.stderr)
        return 2
    if a.out:
        Path(a.out).write_text(json.dumps(rep, indent=1))
    return 0 if rep["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
