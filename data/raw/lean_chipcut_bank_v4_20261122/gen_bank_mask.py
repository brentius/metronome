#!/usr/bin/env python3
"""Generate the Lean `CFG_MASK` table for Metronome.ChipCut.Discharge.BankWire.

Reads `src/md2_map.vh` (the RTL authority), extracts the 3840-bit `CFG_MASK`
localparam, checks it against the map constants, and prints

  * the 480-entry Lean `List Nat` byte table (byte 0 = least significant byte,
    i.e. `CFG_MASK[8k +: 8]` for byte k, which is `md2_cfg_cells`'s mask of
    window offset k),
  * the per-block byte patterns used by the Lean `decide` checks,
  * the cross-checks recorded in `WIRE_BANK_NOTES.md`.

Usage:  python gen_bank_mask.py [--repo ROOT] [--write]

Nothing is written without `--write`; with it, `cfg_mask.lean.txt` is written
next to this script.
"""
import argparse
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_ROOT = os.path.normpath(os.path.join(HERE, "..", "..", ".."))

# md2_map.vh / Machine.Tables
CFG_LO = 0x2000
CFG_BYTES = 480
CFG_LATCH_BITS = 2112
STRIDES = {"LINE": (0x2000, 0x20, 4), "THREAD": (0x2080, 0x8, 6),
           "LFSR": (0x20C0, 0x8, 2), "STREAM": (0x20D0, 0x8, 2),
           "OUT": (0x2100, 0x10, 14)}


def parse_mask(path):
    text = open(path, encoding="utf-8", errors="replace").read()
    m = re.search(r"CFG_MASK\s*=\s*3840'h([0-9A-Fa-f]+)", text)
    if not m:
        sys.exit("CFG_MASK not found in " + path)
    hexs = m.group(1)
    if len(hexs) != 960:
        sys.exit("CFG_MASK literal is %d hex digits, expected 960" % len(hexs))
    # Verilog hex literal: leftmost digit is most significant.  Byte 0 is the
    # least significant byte, i.e. the rightmost two hex digits.
    return [int(hexs[len(hexs) - 2 * (k + 1):len(hexs) - 2 * k], 16)
            for k in range(CFG_BYTES)]


def parse_scalars(path):
    text = open(path, encoding="utf-8", errors="replace").read()
    out = {}
    for name in ("CFG_BYTES", "CFG_LATCH_BITS"):
        m = re.search(r"localparam\s+integer\s+%s\s*=\s*(\d+)" % name, text)
        out[name] = int(m.group(1)) if m else None
    return out


def popcount(bs):
    return sum(bin(b).count("1") for b in bs)


def lean_list(xs, width=100):
    return "[" + ", ".join("0x%02X" % x for x in xs) + "]"


def lean_list_lines(xs, per_line=16, indent="  "):
    items = ["0x%02X" % x for x in xs]
    rows = [", ".join(items[i:i + per_line]) for i in range(0, len(items), per_line)]
    return "[\n" + ",\n".join(indent + r for r in rows) + "]"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=DEFAULT_ROOT)
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()
    vh = os.path.join(args.repo, "src", "md2_map.vh")
    mask = parse_mask(vh)
    scalars = parse_scalars(vh)
    nz = [(k, b) for k, b in enumerate(mask) if b]
    partial = [(k, b) for k, b in nz if b != 0xFF]
    full = [k for k, b in nz if b == 0xFF]
    report = []
    report.append("source: %s" % vh)
    report.append("CFG_MASK bytes: %d (vh CFG_BYTES=%s)" % (len(mask), scalars["CFG_BYTES"]))
    report.append("nonzero mask bytes: %d" % len(nz))
    report.append("fully-latched bytes (0xFF): %d" % len(full))
    report.append("partially-latched bytes: %d" % len(partial))
    report.append("latched bits (popcount): %d (vh CFG_LATCH_BITS=%s)"
                  % (popcount(mask), scalars["CFG_LATCH_BITS"]))
    report.append("partial byte list: " +
                  ", ".join("%d:0x%02X" % (k, b) for k, b in partial))
    for name, (base, stride, inst) in STRIDES.items():
        pats = []
        for i in range(inst):
            b = base - CFG_LO + stride * i
            pats.append(mask[b:b + stride])
        ok = len({tuple(p) for p in pats}) == 1
        report.append("%s block: %d instances, uniform pattern=%s, bytes=%s"
                      % (name, inst, ok, " ".join("0x%02X" % x for x in pats[0])))
        report.append("  Lean pattern: " + lean_list(pats[0]))
    print("\n".join(report))
    body = "/-- `CFG_MASK` bytes, offset `k` of the configuration window\n(`CFG_MASK[8k +: 8]`). -/\ndef cfgMaskList : List Nat :=\n  " + \
        lean_list(mask) + "\n"
    if args.write:
        out = os.path.join(HERE, "cfg_mask.lean.txt")
        with open(out, "w", encoding="utf-8") as f:
            f.write(body)
        with open(os.path.join(HERE, "gen_bank_mask.report.txt"), "w",
                  encoding="utf-8") as f:
            f.write("\n".join(report) + "\n")
        print("wrote " + out)


if __name__ == "__main__":
    main()
