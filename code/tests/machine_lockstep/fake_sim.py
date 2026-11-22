"""Fake `machine-sim`: a second metronome2 Chip speaking the stdin/stdout protocol, to self-test the harness.

    --flip CYCLE:KEY:BIT   xor bit BIT of KEY in the output line of cycle CYCLE (0-based since the last reset)
"""
import json
import sys

from dump_model import dump
from metronome2.chip import Chip


def main(argv):
    flip = None
    if "--flip" in argv:
        c, k, b = argv[argv.index("--flip") + 1].split(":")
        flip = (int(c), k, int(b))
    chip, t = Chip(), 0
    out = sys.stdout
    for line in sys.stdin:
        w = line.split()
        if not w:
            continue
        if w[0] == "quit":
            break
        if w[0] == "reset":
            chip, t = Chip(), 0
            continue
        ui, uio, rst = map(int, w)
        d = dump(chip, tuple(chip.step(ui, uio, rst)))
        if flip and t == flip[0]:
            d[flip[1]] ^= 1 << flip[2]
        out.write(json.dumps(d, separators=(",", ":")) + "\n")
        out.flush()
        t += 1


if __name__ == "__main__":
    main(sys.argv[1:])
