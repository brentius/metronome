"""Host script for the pattern-generator personality (code/score/lib/pattern_gen.score).

Compiles the score for a pin and a bit rate, packs a bit list into the 64-byte pattern the score streams, and plays it
on the v2 cycle-level model.  The same `pack` / image output is what a real host would send over the host link.

    python code/score/examples/pattern_gen_host.py --rate 1e6 --bits 1011001110001111 --vcd out.vcd

The pattern is 512 beats (64 bytes, LSB of each byte first); a shorter bit list is padded with zeros (the line idles
low).  Evidence kind: cycle model only; no RTL run, no hardware.
"""
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
for p in ("code/scorec", "code/score", "code/host2", "sim/reference", "code/tests/scorec"):
    if str(ROOT / p) not in sys.path:
        sys.path.insert(0, str(ROOT / p))

LIB = ROOT / "code/score/lib/pattern_gen.score"
PATTERN_BITS = 512


def pack(bits):
    """Bit list (first bit first) -> 64 bytes, LSB of each byte sent first."""
    bits = list(bits)
    if len(bits) > PATTERN_BITS:
        raise ValueError(f"pattern longer than {PATTERN_BITS} bits")
    bits += [0] * (PATTERN_BITS - len(bits))
    return bytes(sum(b << i for i, b in enumerate(bits[k:k + 8])) for k in range(0, PATTERN_BITS, 8))


def compile_pattern_gen(rate_hz=1e6, pin="O8"):
    import scorec
    return scorec.compile_score(LIB.read_text(encoding="utf-8"), "generator", f"pin={pin}", rate_hz=rate_hz)


def play(compiled, bits, rate_hz, pin=8, extra_beats=8):
    """Run the compiled image on the cycle model; return (chip, pin level at every chip cycle)."""
    from harness import HM, IDLE, hostin, new_chip, stream_reg, stream_rewind
    chip = new_chip(compiled)
    chip.backdoor_write(HM["DATA_BASE"], pack(bits))
    stream_reg(chip, 0, "LEN", 64, 2)
    stream_rewind(chip, 0)
    for _ in range(40):
        chip.step(IDLE, 0)
    hostin(chip, 1)                                   # the go byte
    trace = []
    for _ in range(int((PATTERN_BITS + extra_beats) * 60e6 / rate_hz) + 200):
        uo, uio, oe = chip.step(IDLE, 0)
        trace.append((uio >> pin) & 1 if pin < 8 else (uo >> (pin - 8 + 2)) & 1)
    return chip, trace


def write_vcd(trace, path, name="pin"):
    """One VCD value change per level change; timescale 1 ns, times rounded from 16.667 ns chip cycles."""
    lines = ["$timescale 1 ns $end", f"$var wire 1 ! {name} $end", "$enddefinitions $end", f"#0\n{trace[0]}!"]
    for i in range(1, len(trace)):
        if trace[i] != trace[i - 1]:
            lines.append(f"#{round(i * 1e9 / 60e6)}\n{trace[i]}!")
    Path(path).write_text("\n".join(lines) + "\n", encoding="ascii")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--rate", type=float, default=1e6)
    ap.add_argument("--bits", default="1011001110001111")
    ap.add_argument("--vcd")
    a = ap.parse_args()
    comp = compile_pattern_gen(a.rate)
    chip, tr = play(comp, [int(c) for c in a.bits], a.rate)
    print(comp.report)
    if a.vcd:
        write_vcd(tr, a.vcd)
        print("wrote", a.vcd)
