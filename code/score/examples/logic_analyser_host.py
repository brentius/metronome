"""Host script for the logic-analyser personality (code/score/lib/logic_analyser.score).

Compiles the analyser for an input pin and a sample rate, runs it on the v2 cycle-level model against a waveform you
supply (one level per sample beat), reads the receive stream back from data RAM, and writes a VCD.

    python code/score/examples/logic_analyser_host.py --rate 1e6 --demo out.vcd

The capture starts at the first rising edge on the pin (the trigger) and holds 128 samples after the trigger beat,
which is itself the known 1 that starts the clock.  Evidence kind: cycle model only; no RTL run, no hardware.
"""
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
for p in ("code/scorec", "code/score", "code/host2", "sim/reference", "code/tests/scorec"):
    if str(ROOT / p) not in sys.path:
        sys.path.insert(0, str(ROOT / p))

LIB = ROOT / "code/score/lib/logic_analyser.score"
STREAM_BASE = 0x400          # the receive stream of the compiled image (data RAM offset)
SAMPLES = 128


def compile_analyser(rate_hz=1e6, pin="P5"):
    import scorec
    return scorec.compile_score(LIB.read_text(encoding="utf-8"), "analyser", f"pin={pin}", rate_hz=rate_hz)


def capture(compiled, beats, rate_hz=1e6, pin_index=5):
    """Drive `beats` (a list of 0/1, one per sample beat; beats[0] must be the 1 that triggers) on input P<pin_index>.
    Returns (the bits the chip stored, first sample first; the chip)."""
    from harness import IDLE, new_chip
    chip = new_chip(compiled)
    cyc = 60e6 / rate_hz
    for _ in range(60):
        chip.step(IDLE, 0)
    t = 0.0
    for b in beats:
        end = t + cyc
        while t < end:
            chip.step(IDLE, b << pin_index)
            t += 1
    for _ in range(int(4 * cyc) + 200):
        chip.step(IDLE, 0)
    s = chip.mem.streams[0]
    raw = bytes(chip.mem.data[STREAM_BASE:STREAM_BASE + s.POS])
    return [(raw[i // 8] >> (i % 8)) & 1 for i in range(len(raw) * 8)], chip


def write_vcd(samples, rate_hz, path, name="pin", trigger=True):
    """VCD with a 1 ns timescale; the trigger beat (a known 1) is time 0 and sample k is at (k + 1) beats."""
    period_ns = 1e9 / rate_hz
    series = ([1] if trigger else []) + list(samples)
    out = ["$timescale 1 ns $end", f"$var wire 1 ! {name} $end", "$enddefinitions $end", f"#0\n{series[0]}!"]
    for k in range(1, len(series)):
        if series[k] != series[k - 1]:
            out.append(f"#{round(k * period_ns)}\n{series[k]}!")
    Path(path).write_text("\n".join(out) + "\n", encoding="ascii")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--rate", type=float, default=1e6)
    ap.add_argument("--demo", metavar="VCD", help="capture a built-in 0xA5-pattern stimulus and write this VCD")
    a = ap.parse_args()
    comp = compile_analyser(a.rate)
    stim = [1] + [(0xA5 >> (i % 8)) & 1 for i in range(SAMPLES)]
    got, _ = capture(comp, stim, a.rate)
    print(comp.report)
    print("captured", len(got), "samples; matches stimulus:", got == stim[1:1 + len(got)])
    if a.demo:
        write_vcd(got, a.rate, a.demo)
        print("wrote", a.demo)
