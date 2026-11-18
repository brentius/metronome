"""Characterisation sweep ("shmoo") of a compiled UART receiver: sample point x sender rate error.

Each grid point compiles the receiver from a score transform (the symbol's `sample tx at X%` moved), drives it on the v2
cycle-level model with the reference codec's waveform at rate * (1 + error), and records pass/fail (bytes exact and
every status 0).  Then each column's pass edges are bisected to 0.05% and compared with the closed-form window
(calculated): with the line started by the start-bit edge, the stop bit (index 9) is sampled at (9 + s) receiver bits.
A sender with rate error e (positive = fast) has bits of 1/(1+e) receiver bits, so its stop bit spans
[9/(1+e), 10/(1+e)), giving  9/(9+s) - 1 <= e < 10/(9+s) - 1.  This ideal window ignores the start-edge latency and the
re-arm time before the next start edge, so the measured window is expected to be somewhat narrower.

Evidence class: verified in simulation (v2 model + reference codec); the window is calculated.  Not hardware.

    python code/host2/sweep/uart_shmoo.py            # writes data/processed/v3_rival/uart_shmoo.{json,png}
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
for p in (ROOT / "code" / "scorec", ROOT / "code" / "score", ROOT / "code" / "host2", ROOT / "sim" / "reference",
          ROOT / "code" / "tests" / "scorec"):
    sys.path.insert(0, str(p))

from harness import IDLE, Codec, new_chip, parse, scorec, spec_block  # noqa: E402

RATE = 1_000_000                        # 60 cycles per bit: fast to simulate, same divider arithmetic
DATA = bytes([0x00, 0x55, 0xFF, 0x80, 0x01, 0xF0])
SAMPLES = [20, 30, 40, 50, 60, 70, 80]  # % of the bit
ERRORS = [e / 1000 for e in range(-80, 81, 5)]


def score_text(sample_pct):
    t = spec_block(0).replace("clock 115200 Hz", f"clock {RATE} Hz")
    return t.replace("sample tx at 50%", f"sample tx at {sample_pct}%")


_rx_cache: dict = {}


def receiver(sample_pct):
    if sample_pct not in _rx_cache:
        _rx_cache[sample_pct] = scorec.compile_score(score_text(sample_pct), "receiver", "tx=P5")
    return _rx_cache[sample_pct]


def passes(sample_pct, err) -> bool:
    enc = Codec(parse(spec_block(0)), rate=RATE * (1 + err)).encode_all([("data", b) for b in DATA])
    chip = new_chip(receiver(sample_pct))
    for _ in range(40):
        chip.step(IDLE, 1 << 5)
    st = []
    for lvl in list(enc.bus["tx"]) + [1] * 300:
        chip.step(IDLE, (lvl & 1) << 5)
        if chip.host.OUTV:
            st.append(chip.host.OUTB)
            chip.host.OUTV = 0
    got = bytes(chip.mem.data[0x400:0x400 + chip.mem.streams[0].POS])
    return got == DATA and st == [0] * len(DATA)


def edge(sample_pct, inside, outside, tol=0.0005):
    """Bisect between a passing and a failing error."""
    while abs(outside - inside) > tol:
        mid = (inside + outside) / 2
        if passes(sample_pct, mid):
            inside = mid
        else:
            outside = mid
    return inside


def main():
    grid = {s: [passes(s, e) for e in ERRORS] for s in SAMPLES}
    edges = {}
    for s in SAMPLES:
        row = grid[s]
        ok = [e for e, p in zip(ERRORS, row) if p]
        if not ok or not passes(s, 0.0):
            edges[s] = None
            continue
        lo_in = min(ok)
        lo_out = max([e for e, p in zip(ERRORS, row) if not p and e < lo_in], default=ERRORS[0] - 0.005)
        hi_in = max(ok)
        hi_out = min([e for e, p in zip(ERRORS, row) if not p and e > hi_in], default=ERRORS[-1] + 0.005)
        frac = s / 100
        edges[s] = {"measured": [edge(s, lo_in, lo_out), edge(s, hi_in, hi_out)],
                    "calculated": [9 / (9 + frac) - 1, 10 / (9 + frac) - 1],
                    "contiguous": all(row[i] for i, e in enumerate(ERRORS) if lo_in <= e <= hi_in)}
    out_dir = ROOT / "data" / "processed" / "v3_rival"
    out_dir.mkdir(parents=True, exist_ok=True)
    res = {"what": "UART receiver shmoo: sample point x sender rate error; compiled receiver on the v2 cycle model, "
                   "reference-codec sender waveform", "evidence": "verified in simulation; window is calculated",
           "rate_hz": RATE, "fclk_hz": 60e6, "data": DATA.hex(), "samples_pct": SAMPLES, "errors": ERRORS,
           "grid": {str(s): grid[s] for s in SAMPLES}, "edges": {str(s): edges[s] for s in SAMPLES},
           "generator": "code/host2/sweep/uart_shmoo.py"}
    (out_dir / "uart_shmoo.json").write_text(json.dumps(res, indent=1), encoding="utf-8")
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        fig, ax = plt.subplots(figsize=(7, 4))
        for i, s in enumerate(SAMPLES):
            for e, p in zip(ERRORS, grid[s]):
                ax.add_patch(plt.Rectangle((e * 100 - 0.25, s - 4), 0.5, 8, color="#2e7d32" if p else "#d9d9d9"))
            if edges[s]:
                lo, hi = edges[s]["calculated"]
                ax.plot([lo * 100, hi * 100], [s, s], "k|", ms=14, mew=2)
        ax.set_xlim(ERRORS[0] * 100 - 0.5, ERRORS[-1] * 100 + 0.5)
        ax.set_ylim(SAMPLES[0] - 6, SAMPLES[-1] + 6)
        ax.set_xlabel("sender rate error (%)")
        ax.set_ylabel("receiver sample point (% of bit)")
        ax.set_title("Compiled UART receiver: pass (green) vs. calculated window (black ticks)")
        fig.tight_layout()
        fig.savefig(out_dir / "uart_shmoo.png", dpi=130)
    except ImportError:
        pass
    for s in SAMPLES:
        print(s, edges[s])
    return res


if __name__ == "__main__":
    main()
