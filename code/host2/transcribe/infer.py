"""Infer a wire protocol from a captured single-wire trace and emit a .score.

Trace model: a sequence of 0/1 levels, one per sample, at a known sample rate (default 60 MHz).
Everything here is host-side Python; evidence is model-level (reference codec), not hardware.
"""
from __future__ import annotations

from bisect import bisect_right
from dataclasses import dataclass, field

STD_BAUDS = [300, 600, 1200, 2400, 4800, 9600, 14400, 19200, 28800, 38400, 57600, 115200, 230400, 460800,
             921600, 1_000_000, 1_500_000, 2_000_000, 3_000_000, 4_000_000, 5_000_000, 6_000_000, 10_000_000]
MIN_SAMPLES_PER_BIT = 4.0


class InferenceError(Exception):
    """The trace does not look like a protocol this tool can transcribe."""


class Trace:
    """Run-length view of a level sequence."""

    def __init__(self, levels):
        lv = [1 if x else 0 for x in levels]
        if len(lv) < 8:
            raise InferenceError("trace too short")
        self.n = len(lv)
        self.first = lv[0]
        self.edges = [i for i in range(1, len(lv)) if lv[i] != lv[i - 1]]   # first sample after each change
        if len(self.edges) < 4:
            raise InferenceError(f"no usable activity: only {len(self.edges)} edge(s) in {self.n} samples")
        b = [0] + self.edges + [self.n]
        self.runs = [b[i + 1] - b[i] for i in range(len(b) - 1)]           # includes truncated first/last
        self.run_levels = [self.first ^ (i & 1) for i in range(len(self.runs))]

    def level_at(self, t: float) -> int:
        i = min(int(t), self.n - 1)
        return self.first ^ (bisect_right(self.edges, i) & 1)

    @property
    def idle(self) -> tuple[int, str]:
        if self.first == self.run_levels[-1]:
            return self.first, "trace starts and ends at this level"
        k = max(range(len(self.runs)), key=lambda i: self.runs[i])
        return self.run_levels[k], "longest run (trace start and end levels differ)"


def _median(xs):
    s = sorted(xs)
    return s[len(s) // 2]


def _refine(runs, T0, kmax=None, tol=0.35, iters=6):
    """Least-squares T through the origin over all runs: r ~ k T with k = round(r/T). Returns (T, rms in T, n used)."""
    T, used = T0, []
    for _ in range(iters):
        used = []
        for r in runs:
            k = round(r / T)
            if k >= 1 and (kmax is None or k <= kmax) and abs(r / T - k) < tol:
                used.append((k, r))
        if not used:
            return T0, 9.9, 0
        T = sum(k * r for k, r in used) / sum(k * k for k, r in used)
    rms = (sum((r / T - k) ** 2 for k, r in used) / len(used)) ** 0.5
    return T, rms, len(used)


# ---- Manchester vs NRZ -------------------------------------------------------------------------------------
@dataclass
class Classification:
    kind: str                    # "manchester" | "nrz" | "unknown"
    bit_rate: float | None       # bit/s for manchester (= fs / (2 H)); None otherwise
    half_bit_samples: float | None
    evidence: str


def classify(levels, fs: float = 60e6) -> Classification:
    """Manchester has runs of exactly 1 or 2 half-bits (plus rare gaps); NRZ has a tail of longer runs.
    A short pattern such as 0xAA bytes on a UART is also all 1- and 2-bit runs and would be misread as Manchester."""
    tr = levels if isinstance(levels, Trace) else Trace(levels)
    runs = tr.runs[1:-1]
    if len(runs) < 16:
        return Classification("unknown", None, None, f"only {len(runs)} complete runs")
    small = min(runs)
    H0 = _median([r for r in runs if r <= 1.4 * small])
    if H0 < 2:
        return Classification("unknown", None, None, "shortest runs are glitches (<2 samples)")
    H, _, _ = _refine(runs, H0, kmax=2)
    n1 = sum(1 for r in runs if abs(r / H - 1) < 0.35)
    n2 = sum(1 for r in runs if abs(r / H - 2) < 0.35)
    nlong = sum(1 for r in runs if r > 2.65 * H)
    frac_fit = (n1 + n2) / len(runs)
    if frac_fit >= 0.9 and nlong <= 0.08 * len(runs) and n1 >= 0.1 * len(runs) and n2 >= 0.1 * len(runs):
        return Classification("manchester", fs / (2 * H), H,
                              f"{100 * frac_fit:.0f}% of {len(runs)} runs are 1 or 2 half-bits (H={H:.2f} samples), "
                              f"{nlong} long runs (gaps)")
    return Classification("nrz", None, None, f"{100 * nlong / len(runs):.0f}% of runs are longer than 2.65 H0 "
                          f"(H0={H0}); not the Manchester run pattern")


# ---- UART inference ----------------------------------------------------------------------------------------
@dataclass
class UartInference:
    fs: float
    idle_level: int
    idle_reason: str
    T: float                     # samples per bit
    baud_measured: float
    baud_used: int
    baud_standard: bool
    baud_error_pct: float        # measured vs the standard baud nearest to it
    data_bits: int
    parity: str                  # none | even | odd
    stop_bits: int
    stop_bits_note: str
    n_frames: int
    words: list
    bit_order: str = "lsb first (assumed; not inferable from the wire)"
    notes: list = field(default_factory=list)
    alternatives: list = field(default_factory=list)


def _decode_frames(tr: Trace, idle: int, T: float, n: int, par: str):
    """Decode every frame under hypothesis (n data bits, parity, >=1 stop). Returns (words, n_bad, start samples)."""
    L = 1 + n + (par != "none") + 1
    t = 0
    while t < tr.n and tr.level_at(t) != idle:      # skip a capture that begins mid-frame
        t += 1
    words, starts, bad = [], [], 0
    ei = bisect_right(tr.edges, t)
    while ei < len(tr.edges):
        s = tr.edges[ei]
        if tr.level_at(s) == idle:                  # edge back to idle
            ei += 1
            continue
        if s + (L - 0.5) * T >= tr.n:
            break                                   # capture ends mid-frame
        mark = [1 if tr.level_at(s + (k + 0.5) * T) == idle else 0 for k in range(L)]   # logical 1 = idle level
        data = mark[1:1 + n]
        ok = mark[0] == 0 and mark[-1] == 1
        if par != "none":
            ok = ok and ((sum(data) + mark[1 + n]) % 2 == (0 if par == "even" else 1))
        bad += not ok
        words.append(sum(b << i for i, b in enumerate(data)))
        starts.append(s)
        ei = bisect_right(tr.edges, s + (L - 0.5) * T)
    return words, bad, starts


def infer_uart(levels, fs: float = 60e6) -> UartInference:
    tr = levels if isinstance(levels, Trace) else Trace(levels)
    idle, why = tr.idle
    runs = tr.runs[1:-1]
    if len(runs) < 6:
        raise InferenceError(f"only {len(runs)} complete runs: not enough activity to infer a bit time")
    small = min(runs)
    T0 = _median([r for r in runs if r <= 1.4 * small])
    cands = []
    for m in (1, 2, 3):                              # the shortest run may be 2 or 3 bits if single-bit runs are absent
        Tc = T0 / m
        if Tc < MIN_SAMPLES_PER_BIT:
            continue
        T, rms, used = _refine(runs, Tc)
        if used >= 0.9 * len(runs) and rms < 0.12:
            cands.append((T, rms))
    if not cands:
        raise InferenceError("run lengths are not integer multiples of one bit time (no consistent bit clock): "
                             "not an asynchronous NRZ wire, or too noisy")
    failures, found = [], None
    for T, rms in cands:
        valid = []
        for n in range(5, 10):
            for par in ("none", "even", "odd"):
                L = n + 3 if par != "none" else n + 2
                words, bad, starts = _decode_frames(tr, idle, T, n, par)
                if words and bad <= 0.05 * len(words):
                    valid.append((L, n, par, words, starts))
        if not valid:
            failures.append(f"T={T:.2f}: no framing of 5..9 data bits x parity x >=1 stop bit gives valid frames")
            continue
        Lmin = min(h[0] for h in valid)
        top = [h for h in valid if h[0] == Lmin]
        withpar = [h for h in top if h[2] != "none"]
        nopar = [h for h in top if h[2] == "none"]
        # same frame length: parity wins over an extra data bit only with real evidence (>= 6 frames all passing)
        pick = withpar[0] if (withpar and len(top[0][3]) >= 6) or not nopar else nopar[0]
        found = (T, pick, [(h[1], h[2]) for h in top if h is not pick])
        break
    if not found:
        raise InferenceError("bit clock found but no UART framing fits (" + "; ".join(failures) + ")")
    T, (L, n, par, words, starts), alts = found
    notes = ["data bit order is assumed LSB first (UART convention); it cannot be inferred from the wire"]
    stop, snote = 1, "1 (lower bound: no shorter inter-frame spacing could be observed)"
    if len(starts) >= 2:
        sp = min((b - a) / T for a, b in zip(starts, starts[1:]))
        if abs(sp - round(sp)) < 0.3 and round(sp) >= L:
            stop = 1 + round(sp) - L
            snote = (f"{stop} (shortest start-to-start spacing {sp:.2f} bits; if the sender always idles between "
                     f"frames this is a lower bound)")
        elif abs(sp - round(sp)) >= 0.3:
            notes.append(f"start-to-start spacing {sp:.2f} bits is not a whole number of bits (variable idle gaps)")
    if len(words) < 4:
        notes.append(f"only {len(words)} frames: the frame format is weakly constrained")
    if alts:
        notes.append(f"equally short alternatives, indistinguishable on the wire: {alts}")
    baud = fs / T
    std = min(STD_BAUDS, key=lambda b: abs(b / baud - 1))
    err = (baud / std - 1) * 100
    used, is_std = (std, True) if abs(err) <= 1.0 else (int(round(baud)), False)
    return UartInference(fs, idle, why, T, baud, used, is_std, err, n, par, stop, snote, len(words), words,
                         notes=notes, alternatives=alts)


# ---- score emission ----------------------------------------------------------------------------------------
def emit_uart_score(inf: UartInference, name: str = "transcribed_uart", wire: str = "tx") -> str:
    hi = inf.idle_level == 1
    start, stop = ("0", "1") if hi else ("1", "0")
    near = min(STD_BAUDS, key=lambda b: abs(b / inf.baud_measured - 1))
    basis = (f"standard baud {inf.baud_used} (measured {inf.baud_measured:.1f}, {inf.baud_error_pct:+.2f}%)"
             if inf.baud_standard else
             f"measured {inf.baud_measured:.1f} baud used as is ({inf.baud_error_pct:+.2f}% from the nearest "
             f"standard {near}, outside the 1% rounding window)")
    lines = [
        "# Transcribed from a captured wire by code/host2/transcribe: inferred, not a specification.",
        f"# Sample rate {inf.fs / 1e6:g} MHz, {inf.T:.2f} samples/bit, {inf.n_frames} frames seen.",
        f"# Clock: {basis}.",
        f"# Idle {'high' if hi else 'low'} ({inf.idle_reason}); {inf.data_bits} data bits, parity {inf.parity}, "
        f"stop bits {inf.stop_bits_note}.",
        "# Bit order lsb first is an ASSUMPTION (UART convention), not measured.",
        f"protocol {name}",
        "roles    sender, receiver",
        "",
        f"wire {wire} out push-pull idle {'high' if hi else 'low'} by sender",
        "",
        f"clock {inf.baud_used} Hz",
        "  sender:   generated",
        f"  receiver: started by {wire} {'fall' if hi else 'rise'}",
        "  tolerance 3%",
        "",
        "symbols",
        f"  bit(d)   {wire} \"d\"          sample {wire} at 50%",
        "",
        "bits lsb first" + ("" if hi else ", invert"),
        "",
        "grammar",
        "  line   = char*",
        f"  char   = bit({start})                     # start bit",
        f"           data:u{inf.data_bits}",
    ]
    if inf.parity != "none":
        lines.append(f"           par: parity {inf.parity} over data")
    lines.append(f"           bit({stop})                     # stop bit")
    lines += [f"           bit({stop})                     # extra stop bit"] * (inf.stop_bits - 1)
    lines.append("           gap 0 beats")
    return "\n".join(lines) + "\n"


@dataclass
class Transcription:
    classification: Classification
    uart: UartInference | None
    score: str | None


def transcribe(levels, fs: float = 60e6, name: str = "transcribed_uart") -> Transcription:
    """Classify the trace; for an NRZ/UART wire infer the format and return a checked score."""
    from score import check, parse
    tr = Trace(levels)
    cl = classify(tr, fs)
    if cl.kind == "manchester":
        return Transcription(cl, None, None)          # score emission for Manchester is not implemented
    inf = infer_uart(tr, fs)
    text = emit_uart_score(inf, name)
    errs = [d for d in check(parse(text)) if str(d.code).startswith("E-")]
    if errs:
        raise InferenceError("emitted score failed checks: " + "; ".join(map(str, errs)))
    return Transcription(cl, inf, text)
