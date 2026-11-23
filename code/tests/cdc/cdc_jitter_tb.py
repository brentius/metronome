"""Metastability-injection bench: replay a protocol scenario with per-edge, per-pin zero/one-cycle input timing jitter.

Each first-stage synchroniser capture is modelled at the stimulus, as the brief asks: an input edge that arrives at
a clock boundary may be seen by the chip in cycle n or (with probability CDC_JITTER) one cycle later.  Edges are
resolved independently per raw pin (uio_in[7:0], ui_in[7:0]); rst_n is included when the scenario allows it.  The
injection is a pure delay of the *pin*, so it is the physically possible late-resolution outcome, never an early one.

One clean pass (no jitter) and one pass per seed run inside one simulation, each starting from reset.  Results are
decoded from the pins only (SPI MISO and the O8 UART transmitter) and compared pass to pass: protocol decodes must be
identical, while the cycle-exact output trace is expected to diverge (reported, not asserted).

Environment (set by cdc_sim.py / gl_cdc.sh):
    CDC_SCENARIO   scenario name (scenarios_cdc.BUILDERS)
    CDC_SEEDS      comma-separated jitter seeds, default "1,2"
    CDC_JITTER     probability that a given input edge is resolved one cycle late, default 0.5
    CDC_JITTER_DEPTH  cycles added when an edge resolves late, default 1.  Only the negative control raises it;
                   the campaign claim is about depth 1.
    CDC_OUT        write a JSON summary (pass results, comparisons, edge counts) here
    CDC_GL         1 when running a gate-level netlist (only changes diagnostics; the bench is pins-only anyway)
    CDC_EXPECT_DIVERGENCE
                   1 for the negative control: the clean pass must still decode correctly, and at least one jittered
                   pass must decode *differently*.  Proves the comparison is able to report a difference.
"""
from __future__ import annotations

import hashlib
import json
import os
import random
import sys
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, RisingEdge

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for _p in (HERE, ROOT / "code/tests/lockstep_v2", ROOT / "sim/reference", ROOT / "code/host2"):
    if str(_p) not in sys.path:
        sys.path.insert(0, str(_p))

import scenarios_cdc as sc                               # noqa: E402


def _val(sig, default=None):
    v = sig.value
    return int(v) if v.is_resolvable else default


class Pins:
    """Pin-level view of the DUT, also when a `tb` wrapper is the top level."""

    def __init__(self, dut):
        self.root = dut
        self.dut = getattr(dut, "user_project", dut)

    def __getattr__(self, name):
        return getattr(self.dut, name)


class Jitter:
    """Per-bit, per-edge late resolution of the raw input pins (default one cycle)."""

    def __init__(self, seed: int, prob: float, mask: int, rst: bool, depth: int = 1):
        self.rng = random.Random(seed)
        self.prob = prob
        self.mask = mask
        self.rst = rst
        self.depth = depth
        self.last: dict[int, int] = {}
        self.out: dict[int, int] = {}
        self.sched: dict[int, tuple[int, int]] = {}
        self.edges = [0] * 17
        self.delayed = [0] * 17

    def _bit(self, t: int, k: int, value: int) -> int:
        if k not in self.last:
            self.last[k] = self.out[k] = value
            return value
        if k in self.sched and self.sched[k][0] <= t:
            self.out[k] = self.sched.pop(k)[1]
        if value != self.last[k]:
            self.last[k] = value
            self.edges[k] += 1
            delay = self.depth if self.rng.random() < self.prob else 0
            self.delayed[k] += delay
            if delay:
                self.sched[k] = (t + delay, value)
            else:
                self.out[k] = value
        return self.out[k]

    def step(self, t: int, ui: int, uio: int, rst_n: int) -> tuple[int, int, int]:
        raw = (ui << 8) | uio
        driven = raw
        for k in range(16):
            if not (self.mask >> k) & 1:
                continue
            bit = self._bit(t, k, (raw >> k) & 1)
            if ((driven >> k) & 1) != bit:
                driven = (driven & ~(1 << k)) | (bit << k)
        if self.rst:
            rst_n = self._bit(t, 16, rst_n)
        return driven >> 8, driven & 0xFF, rst_n


def _eval(x, t, outs):
    return x(t, outs) if callable(x) else x


def program_frames(scn) -> set[int]:
    """Frame indices of host writes into the program window (PROG_BASE..DATA_BASE).

    Program memory is SRAM and keeps its contents across reset (SPEC v2: config is cleared, memories are not), so a
    later pass can start with the image already loaded and skip ~130k SPI frames of re-loading.  Address decoding
    uses the ideal ui_in bits (SCK/CS/MOSI are never driven by a callback in these scenarios).
    """
    frames: set[int] = set()
    active = None
    bits: list[int] = []
    prev_sck = False
    for t, (f, _hi, _uio, _rst) in enumerate(scn.steps):
        ui = _eval(f, t, (0, 0, 0))
        cs = bool(ui & 2)
        sck = bool(ui & 1)
        if not cs:
            if active is None:
                active = t
            if sck and not prev_sck:
                bits.append(1 if ui & 4 else 0)
        elif active is not None:
            if len(bits) >= 24:
                cmd = int("".join(map(str, bits[:8])), 2)
                addr = int("".join(map(str, bits[8:24])), 2)
                if cmd == 0x02 and addr < sc.HM["DATA_BASE"]:
                    frames.update(range(active, t + 1))
            active, bits = None, []
        prev_sck = sck and not cs
    return frames


async def run_pass(pins, spec, seed, prob, steps, depth=1):
    await FallingEdge(pins.clk)          # a previous pass may have ended mid-cycle
    pins.rst_n.value = 0
    pins.ui_in.value = sc.IDLE
    pins.uio_in.value = 0
    pins.ena.value = 1
    for _ in range(4):
        await RisingEdge(pins.clk)
    jit = None if seed is None else Jitter(seed, prob, spec.mask, spec.rst_jitter, depth)
    outs = (0, 0, 0)
    frames: list[int] = []
    miso: list[int | None] = []
    tx: list[int | None] = []
    trace: list[tuple[int, int, int]] = []
    driven = (sc.IDLE, 0, 0)
    for k in range(len(steps) + 1):
        await FallingEdge(pins.clk)
        if k:                                    # outputs of the cycle whose frame was driven last iteration
            value = pins.uo_out.value
            uo = int(value) if value.is_resolvable else None
            outs = (uo or 0, _val(pins.uio_out) or 0, _val(pins.uio_oe) or 0)
            trace.append(outs)
            miso.append(uo & 1 if uo is not None else int(value[0]) if value[0].is_resolvable else None)
            tx.append((uo >> sc.O8) & 1 if uo is not None else
                      int(value[sc.O8]) if value[sc.O8].is_resolvable else None)
        if k == len(steps):
            break
        t, (f, hi, uio_spec, rst_n) = steps[k]
        ui_spec = _eval(f, t, outs)
        hi_spec = _eval(hi, t, outs)
        uio_now = _eval(uio_spec, t, outs)
        ui = (ui_spec & 0x07) | (hi_spec & 0xF8)
        uio = uio_now & 0xFF
        rst = rst_n
        frames.append(ui)                    # ideal host timing, not the jittered pin sequence
        if jit is not None:
            ui, uio, rst = jit.step(k, ui, uio, rst)
        if ui != driven[0]:
            pins.ui_in.value = ui
        if uio != driven[1]:
            pins.uio_in.value = uio
        if rst != driven[2]:
            pins.rst_n.value = rst
        driven = (ui, uio, rst)
    window = [level for (t, _), level in zip(steps, tx) if spec.uart_start is not None and t >= spec.uart_start]
    error = None
    txns, reads = [], []
    try:
        txns, reads = sc.decode_spi(frames, miso)
        result = spec.validate(reads, window)
    except AssertionError as exc:
        error = str(exc)
        result = {}
    diagnostics = {"learned_bit_time_q5": result.pop("tu")} if "tu" in result else {}
    return {
        "seed": seed,
        "cycles": len(steps),
        "edges": 0 if jit is None else sum(jit.edges),
        "edges_delayed": 0 if jit is None else sum(jit.delayed),
        "edges_by_pin": {} if jit is None else {
            name: {"edges": edges, "delayed": delayed}
            for name, edges, delayed in zip(
                [f"uio_in[{i}]" for i in range(8)] + [f"ui_in[{i}]" for i in range(8)] + ["rst_n"],
                jit.edges, jit.delayed)
        },
        "result": result,
        "error": error,
        "spi_readback": [(address, data.hex()) for address, data in reads],
        "diagnostics": diagnostics,
        "txns": len(txns),
        "trace_sha": hashlib.sha1(bytes(v for t in trace for v in t)).hexdigest()[:16],
        "_trace": trace,
    }


@cocotb.test()
async def cdc_jitter(dut):
    name = os.environ.get("CDC_SCENARIO", "spi_host")
    seeds = [int(s) for s in os.environ.get("CDC_SEEDS", "1,2,3").split(",") if s.strip()]
    prob = float(os.environ.get("CDC_JITTER", "0.5"))
    depth = int(os.environ.get("CDC_JITTER_DEPTH", "1"))
    expect_divergence = os.environ.get("CDC_EXPECT_DIVERGENCE") == "1"
    assert seeds and len(set(seeds)) == len(seeds), "CDC_SEEDS must contain distinct integers"
    assert 0 < prob <= 1, "CDC_JITTER must be in (0, 1]"
    assert depth >= 1, "CDC_JITTER_DEPTH must be >= 1"
    spec = sc.build(name)
    if os.environ.get("CDC_MASK"):                      # diagnostic override, recorded in the summary
        spec.mask = int(os.environ["CDC_MASK"], 0)
    pins = Pins(dut)
    cocotb.start_soon(Clock(pins.clk, 16666, unit="ps").start())
    full = [(t, step) for t, step in enumerate(spec.scn.steps)]
    skip = program_frames(spec.scn) if spec.retain_program else set()
    reduced = [(t, step) for t, step in full if t not in skip]
    if skip:
        dut._log.info(f"{name}: {len(spec.scn.steps)} frames; later passes skip {len(skip)} program-load frames")
    passes = []
    for idx, seed in enumerate([None] + seeds):
        steps = full if idx == 0 else reduced
        label = "clean" if seed is None else f"jitter-{seed}"
        r = await run_pass(pins, spec, seed, prob, steps, depth)
        r["label"] = label
        passes.append(r)
        dut._log.info(f"{name} {r['label']}: {r['cycles']} cycles, {r['edges']} jittered edges "
                      f"({r['edges_delayed']} delayed), txns={r['txns']}")
    clean = passes[0]
    # When the image is already resident, compare only from the UART observation
    # window onward. Outputs during the omitted host transactions are incomparable.
    comparable_cycles = [(i, t) for i, (t, _) in enumerate(reduced)
                         if not skip or (spec.uart_start is not None and t >= spec.uart_start)]
    differences = []
    for p in passes[1:]:
        first_diff = next((t for i, t in comparable_cycles
                           if clean["_trace"][t] != p["_trace"][i]), None)
        p["first_pin_trace_divergence_vs_clean"] = first_diff
        if first_diff is not None:
            differences.append(first_diff)
    first_diff = min(differences, default=None)
    summary = {
        "scenario": name,
        "notes": spec.notes,
        "clock_ns": 16.666,
        "jitter_probability": prob,
        "jitter_depth_cycles": depth,
        "mask": hex(spec.mask),
        "program_frames_skipped_after_first_pass": len(skip),
        "passes": [{k: v for k, v in p.items() if not k.startswith("_")} for p in passes],
        "protocol_results_equal": all(p["error"] is None and p["result"] == clean["result"] for p in passes),
        "first_pin_trace_divergence_vs_clean": first_diff,
        "expect_divergence": expect_divergence,
        "gl": os.environ.get("CDC_GL") == "1",
    }
    out = os.environ.get("CDC_OUT")
    if out:
        Path(out).write_text(json.dumps(summary, indent=2, default=str), encoding="utf-8")
    assert clean["error"] is None, f"{name}: the unperturbed control failed: {clean['error']}"
    assert all(p["edges_delayed"] for p in passes[1:]), "jitter inactive"
    if expect_divergence:
        assert not summary["protocol_results_equal"], (
            f"{name}: negative control did not diverge - the comparison cannot detect a difference")
        detail = [p["error"] or p["result"] for p in passes[1:] if p["error"] is not None
                  or p["result"] != clean["result"]]
        dut._log.info(f"{name}: negative control diverged as required ({detail[:1]}); the clean pass decoded")
    else:
        assert summary["protocol_results_equal"], \
            [(p["label"], p["error"] or p["result"]) for p in passes]
        dut._log.info(f"{name}: protocol decode unchanged over {len(passes) - 1} jitter seed(s); "
                      f"cycle-exact pin trace first diverges at {first_diff}")
