"""cocotb side of the xinit bench: power-up state randomisation, X propagation and reset behaviour.

Three questions, answered against the metronome2 model and the v2 lockstep scenarios (imported read-only):

  random_*     With every flop and (optionally) every SRAM word set to a random value before reset is asserted, does
               reset + program load reach exactly the model's known state?  The model starts at 0.
  x_*          With Icarus' default X for all regs and SRAM words, does any X reach uo_out/uio_out/uio_oe after reset
               deasserts (and after a program is loaded)?  Where does X live before it is first loaded?
  xinit_pulse_ Reset asserted mid-run with a sub-cycle pulse: is the asynchronous clear captured, and how many rising
               edges does the rst_m/rst_q synchroniser take to release?

This file owns no RTL: it only drives tt_um_brentius_metronome.  The RTL build is the same source list as lockstep_v2
(rtl_sources.rtl_files), so RTL results are RTL-simulated (Icarus), not gate level.  Gate level (`XINIT_GATE=1`) runs
the same stimuli against a routed netlist; there the bench can only touch chip pins and the SRAM models.

Modes (XINIT_MODE):
  x_check      no deposit: every flop and SRAM word keeps the simulator's X
  x_probe      as x_check; asserts that a documented host-contract read of an unwritten word does produce X
  random_flops deposit every source-declared register path; zero the SRAM words (lockstep convention)
  random_all   deposit every source-declared register path and randomise all 1,024 SRAM words
  random_sram  randomise the SRAM words only (flops start X); the gate-level random-init variant
"""
from __future__ import annotations

import json
import os
import random
import sys
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.handle import Immediate
from cocotb.triggers import FallingEdge, ReadOnly, ReadWrite, RisingEdge, Timer

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path[:0] = [str(ROOT / "sim/reference"), str(ROOT / "code/tests/lockstep_v2")]

import scenarios  # noqa: E402
from metronome2.chip import Chip  # noqa: E402
from lockstep_tb import _val as val, zero_srams  # noqa: E402

IDLE = scenarios.IDLE
PERIOD_NS = 16
HALF_PS = PERIOD_NS * 500
RESET_SETTLE_CYCLES = 3
SRAM_INSTANCES = (("u_pmem0", 256, 8), ("u_pmem1", 256, 8), ("u_dmem", 512, 4))
MODES = ("x_check", "zero", "random_flops", "random_all", "random_sram", "x_probe")


def _sram_handle(dut, inst):
    """The SRAM macro instance, in RTL (`u_pmem0.u_sram`) or in a flattened gate netlist (`u_pmem0.u_sram`)."""
    h = getattr(dut, inst, None)
    if h is not None:
        return getattr(h, "u_sram", h)          # behavioural-array fallback: h.mem
    # A routed netlist is flat; Icarus keeps the escaped hierarchical name, e.g. `u_dmem.u_sram`.
    # `_items()` (not `_sub_handles.items()`) triggers cocotb's lazy child discovery.
    flat = [(name, sub) for name, sub in dut._items() if isinstance(name, str)]
    for name, sub in flat:
        if name == f"{inst}.u_sram" or name.endswith(f".{inst}.u_sram"):
            return sub
    raise AttributeError(f"no SRAM instance for {inst} (flat names: "
                         f"{[name for name, _ in flat if 'sram' in name.lower() or inst in name][:6]})")


def sram_memory(dut, inst):
    """The SRAM model's word array (or md2_pmem/md2_dmem's own array).

    Only the RTL hierarchy exposes it: a flattened netlist's SRAM model is reached by name but Icarus does not
    publish the model's internal array through VPI, so gate mode randomises SRAM contents with a power-up initial
    in a generated copy of the core model instead (see test_xinit.py).
    """
    h = _sram_handle(dut, inst)
    core = getattr(h, "i_SRAM_1P_behavioral_bm_bist", None)
    if core is not None and hasattr(core, "memory"):
        return core.memory
    return h.mem


def _resolve(root, path):
    """Resolve 'g_core[1].u_core.ir' against a cocotb hierarchy object."""
    obj = root
    for part in path.split("."):
        while "[" in part:
            name, rest = part.split("[", 1)
            if name:
                obj = getattr(obj, name)
            idx, part = rest.split("]", 1)
            obj = obj[int(idx)]
        if part:
            obj = getattr(obj, part)
    return obj


class Randomizer:
    """Set every storage net from the Yosys inventory (plus every SRAM word) to a random value.

    A VPI deposit on a combinational net can stick until its driver changes
    and corrupt control such as A_WEN. The paths name source-declared regs.
    """

    def __init__(self, seed, paths, do_sram=True):
        self.seed = seed
        self.paths = paths
        self.do_sram = do_sram
        self.leaves = 0
        self.leaf_bits = 0
        self.words = 0
        self.word_bits = 0
        self.missing = []

    def apply(self, dut):
        seen = set()
        for p in self.paths:
            try:
                obj = _resolve(dut, p)
            except (AttributeError, IndexError, KeyError):
                self.missing.append(p)
                continue
            if obj._path in seen:
                continue
            seen.add(obj._path)
            try:
                # Per-path seed: removing or adding a path does not change any other path's value, which makes the
                # inventory bisection meaningful.
                rng = random.Random(f"{self.seed}:{p}")
                obj.value = Immediate(rng.getrandbits(len(obj)))
                self.leaves += 1
                self.leaf_bits += len(obj)
            except Exception as e:                       # constants etc. are not storage
                self.missing.append(f"{p}: {type(e).__name__}")
        if self.do_sram:
            for inst, words, word_bytes in SRAM_INSTANCES:
                mem = sram_memory(dut, inst)
                assert len(mem) == words
                for i in range(words):
                    assert len(mem[i]) == 8 * word_bytes
                    rng = random.Random(f"{self.seed}:{inst}:{i}")
                    mem[i].value = Immediate(rng.getrandbits(len(mem[i])))
                    self.words += 1
                    self.word_bits += len(mem[i])
        return self


class ReadBeforeWrite:
    """Track known writes at each SRAM sampling edge, down to byte lanes."""

    def __init__(self, dut):
        self.ports = []
        for inst, _words, word_bytes in SRAM_INSTANCES:
            h = _sram_handle(dut, inst)
            self.ports.append((inst, word_bytes, h.A_MEN, h.A_WEN, h.A_REN, h.A_ADDR, h.A_BM))
        self.written = {}
        self.reads = self.writes = 0
        self.unknown_accesses = 0
        self.unwritten_reads = {}

    def sample(self, cycle):
        for inst, word_bytes, men, wen, ren, addr, mask in self.ports:
            if val(men) == 0:
                continue
            control = (val(men), val(wen), val(ren), val(addr))
            if None in control:
                self.unknown_accesses += 1
                continue
            _, write, read, word = control
            key = (inst, word)
            defined = self.written.get(key, 0)
            full_mask = (1 << (word_bytes * 8)) - 1
            if write:
                if val(mask) is None:
                    self.unknown_accesses += 1
                else:
                    defined |= val(mask)
                    self.written[key] = defined
                    self.writes += 1
            if read:
                self.reads += 1
                missing = tuple(lane for lane in range(word_bytes)
                                if (full_mask ^ defined) & (0xff << (8 * lane)))
                if missing:
                    self.unwritten_reads.setdefault((key, missing), {
                        "cycle": cycle, "array": inst, "word": word,
                        "byte_addr": word * word_bytes, "unwritten_lanes": missing,
                    })

    def report(self):
        return {"reads": self.reads, "writes": self.writes,
                "unknown_accesses": self.unknown_accesses,
                "unwritten_reads": list(self.unwritten_reads.values())}


def _deposit_plan(mode, gate):
    """(deposit flop paths, randomise SRAM words through VPI).  Flop deposits and the SRAM array need RTL
    hierarchy; gate mode randomises SRAM contents from a generated power-up initial instead."""
    if mode in ("x_check", "x_probe", "zero"):
        return False, False
    if mode == "random_flops":
        return True, False
    if mode == "random_all":
        return not gate, True
    if mode == "random_sram":
        return False, not gate
    raise AssertionError(f"unknown mode {mode}")


def _randomise(dut, seed, mode, paths, gate=False, preserve_reset=False):
    deposit_flops, do_sram = _deposit_plan(mode, gate)
    use = list(paths) if deposit_flops else []
    if preserve_reset:
        use = [path for path in use if path not in {"rst_m", "rst_q"}]
    rz = Randomizer(seed, use, do_sram).apply(dut)
    assert not rz.missing, f"storage paths did not resolve: {rz.missing[:8]}"
    assert rz.leaves == len(use)
    if do_sram:
        assert (rz.words, rz.word_bits) == (1024, 49152)
    return {"leaves": rz.leaves, "leaf_bits": rz.leaf_bits,
            "words": rz.words, "word_bits": rz.word_bits}


def _paths():
    return json.loads(Path(os.environ["XINIT_PATHS"]).read_text())


async def _start(dut, mode, seed, gate):
    dut.ena.value = 1
    dut.ui_in.value = IDLE
    dut.uio_in.value = 0
    dut.clk.value = 0
    dut.rst_n.value = 1
    await ReadWrite()
    stats = {}
    deposit, sram = _deposit_plan(mode, gate)
    if deposit or sram:
        stats = _randomise(dut, seed, mode, _paths(), gate)
    elif gate and mode == "random_sram":
        stats = {"words": 1024, "word_bits": 49152,
                 "method": "power-up initial in a generated copy of the SRAM core model"}
    if mode in ("zero", "random_flops"):
        zero_srams(dut)
    # Assert before the first rising edge so uncontrolled power-up pins cannot
    # cause a spurious pre-reset edge, which is outside the host sequence.
    dut.rst_n.value = 0
    await Timer(1, unit="ns")
    cocotb.start_soon(Clock(dut.clk, PERIOD_NS, unit="ns").start())
    return stats


def _scenario(name):
    if name.startswith("xinit_"):
        import xinit_scenarios
        return xinit_scenarios.build(name)
    if name.startswith("random_") and os.environ.get("XINIT_FULL_RANDOM") != "1":
        seed = int(name.split("_")[1])
        scenario = scenarios.random_scn(seed, run_cycles=1000)
        # The smoke case covers the full runtime register dump. Keep the
        # generated traffic, including any reads generated during the run.
        dump = scenarios.Scn("runtime_dump")
        dump.readback_all()
        del scenario.steps[-len(dump.steps):]
        return scenario
    return scenarios.build(name)


def _internal_state(dut):
    """Definedness of storage that the reset does not (and need not) clear.

    `ir` is the only design-wide non-reset register that holds data: it is loaded by the same fetch that sets xv, and
    is only consumed while xv=1.  The SRAM read register dr_r is loaded by the read that a consumer issued.
    """
    out = {}
    try:
        for k in range(2):
            core = dut.g_core[k].u_core
            out[f"core{k}.ir"] = {"defined": val(core.ir) is not None, "xv": val(core.xv)}
        for inst, _words, _wb in SRAM_INSTANCES:
            h = _sram_handle(dut, inst)
            core = getattr(h, "i_SRAM_1P_behavioral_bm_bist", None)
            out[f"{inst}.dr_r"] = {"defined": core is not None and val(core.dr_r) is not None}
    except AttributeError:
        return {}
    return out


class Result:
    def __init__(self):
        self.mismatches = []
        self.x_cycles = []
        self.x_detail = []
        self.reset_checks = []
        self.mid_randomised = None
        self.pulse_edges = []
        self.run_pin_values = set()
        self.cycles = 0
        self.monitor = None
        self.stats = {}
        self.internal = []
        self.pulse = None
        self.latency = None

    def _latency(self):
        """Rising edges the rst_m/rst_q synchroniser holds rst_q low after a mid-run pulse."""
        if not self.pulse_edges:
            return None
        edges = self.pulse_edges
        low = [e["cycle"] for e in edges if e["rst_q"] == 0]
        if not low:
            return {"edges_low": 0, "note": "pulse did not reach rst_q"}
        first = min(low)
        held = []
        for e in edges:
            if e["cycle"] >= first and e["rst_q"] == 0:
                held.append(e["cycle"])
        active = [e["cycle"] for e in edges if e["rst_n"] == 0]
        return {"edges_low": len(held), "low_cycles": held,
                "reset_active_at_edge": active,
                "release_cycle": max(held) + 1}

    def write(self):
        path = os.environ.get("XINIT_RESULT")
        if not path:
            return
        Path(path).write_text(json.dumps({
            "scenario": os.environ.get("XINIT_SCENARIO", "?"),
            "mode": os.environ.get("XINIT_MODE", "?"),
            "seed": int(os.environ.get("XINIT_SEED", "0")),
            "gate": os.environ.get("XINIT_GATE") == "1",
            "cycles": self.cycles,
            "mismatches": len(self.mismatches),
            "first_mismatches": self.mismatches[:10],
            "x_cycles": self.x_cycles[:20],
            "x_detail": self.x_detail,
            "reset_checks": self.reset_checks,
            "mid_randomised": self.mid_randomised,
            "pulse": self.pulse,
            "pulse_edges": self.pulse_edges,
            "reset_latency": self.latency,
            "run_pin_values": sorted(self.run_pin_values),
            "internal": self.internal,
            "read_before_write": self.monitor.report() if self.monitor else None,
            "randomised": self.stats,
        }, indent=1), encoding="utf-8", newline="\n")


@cocotb.test()
async def xinit(dut):
    mode = os.environ["XINIT_MODE"]
    name = os.environ["XINIT_SCENARIO"]
    seed = int(os.environ["XINIT_SEED"])
    gate = os.environ.get("XINIT_GATE") == "1"
    assert mode in MODES, mode
    res = Result()
    scen = _scenario(name)
    res.pulse = getattr(scen, "pulse", None)
    res.monitor = None if gate else ReadBeforeWrite(dut)
    model = Chip()
    outs = (0, 0, 0)
    last_reset = -RESET_SETTLE_CYCLES
    try:
        res.stats = await _start(dut, mode, seed, gate)
        for t, (ui, hi, uio, rst_n) in enumerate(scen.steps):
            await FallingEdge(dut.clk)
            uio = (uio(t, outs) if callable(uio) else uio) & 0xff
            hi = hi(t, outs) if callable(hi) else hi
            ui = (ui & 0x07) | (hi & 0xf8)
            dut.ui_in.value = ui
            dut.uio_in.value = uio
            pulse = res.pulse
            if t == getattr(scen, "mid", None) and pulse:
                cocotb.start_soon(_pulse(dut, *pulse, seed, res, mode, gate))
            elif not pulse or t > scen.mid + 2 or t < scen.mid:
                if t == getattr(scen, "mid", None):
                    res.mid_randomised = _randomise(dut, f"{seed}:mid", mode, _paths(), gate,
                                                    preserve_reset=True)
                dut.rst_n.value = rst_n
            if not rst_n:
                last_reset = t
            exp = tuple(model.step(ui, uio, rst_n))
            if res.monitor:
                await Timer(HALF_PS - 1, unit="ps")
                res.monitor.sample(t)
            await RisingEdge(dut.clk)
            await ReadOnly()
            got = (val(dut.uo_out), val(dut.uio_out), val(dut.uio_oe))
            res.cycles += 1
            if pulse and scen.mid - 1 <= t <= scen.mid + 5:
                res.pulse_edges.append({"cycle": t, "rst_n": val(dut.rst_n),
                                        "rst_q": val(dut.rst_q)})
            if name == "xinit_load_run" and got[2] == 1 and got[1] is not None:
                res.run_pin_values.add(got[1] & 1)
            settled = t >= max(scen.compare_from, last_reset + RESET_SETTLE_CYCLES)
            if settled and None in got:
                res.x_cycles.append(t)
                if len(res.x_detail) < 5:
                    res.x_detail.append({"cycle": t, "got": got, "ui": ui, "uio": uio})
            if settled and mode != "x_probe" and got != exp:
                res.mismatches.append({"cycle": t, "rtl": got, "model": exp})
            if not gate and t == last_reset + RESET_SETTLE_CYCLES:
                state = {name: val(getattr(dut, name)) for name in
                         ("cfg", "run_g", "fl", "irqen", "inb", "outb", "misr", "dc", "o_out", "o_oe")}
                res.reset_checks.append({"cycle": t, "state": state})
                assert all(v == 0 for v in state.values()), state
                res.internal.append({"cycle": t, "signals": _internal_state(dut)})
            outs = exp
        if not gate:
            res.internal.append({"cycle": res.cycles, "signals": _internal_state(dut)})
        res.latency = res._latency()
        if scen.check is not None and mode != "x_probe":
            scen.check(model)
    finally:
        res.write()
    if mode == "x_probe":
        assert res.x_cycles and res.monitor.unwritten_reads, "expected host-contract counterexample"
        return
    if name == "xinit_load_run":
        assert res.run_pin_values == {0, 1}, "expected activity on enabled loopback pin"
    assert not res.x_cycles, f"X on an output at {res.x_detail}"
    assert not res.mismatches, f"{len(res.mismatches)} mismatches, first {res.mismatches[:1]}"
    if pulse:
        # Async assert: a pulse ending before a sampled edge holds rst_q low for that
        # one edge; a pulse that straddles a rising edge also clears rst_m, so the
        # release takes a second edge.  0 would mean the clear was missed.
        active = [e for e in res.pulse_edges if e["rst_n"] == 0]
        want = 2 if active else 1
        assert res.latency and res.latency["edges_low"] == want, (res.latency, res.pulse_edges)
    # Internal register names do not survive synthesis, so at gate level these cases rely on the
    # pin-level X and model checks above; res.internal stays empty there (review B1, 2026-11-19).
    if gate:
        return
    if mode == "x_check" and name == "xinit_load_run":
        last = res.internal[-1]["signals"]
        undefined = [k for k in ("core0.ir", "core1.ir") if not last[k]["defined"]]
        assert not undefined, f"instruction register still X after a complete load: {undefined}"
    if mode == "x_check" and name == "xinit_load_read":
        assert res.internal[-1]["signals"]["u_dmem.dr_r"]["defined"], "data RAM read register still X"


async def _pulse(dut, width, phase, seed, result, mode, gate):
    await Timer(phase, unit="ps")
    result.mid_randomised = _randomise(dut, f"{seed}:mid", mode, _paths(), gate, preserve_reset=True)
    dut.rst_n.value = 0
    await Timer(width, unit="ps")
    dut.rst_n.value = 1
