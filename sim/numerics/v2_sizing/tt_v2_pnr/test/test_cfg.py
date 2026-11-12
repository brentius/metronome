"""Configuration latch write path at gate level, meant for a back-annotated (SDF) run (V2_DESIGN 4.7, D24).

    python run_local.py --gl NETLIST --pdk-stdcell DIR --sdf CORNER.sdf --test test_cfg

Writes every configuration byte through the real SPI host path and reads each existing latch's Q net directly
(cfg_probe, generated from the netlist by gen_cfg_probe.py). Checks:
  1. reset clears every latch;
  2. five whole-bank patterns land exactly (random, its complement, all ones, all zeros, alternating);
  3. 56 single-byte writes each change only their byte;
  4. reset in the middle of operation clears every latch, and writing works after it;
  5. each write gives exactly one strobe on its byte's gated clock and none elsewhere (cfg_gate_cnt);
  6. the per-latch monitors (cfg_latch_chk) saw no setup, hold or gate-width violation, no X, and D never moved
     while a latch was open (the D24 property: data settles before the gate opens);
  7. the SDF delays are in effect: Q changes a nonzero time after its gate opens.
CLK_PS (environment, default 16666) sets the clock period; a short period is the negative control.
"""
import json
import os
import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles

from test import A_CFG, CS_N, Host

CFG_BYTES = 56
CLK_PS = int(os.environ.get("CLK_PS", "16666"))


def expected(state, bits):
    v = 0
    for n in bits:
        k, b = divmod(n, 8)
        if (state[k] >> b) & 1:
            v |= 1 << n
    return v


@cocotb.test()
async def test_cfg_write_path(dut):
    probe = json.load(open(os.environ["CFG_PROBE_JSON"]))
    bits, gated = probe["bits"], probe["gated_bytes"]
    mask = sum(1 << n for n in bits)
    dut._log.info(f"{len(bits)} latches, {len(gated)} clock gates, clock {CLK_PS} ps")

    cocotb.start_soon(Clock(dut.clk, CLK_PS, unit="ps").start())
    dut.ena.value = 1
    dut.ui_in.value = 1 << CS_N
    dut.uio_in.value = 0
    dut.rst_n.value = 0
    await ClockCycles(dut.clk, 10)
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 10)
    dut.chk_arm.value = 1

    host = Host(dut)
    state = [0] * CFG_BYTES
    writes = [0] * CFG_BYTES
    checks = 0

    def check(what):
        nonlocal checks
        v = dut.cfg_probe.value
        if not v.is_resolvable:
            s = str(v)[::-1]                    # index i = bit i
            xs = [n for n in bits if s[n] not in "01"]
            assert not xs, f"{what}: latch outputs not 0/1 at bits {xs[:16]}"
        got, exp = int(v) & mask, expected(state, bits)
        if got != exp:
            diff = [n for n in bits if ((got ^ exp) >> n) & 1]
            raise AssertionError(f"{what}: {len(diff)} latch bits differ, first {diff[:16]}")
        checks += 1

    check("after reset")

    rng = random.Random(20261112)
    first = [rng.randrange(256) for _ in range(CFG_BYTES)]
    patterns = [first, [x ^ 0xFF for x in first], [0xFF] * CFG_BYTES, [0x00] * CFG_BYTES,
                [0x55 if k % 2 else 0xAA for k in range(CFG_BYTES)]]
    for i, p in enumerate(patterns):
        await host.write(A_CFG, p)
        state = list(p)
        writes = [w + 1 for w in writes]
        await ClockCycles(dut.clk, 4)
        check(f"whole-bank pattern {i}")

    for k in range(CFG_BYTES):
        v = state[k] ^ (1 + rng.randrange(255))      # always a change
        await host.write(A_CFG + k, [v])
        state[k] = v
        writes[k] += 1
        await ClockCycles(dut.clk, 4)
        check(f"single byte {k}")

    dut.rst_n.value = 0
    await ClockCycles(dut.clk, 3)
    state = [0] * CFG_BYTES
    check("during reset")
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 10)
    check("after second reset")
    last = [rng.randrange(256) for _ in range(CFG_BYTES)]
    await host.write(A_CFG, last)
    state = list(last)
    writes = [w + 1 for w in writes]
    await ClockCycles(dut.clk, 4)
    check("write after second reset")

    pulses = {k: int(getattr(dut, f"u_gck_{k}").pulses.value) for k in gated}
    bad = {k: (pulses[k], writes[k]) for k in gated if pulses[k] != writes[k]}
    counters = {n: int(getattr(dut, f"chk_{n}").value) for n in ("setup_err", "hold_err", "width_err",
                                                                   "open_change", "x")}
    lat = (float(dut.chk_q_lat_min.value), float(dut.chk_q_lat_max.value))
    dut._log.info(f"state checks {checks}; strobes per byte match writes on {len(gated) - len(bad)}/{len(gated)} "
                  f"bytes; monitors {counters}; Q after gate opens {lat[0]:.3f} to {lat[1]:.3f} ns")
    assert not bad, f"strobe count (pulses, writes) per byte differs: {bad}"
    assert all(v == 0 for v in counters.values()), f"latch timing monitors: {counters}"
    assert lat[0] > 0.05, f"Q followed its gate in {lat[0]:.3f} ns: SDF delays do not look applied"
