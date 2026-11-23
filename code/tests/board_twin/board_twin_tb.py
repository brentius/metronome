"""Board twin: run the real RP2350 loader core (code/host2/board) against the full-chip RTL.

The loader core is the same Python file the demo board runs.  `twin_bus.TwinBus` executes its operations on
`tt_um_brentius_metronome` with a configurable SCK period and sub-cycle phase/jitter, and `twin_bus.ModelMonitor`
compares every RTL output pin, every cycle, against the metronome2 cycle model.  `twin_check` turns the raw bytes a
trial returns into the PASS/FAIL verdict used by the sweep and by the negative control.

Environment:
    TWIN_RESULTS   path for the sweep result JSON   (default: sweep_results.json next to this file)
    TWIN_GRID      comma-separated "period:phase:jitter[:sample_lead]" points overriding the default sweep grid
    TWIN_SEED      PRNG seed for the first sweep point (default 1)

Evidence class: RTL-simulated (Icarus, IHP SRAM behavioural models) plus cycle-model comparison.  Not hardware.
"""
from __future__ import annotations

import json
import os
import sys
from pathlib import Path

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path[:0] = [str(HERE), str(ROOT / "sim/reference"), str(ROOT / "code/host2")]

from board.metronome_core import MetronomeHost, Timing, ID_VALUE, HOST_MAP_DATARAM  # noqa: E402
from twin_bus import CLOCK_PERIOD_PS, ModelMonitor, TwinBus  # noqa: E402
import twin_check  # noqa: E402

UART_BIT_CYCLES = 3125.0 / 6.0        # examples/uart_tx.mas: inc/mod = 6/3125 of the chip clock = 115200 baud
CHIP_CLOCK_HZ = 1e9 / CLOCK_PERIOD_PS  # 62.5 MHz in the twin; every SPEC ratio is clock-independent

#: (SCK period in chip cycles, first-edge phase, per-edge jitter in cycles[, MISO sample lead])
DEFAULT_GRID = [
    # SPEC-conforming: period >= 16 chip cycles (SCK <= clk/16), including the slow end and a non-integer period
    (32.0, 0.05, 0.0), (32.0, 0.50, 0.0), (32.0, 0.95, 0.0),
    (24.0, 0.05, 0.0), (24.0, 0.50, 0.0), (24.0, 0.95, 0.0),
    (20.0, 0.50, 0.0),
    (16.0, 0.05, 0.0), (16.0, 0.37, 0.0), (16.0, 0.50, 0.0), (16.0, 0.95, 0.0),   # the SPEC v2 9 limit, clk/16
    (16.0, 0.50, 0.45),                                                          # RP2350 GPIO jitter model
    (15.5, 0.50, 0.0),                                                           # walks every sub-cycle phase
    # faster than the SPEC allows: this is where the link breaks (upper bound for the spec margin)
    (15.0, 0.50, 0.0), (15.0, 0.95, 0.0),
    (12.0, 0.50, 0.0),
    (10.0, 0.95, 0.0),
    (8.0, 0.05, 0.0), (8.0, 0.50, 0.0), (8.0, 0.95, 0.0),                        # the lockstep bench's write rate
    (6.0, 0.50, 0.0), (6.0, 0.95, 0.0),
    (5.0, 0.05, 0.0), (5.0, 0.50, 0.0),
    (4.0, 0.05, 0.0), (4.0, 0.37, 0.0), (4.0, 0.62, 0.0), (4.0, 0.95, 0.0), (4.0, 0.50, 0.30),
    (3.5, 0.50, 0.0),
    (3.0, 0.50, 0.0), (3.0, 0.95, 0.0),
    (2.0, 0.05, 0.0), (2.0, 0.50, 0.0), (2.0, 0.95, 0.0),
    # MISO sample point: 5% of the half period before the edge instead of 25% (a real mode-0 master samples at the edge)
    (8.0, 0.50, 0.0, 0.05), (6.0, 0.50, 0.0, 0.05), (4.0, 0.50, 0.0, 0.05),
]


def zero_srams(dut) -> int:
    """The IHP SRAM models start as X and the model's memories start at 0 (copied from lockstep_v2/lockstep_tb.py)."""
    n = 0
    for inst, words in (("u_pmem0", 256), ("u_pmem1", 256), ("u_dmem", 512)):
        handle = getattr(dut, inst)
        try:
            mem = handle.u_sram.i_SRAM_1P_behavioral_bm_bist.memory
        except AttributeError:
            mem = handle.mem
        for i in range(words):
            mem[i].value = 0
        n += 1
    return n


async def bring_up(dut, trace_uo=True):
    """Clock at 16 ns, idle pins, RTL monitor and a bus aligned to a chip clock edge."""
    cocotb.start_soon(Clock(dut.clk, CLOCK_PERIOD_PS / 1000.0, unit="ns").start())
    dut.ena.value = 1
    dut.ui_in.value = 0x02          # CS_N high, SCK low
    dut.uio_in.value = 0
    dut.rst_n.value = 0             # start held in reset, like the board; the loader releases it
    zero_srams(dut)
    await RisingEdge(dut.clk)       # let the asynchronous reset settle before any output is compared
    await RisingEdge(dut.clk)
    monitor = ModelMonitor(dut, trace_uo=trace_uo)
    cocotb.start_soon(monitor.run())
    bus = TwinBus(dut)
    await bus.start()
    return monitor, bus


async def link_trial(bus, monitor, period, phase, jitter=0.0, seed=1, sample_lead=0.25):
    """Reset, then at one SCK timing point: read ID, round-trip a data-RAM block and a runtime register.

    The same data and register are read again at the spec rate (clk/16) afterwards, so a failure is attributed
    correctly: `*_via_spec` says the chip state is right (the write path survived the timing point), `readback` and
    `phase_readback` say the read path also worked at the trial timing, `id` covers the first read after reset.
    `phases` holds the chip-clock phase of every SCK rising edge of the trial transactions only (not of the
    clk/16 verification reads), and `cycles`/`mismatches` cover the whole trial.
    """
    host = MetronomeHost(Timing(period, phase, jitter, seed, sample_lead_fraction=sample_lead),
                         60000000.0, enforce_spec=False)
    spec_rate = MetronomeHost(Timing(16.0, 0.5), 60000000.0)
    mismatches_before = monitor.mismatch_count
    reported_before = len(monitor.mismatches)
    cycles_before = monitor.cycle
    nudges_before = bus.nudges
    await bus.realign()                                   # phase origin, so a point does not inherit the last one
    phases_before = len(bus.rise_phases)
    await bus.run(host.reset_sequence(hold_cycles=48, settle_cycles=48))

    id_value = await bus.run(host.read_id())
    payload = bytes((0x5A, 0xA5, 0x00, 0xFF))
    await bus.run(host.write(HOST_MAP_DATARAM + 0x40, payload))
    readback = bytes(await bus.run(host.read(HOST_MAP_DATARAM + 0x40, 4)))
    await bus.run(host.write(0x2410, b"\x34\x12"))       # LRT0.PHASE, a read/write runtime register
    phase_readback = bytes(await bus.run(host.read(0x2410, 2)))
    trial_phases = list(bus.rise_phases[phases_before:])
    data_via_spec = bytes(await bus.run(spec_rate.read(HOST_MAP_DATARAM + 0x40, 4)))
    phase_via_spec = bytes(await bus.run(spec_rate.read(0x2410, 2)))
    return {
        "id": id_value,
        "expect_data": payload.hex(),
        "expect_reg": "3412",
        "readback": readback.hex(),
        "phase_readback": phase_readback.hex(),
        "data_via_spec": data_via_spec.hex(),
        "phase_via_spec": phase_via_spec.hex(),
        "phases": trial_phases,
        "nudges": bus.nudges - nudges_before,
        "mismatches": monitor.mismatch_count - mismatches_before,
        "mismatch_detail": [list(map(str, m)) for m in monitor.mismatches[reported_before:]],
        "cycles": monitor.cycle - cycles_before,
    }


def decode_uart(trace, nbytes, bit_cycles=UART_BIT_CYCLES):
    """Independent 8N1 decoder over a per-cycle pin trace: (bytes, [start bit indices])."""
    falls = [i for i in range(1, len(trace)) if trace[i - 1] == 1 and trace[i] == 0]
    starts = []
    for f in falls:
        if not starts or f - starts[-1] > 9.5 * bit_cycles:
            starts.append(f)
        if len(starts) == nbytes:
            break
    if len(starts) != nbytes:
        raise AssertionError("found %d start bit(s), expected %d (falls at %s)" % (len(starts), nbytes, falls[:8]))
    out = []
    for start in starts:
        bits = [trace[int(round(start + (i + 0.5) * bit_cycles))] for i in range(10)]
        if bits[0] != 0 or bits[9] != 1:
            raise AssertionError("frame at %d has start=%d stop=%d (bits %s)" % (start, bits[0], bits[9], bits))
        out.append(sum(bits[1 + i] << i for i in range(8)))
    return out, starts


def _grid_from_env():
    raw = os.environ.get("TWIN_GRID")
    if not raw:
        return list(DEFAULT_GRID)
    grid = []
    for item in raw.replace(" ", "").split(","):
        if not item:
            continue
        parts = item.split(":")
        values = [float(x) for x in parts]
        while len(values) < 3:                     # period[:phase[:jitter[:sample_lead]]]
            values.append(0.5 if len(values) == 1 else 0.0)
        grid.append(tuple(values))
    return grid


async def wait_host_ready(bus, host, max_cycles=12 * UART_BIT_CYCLES):
    """Hold off until CTRL.HOSTSTAT bit 0 (INV) is clear, so a HOSTIN write is not overwritten (SPEC v2 9).

    Returns the number of cycles waited; raises if INV never clears, because writing anyway would silently drop a
    byte and turn the UART check into a race.
    """
    waited = 0
    while (await bus.run(host.hoststat())) & 1:
        if waited > max_cycles:
            raise AssertionError("HOST.INV stayed set for more than %d cycles" % int(max_cycles))
        await bus.run(host.delay(64))
        waited += 64
    return waited


# ==================================================================================================================
# cocotb tests


@cocotb.test()
async def twin_smoke(dut):
    """SPEC-limit timing (clk/16, worst phase): ID, data RAM, runtime register, full status read-back."""
    monitor, bus = await bring_up(dut)
    host = MetronomeHost(Timing(16.0, 0.95), 60000000.0)
    await bus.run(host.reset_sequence())

    assert await bus.run(host.read_id()) == ID_VALUE, "ID did not read 0xA2"
    payload = bytes(range(8))
    await bus.run(host.write(HOST_MAP_DATARAM + 0x100, payload))
    assert bytes(await bus.run(host.read(HOST_MAP_DATARAM + 0x100, 8))) == payload, "data RAM round-trip failed"

    # line 2 configuration first (write-only; reads 0, SPEC v2 9), then runtime registers, then start the line
    await bus.run(host.write(0x2040, b"\x01\x00"))          # L2.INC = 1
    await bus.run(host.write(0x2042, b"\x64\x00"))          # L2.MOD = 100
    for tap in (0x2044, 0x2046, 0x2048):                    # unused taps at or above MOD (SPEC v2 9a.10)
        await bus.run(host.write(tap, b"\xFF\xFF"))
    assert bytes(await bus.run(host.read(0x2040, 2))) == b"\x00\x00", "configuration must read 0"

    for addr, expected in ((0x2410, b"\x78\x56"), (0x2418, b"\x01\x00"),
                           (0x2440, b"\x42\x08"), (0x2422, b"\x01")):
        await bus.run(host.write(addr, expected))
        got = bytes(await bus.run(host.read(addr, len(expected))))
        assert got == expected, "0x%04X wrote %s read %s" % (addr, expected.hex(), got.hex())

    state = await bus.run(host.probe())
    assert state["ctrl"]["ID"] == ID_VALUE, state["ctrl"]
    assert state["ctrl"]["ERRSUM"] == 0, "ERRSUM after a load of nothing: 0x%02X" % state["ctrl"]["ERRSUM"]
    assert [t["EN"] for t in state["threads"]] == [1, 0, 0, 0, 0, 0], state["threads"]
    assert state["lines"][0]["PHASE"] == 0x5678, state["lines"][0]
    assert state["lines"][1]["PHASE"] == 1, state["lines"][1]
    assert state["lines"][2]["RUN"] == 1 and state["lines"][2]["ARM"] == 0, state["lines"][2]
    assert state["lines"][3]["RUN"] == 0, state["lines"][3]
    assert state["threads"][0]["PC"] == 0x42 and state["threads"][0]["EN"] == 1, state["threads"][0]
    assert not monitor.mismatches, "RTL vs model mismatches: %s" % (monitor.mismatches[:3],)
    dut._log.info("smoke: %d cycles, %d SCK edges, no model mismatch" % (monitor.cycle, len(bus.rise_phases)))


@cocotb.test()
async def twin_sweep(dut):
    """SCK period x phase x jitter sweep: where does the host link stop working?"""
    monitor, bus = await bring_up(dut)
    grid = _grid_from_env()
    results = []
    seed = int(os.environ.get("TWIN_SEED", "1"))
    for point in grid:
        period, phase, jitter = point[0], point[1], point[2]
        sample_lead = point[3] if len(point) > 3 else 0.25
        row = await link_trial(bus, monitor, period, phase, jitter, seed, sample_lead)
        phases = row.pop("phases") or [phase]
        row.update({"period": period, "phase": phase, "jitter": jitter, "seed": seed,
                    "sample_lead": sample_lead, "sck_divider": period,
                    "sck_hz_at_60mhz": 60000000.0 / period, "spec_ok": period >= 16.0})
        row.update(twin_check.trial_flags(row))
        row["rise_phase_min"] = min(phases)
        row["rise_phase_max"] = max(phases)
        row["rise_edges"] = len(phases)
        problems = twin_check.link_problems(row)
        row["problems"] = problems
        row["pass"] = not problems
        results.append(row)
        dut._log.info("clk/%-5.2f phase %.2f jit %.2f: id=%d read(data,reg)=%d%d write(data,reg)=%d%d mismatch=%d %s"
                      % (period, phase, jitter, row["id_ok"], row["read_data_ok"], row["read_reg_ok"],
                         row["write_data_ok"], row["write_reg_ok"], row["mismatches"],
                         "PASS" if row["pass"] else "FAIL"))
        seed += 1
    path = Path(os.environ.get("TWIN_RESULTS", str(HERE / "sweep_results.json")))
    path.write_text(json.dumps({"grid": results, "nudges": bus.nudges,
                                "clock_period_ps": CLOCK_PERIOD_PS,
                                "chip_clock_hz": CHIP_CLOCK_HZ}, indent=1) + "\n", encoding="utf-8")
    dut._log.info("sweep: %d points written to %s" % (len(results), path))
    # The sweep must never fail at a SPEC-conforming timing (this is the acceptance test; the rest is a report).
    bad = [r for r in results if r["spec_ok"] and not r["pass"]]
    assert not bad, "link failed at SPEC-conforming timings: %s" % (
        [(r["period"], r["phase"], r["problems"]) for r in bad],)


@cocotb.test()
async def twin_negative(dut):
    """Negative controls: the verdict must reject corrupt bytes, and a SPEC-violating SCK rate must fail.

    Control 1 is a mutation of the check itself: a passing result is copied, one raw field is corrupted, and the same
    `twin_check.link_problems()` that accepted the original must now reject the copy.  Control 2 is a real timing
    violation: SCK at clk/2 with `enforce_spec=False`, where the target cannot answer a read inside one SCK period.
    """
    monitor, bus = await bring_up(dut)

    # -- control 1: the check is sensitive to each raw field it compares ------------------------------------------
    good = await link_trial(bus, monitor, 16.0, 0.5)
    good.update(twin_check.trial_flags(good))
    assert twin_check.link_ok(good), twin_check.link_problems(good)
    dut._log.info("negative control 1: baseline trial at clk/16 passes (%s)", good["readback"])

    def mutated(**fields):
        copy = dict(good)
        copy.update(fields)
        return copy

    corrupted_data = (int(good["readback"][:2], 16) ^ 0x01)
    corruptions = {
        "corrupted readback byte": mutated(readback="%02x%s" % (corrupted_data, good["readback"][2:])),
        "corrupted register readback": mutated(phase_readback="3512"),
        "corrupted write-path evidence": mutated(data_via_spec="00" * 4),
        "wrong chip ID": mutated(id=0xA0),
        "single cycle-model mismatch": mutated(mismatches=1),
    }
    for name, row in corruptions.items():
        problems = twin_check.link_problems(row)
        assert problems, "the check accepted a %s" % name
        dut._log.info("negative control 1: %s rejected (%s)", name, problems[0])
    # ... and it is data-driven, not a hard-coded rejection: the same bytes as the expectation pass.
    assert twin_check.link_ok(mutated(expect_data=good["readback"])), "the check is not data-driven"

    # -- control 2: SCK at clk/2 is eight times over the SPEC v2 9 limit -----------------------------------------
    bad = await link_trial(bus, monitor, 2.0, 0.5)
    bad.update(twin_check.trial_flags(bad))
    problems = twin_check.link_problems(bad)
    assert problems, "SCK at clk/2 was reported as a working link: %s" % (bad,)
    assert bad["id"] != ID_VALUE, "ID still read 0xA2 with SCK at clk/2"
    assert bad["mismatches"] == 0, "the cycle model disagreed with the RTL at clk/2: %s" % (bad["mismatch_detail"],)
    dut._log.info("negative control 2: clk/2 rejected (ID 0x%02X, %d problem(s))", bad["id"], len(problems))


@cocotb.test()
async def twin_uart_tx(dut):
    """Load examples/uart_tx.mas with the real loader, then check the bytes it puts on O8 = uo_out[2]."""
    from metronome2_tools.asm import assemble_file
    from metronome2_tools.image import build_image

    monitor, bus = await bring_up(dut)
    host = MetronomeHost(Timing(16.0, 0.5), 60000000.0)
    await bus.run(host.reset_sequence())

    image = build_image(assemble_file(str(ROOT / "code/host2/examples/uart_tx.mas")))
    written = await bus.run(host.load_image(image))
    dut._log.info("loaded %d image bytes in %d frames" % (written, host.frames))

    # Image load + read-back: the state the image sets, read over the same link.
    state = await bus.run(host.probe())
    assert state["id"] == ID_VALUE, "ID 0x%02X" % state["id"]
    assert state["ctrl"]["RUN"] & 1, "CTRL.RUN not set by the image"
    assert state["lines"][0]["RUN"] & 1, "line 0 not running: CTL=0x%02X" % state["lines"][0]["CTL"]
    assert state["threads"][0]["EN"] & 1, "thread 0 not enabled: STAT=0x%02X" % state["threads"][0]["STAT"]
    assert state["ctrl"]["ERRSUM"] == 0, "ERRSUM 0x%02X after load" % state["ctrl"]["ERRSUM"]
    assert state["ctrl"]["HOSTSTAT"] == 0, "HOSTSTAT 0x%02X after load" % state["ctrl"]["HOSTSTAT"]
    # Program memory reads 0 (SPEC v2 9 host map), including after an image has written it.
    assert bytes(await bus.run(host.read(0x0000, 4))) == b"\x00\x00\x00\x00", "program memory must read 0"

    sent = [0xA5, 0x3C]
    start = monitor.mark()
    for byte in sent:
        waited = await wait_host_ready(bus, host)
        await bus.run(host.hostin(byte))
        dut._log.info("HOSTIN 0x%02X after %d idle cycles" % (byte, waited))
    await bus.run(host.delay(int(2.5 * 10 * UART_BIT_CYCLES)))
    trace = [((value >> 2) & 1) for value in monitor.trace_uo[start:monitor.mark()]]
    got, starts = decode_uart(trace, len(sent))
    dut._log.info("O8 trace %d cycles from %d, start bits at %s, decoded %s"
                  % (len(trace), start, starts, ["0x%02X" % b for b in got]))
    assert got == sent, "UART bytes on O8 were %s, expected %s" % (got, sent)
    assert not monitor.mismatches, "RTL vs model mismatches: %s" % (monitor.mismatches[:3],)
    final = await bus.run(host.probe())
    assert final["ctrl"]["ERRSUM"] == 0, "ERRSUM 0x%02X after two frames" % final["ctrl"]["ERRSUM"]
    assert not any(t["LATE"] or t["OVR"] for t in final["threads"]), final["threads"]
