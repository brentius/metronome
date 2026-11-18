"""LIN-style autobaud, plan B (see scorec/autobaud.py): the chip logs the falling-edge intervals of the sync field, this
module turns them into a divider and the few host writes that retune the receiver.

SPEC_V2 3.1/9: a line's INC/MOD/taps/PRE are host-written, write-only latch configuration with no move destination, so a
program cannot change its own bit time (plan A is not available).  The chip measures; the host computes the bit time and
writes line 0's registers and the ARM bit before the first data character.

Pure functions, no model needed: `measure`, `retune_writes`.  `run_lin_frame` drives a compiled image on the v2
cycle-level model with a LIN master of a chosen clock error (tests and the sweep use it).

Evidence class when run: verified in simulation (v2 cycle-level model + the reference UART codec); the bias term is
calibrated on the model.  Not RTL lockstep, not hardware.
"""
from __future__ import annotations

import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
for p in (ROOT / "code" / "scorec", ROOT / "code" / "score", ROOT / "code" / "host2", ROOT / "sim" / "reference",
          ROOT / "code" / "tests" / "scorec"):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))

CLOCK_HZ = 60e6
LINE0_CFG = range(0x2000, 0x2020)       # line 0 configuration registers (ISA_TABLES_V2 host map)
LRT0_CTL = 0x2412                        # line 0 CTL (RUN, ARM, REN)
ARM = 0x02
# Each of the four 2-bit intervals reads short by the ruler's restart latency (the ruler restarts the interval counter
# at its next tick after the snapshot, so on average half a tick plus a few cycles are lost).  Added back per interval.
BIAS_CYCLES = 20.0          # calibrated on the model at 115200 baud: 85 ticks x 12 = 1020 read for a true 1041.7-cycle interval


@dataclass
class Measurement:
    ok: bool
    reason: str = ""
    ticks: list = field(default_factory=list)       # interval of each logged fall, in ruler ticks
    bit_cycles: float | None = None
    rate_hz: float | None = None


def parse_log(log: bytes, n=6):
    return [0xFFFF - (log[2 * i] | (log[2 * i + 1] << 8)) for i in range(n)]


def measure(log: bytes, tick_cycles: int, *, spread=0.08, min_break_ratio=5.0, n=6, bias=None) -> Measurement:
    """Bit time from a log of six falls: [power-up to break, break+delimiter, 2 bits, 2 bits, 2 bits, 2 bits].

    Accepts only a plausible sync field: the four 2-bit intervals agree within `spread` and the break interval is at least
    `min_break_ratio` times one of them (a break is >= 13 bit times, a 2-bit interval is 2).  Otherwise the host should
    reset and wait for the next header."""
    if len(log) < 2 * n:
        return Measurement(False, "log too short")
    ticks = parse_log(log, n)
    iv = ticks[2:6]
    if min(iv) == 0 or ticks[1] >= 0xFFFF:
        return Measurement(False, "counter saturated or zero interval", ticks)
    mean = sum(iv) / 4
    if (max(iv) - min(iv)) / mean > spread:
        return Measurement(False, f"sync intervals disagree: {iv}", ticks)
    if ticks[1] < min_break_ratio * mean:
        return Measurement(False, "no break before the sync field", ticks)
    b = BIAS_CYCLES if bias is None else bias
    bit = (sum(iv) * tick_cycles + 4 * b) / 8
    return Measurement(True, "", ticks, bit, CLOCK_HZ / bit)


def retune_writes(base, retuned, *, arm=True):
    """Host writes (addr, bytes) that turn the image compiled for the nominal rate into the one for the measured rate.

    `base` and `retuned` are `Compiled` results (compiled with `autobaud=...`).  Raises when the two images differ
    outside line 0's configuration registers (then a full reload would be needed)."""
    from metronome2_tools.image import host_writes
    a = {addr + k: b for addr, data, _ in host_writes(base.program) for k, b in enumerate(data)}
    out = []
    for addr, data, _ in host_writes(retuned.program):
        for k, b in enumerate(data):
            if a.get(addr + k) != b:
                if addr + k not in LINE0_CFG:
                    raise ValueError(f"retuned image differs at 0x{addr + k:04X}, outside line 0 configuration")
                out.append((addr + k, bytes([b])))
    if arm:
        out.append((LRT0_CTL, bytes([ARM])))
    return out


def run_lin_frame(base_score, nominal_hz, master_error, payload, *, bind="tx=P5", tick_cycles=12, host_latency_cycles=500,
                  break_bits=13, delimiter_bits=1, rate_cache=None, bias=None):
    """One LIN-style frame on the model.  The master runs at nominal_hz * (1 + master_error): break, delimiter, sync 0x55,
    then `payload` as 8N1 characters, back to back.  The chip is compiled for nominal_hz with the measurement attached.

    `host_latency_cycles`: cycles from the chip's last progress byte (1) until the host's retune lands.
    Returns a dict: measurement, applied writes, received bytes, statuses, the cycle the retune landed and the cycle
    the first data character starts (so the host's slack can be reported)."""
    import scorec
    from harness import IDLE, Codec, new_chip, parse
    cache = rate_cache if rate_cache is not None else {}
    base = cache.get(nominal_hz)
    if base is None:
        base = scorec.compile_score(base_score, "receiver", bind, rate_hz=nominal_hz, autobaud={"tick_cycles": tick_cycles})
        cache[nominal_hz] = base
    rate_m = nominal_hz * (1 + master_error)
    pm = CLOCK_HZ / rate_m
    enc = Codec(parse(base_score), rate=rate_m).encode_all([("data", 0x55)] + [("data", b) for b in payload])
    chars = list(enc.bus["tx"])
    first = next(i for i in range(1, len(chars)) if chars[i] == 0 and chars[i - 1] == 1)
    wave = [1] * 300 + [0] * round(break_bits * pm) + [1] * round(delimiter_bits * pm) + chars[first:]
    sync_start = 300 + round(break_bits * pm) + round(delimiter_bits * pm)
    data_start = sync_start + round(10 * pm) + 40
    chip = new_chip(base)
    for _ in range(40):
        chip.step(IDLE, 1 << 5)
    res = {"measurement": None, "writes": [], "statuses": [], "retuned_at": None, "data_start": data_start,
           "latency_slack_cycles": None}
    due, state = None, None
    t = 0
    for lvl in wave + [1] * int(30 * pm):
        chip.step(IDLE, (lvl & 1) << 5)
        t += 1
        if chip.host.OUTV:
            b = chip.host.OUTB
            chip.host.OUTV = 0
            if state is None and b == 1:
                due, state = t + host_latency_cycles, "waiting"
            elif state == "done":
                res["statuses"].append(b)
        if state == "waiting" and t >= due:
            m = measure(bytes(chip.mem.data[0:12]), tick_cycles, bias=bias)
            res["measurement"] = m
            state = "done"
            if m.ok:
                new = scorec.compile_score(base_score, "receiver", bind, rate_hz=m.rate_hz,
                                           autobaud={"tick_cycles": tick_cycles})
                for addr, data in retune_writes(base, new):
                    chip.backdoor_write(addr, data)
                    res["writes"].append((addr, data.hex()))
                res["retuned_at"] = t
                res["latency_slack_cycles"] = res["data_start"] - t
    n = chip.mem.streams[0].POS
    res["received"] = bytes(chip.mem.data[0x400:0x400 + n])
    res["ok"] = res["received"] == bytes(payload) and res["statuses"] == [0] * len(payload)
    res["flags"] = {"late_ovr": any(th.LATE or th.OVR for th in chip.threads), "conflict": chip.ctrl.CONFLICT}
    return res


# ---- plan A (v4, model only): the chip retunes itself ------------------------------------------------------------
def run_lin_frame_onchip(base_score, nominal_hz, master_error, payload, *, bind="tx=P5", break_bits=13,
                         delimiter_bits=1, gap_bits=0.0, rate_cache=None, idle_cycles=300):
    """Plan A (scorec/autobaud_a.py): compile with autobaud={"plan": "A"}, drive one LIN-style frame and let the chip
    measure the sync field and retune line 0 itself. No host action after the image load.

    gap_bits: extra idle after the sync character before the first data character (0 = back to back, the hardest case).
    Returns a dict: received bytes, statuses, line 0 MOD/T1 after the run, the cycle the receiver was armed, error
    flags and contract violations."""
    import scorec
    from harness import IDLE, Codec, new_chip, parse
    cache = rate_cache if rate_cache is not None else {}
    base = cache.get(("A", nominal_hz))
    if base is None:
        base = scorec.compile_score(base_score, "receiver", bind, rate_hz=nominal_hz, autobaud={"plan": "A"})
        cache[("A", nominal_hz)] = base
    rate_m = nominal_hz * (1 + master_error)
    pm = CLOCK_HZ / rate_m
    enc = Codec(parse(base_score), rate=rate_m).encode_all([("data", 0x55)])
    sync = list(enc.bus["tx"])
    s0 = next(i for i in range(1, len(sync)) if sync[i] == 0 and sync[i - 1] == 1)
    sync = sync[s0:s0 + round(10 * pm)]
    data = list(Codec(parse(base_score), rate=rate_m).encode_all([("data", b) for b in payload]).bus["tx"])
    d0 = next(i for i in range(1, len(data)) if data[i] == 0 and data[i - 1] == 1)
    wave = ([1] * idle_cycles + [0] * round(break_bits * pm) + [1] * round(delimiter_bits * pm) + sync
            + [1] * round(gap_bits * pm) + data[d0:])
    data_start = idle_cycles + round(break_bits * pm) + round(delimiter_bits * pm) + len(sync) + round(gap_bits * pm)
    chip = new_chip(base)
    pin = 1 << 5
    for _ in range(40):
        chip.step(IDLE, pin)
    res = {"statuses": [], "armed_at": None, "data_start": data_start + 40}
    for lvl in wave + [1] * int(30 * pm):
        chip.step(IDLE, (lvl & 1) << 5)
        if chip.host.OUTV:
            res["statuses"].append(chip.host.OUTB)
            chip.host.OUTV = 0
        if res["armed_at"] is None and chip.lines[0].ARM:
            res["armed_at"] = chip.cycle
    n = chip.mem.streams[0].POS
    res["received"] = bytes(chip.mem.data[0x400:0x400 + n])
    res["ok"] = res["received"] == bytes(payload) and res["statuses"] == [0] * len(payload)
    res["mod"], res["inc"] = chip.lines[0].MOD, chip.lines[0].INC
    res["bit_cycles"] = res["mod"] / res["inc"]
    res["flags"] = {"late_ovr": any(th.LATE or th.OVR for th in chip.threads), "conflict": chip.ctrl.CONFLICT,
                    "memhaz": chip.ctrl.MEMHAZ, "cwovr": chip.ctrl.CWOVR,
                    "starved": any(s.STARVED for s in chip.mem.streams)}
    res["contract"] = list(chip.contract_violations)
    res["chip"] = chip
    return res
