"""Autobaud / LIN sync, plan B (scorec/autobaud.py, host2/autobaud/lin_autobaud.py) on the v2 cycle-level model.

SPEC_V2 has no move destination for a line's INC/MOD/taps/PRE (host-written, write-only latch configuration), so a program
cannot change its own bit time: plan A is unavailable and the host sets the divider after the chip measures the LIN
sync field.  The sweep records the master clock error window inside which the frame is received exactly.

Evidence class: verified in simulation (v2 model + reference UART codec).  Not RTL lockstep, not hardware."""
import json
import sys

import pytest
from harness import *

sys.path.insert(0, str(ROOT / "code" / "host2" / "autobaud"))
import lin_autobaud as la  # noqa: E402

PAYLOAD = bytes([0x3C, 0x01, 0x80, 0xFE, 0x55])          # PID, data, checksum-like bytes: all 8-bit patterns that matter
CACHE_115200: dict = {}


def test_plan_a_is_not_available_no_program_destination_reaches_line_configuration():
    dests = [d for d in m.DEST_PORTS] if hasattr(m, "DEST_PORTS") else None
    if dests is None:
        txt = (ROOT / "wiki" / "ISA_TABLES_V2.md").read_text(encoding="utf-8")
        dest = txt.split("## Destination ports")[1].split("## Guard conditions")[0]
        names = [l.split("|")[2].strip(" `") for l in dest.splitlines() if l.startswith("| ") and l.split("|")[1].strip().isdigit()]
    else:
        names = [str(d) for d in dests]
    for forbidden in ("INC", "MOD", "PRE", "T0", "T1", "T2", "WLO", "WHI"):
        assert not any(forbidden in n for n in names if n.startswith("L")), (forbidden, names)
    assert [n for n in names if n.startswith("L") and "CTL" in n]       # only RUN/ARM/REN are program-writable


def test_measure_pure_function():
    # six falls: power-up, break+delimiter, four 2-bit intervals of 780 ticks (12 cycles per tick: 2 bits = 9360 cycles)
    iv = [42, 5467, 780, 781, 779, 780]
    log = b"".join((0xFFFF - v).to_bytes(2, "little") for v in iv)
    r = la.measure(log, 12, bias=0)
    assert r.ok and abs(r.bit_cycles - 4680.0) < 1
    assert not la.measure(b"".join((0xFFFF - v).to_bytes(2, "little") for v in [42, 5467, 780, 1560, 780, 780]), 12).ok
    assert not la.measure(b"".join((0xFFFF - v).to_bytes(2, "little") for v in [42, 1000, 780, 780, 780, 780]), 12).ok


def test_retune_touches_only_line_0_configuration():
    import scorec
    base = scorec.compile_score(spec_block(0), "receiver", "tx=P5", rate_hz=115200, autobaud={})
    new = scorec.compile_score(spec_block(0), "receiver", "tx=P5", rate_hz=115200 * 1.1, autobaud={})
    w = la.retune_writes(base, new)
    assert w and all(la.LINE0_CFG.start <= a < la.LINE0_CFG.stop or a == la.LRT0_CTL for a, _ in w)
    assert len(w) <= 12 and w[-1] == (la.LRT0_CTL, bytes([la.ARM]))


def test_autobaud_receiver_is_disarmed_until_the_host_arms_it():
    import scorec
    c = scorec.compile_score(spec_block(0), "receiver", "tx=P5", rate_hz=115200, autobaud={})
    assert "ctl arm" not in c.mas.split(".line 1")[0] and c.errors == []
    assert c.host["autobaud"]["plan"] == "B"


@pytest.mark.parametrize("err", [0.0, 0.07, -0.07, 0.14, -0.14])
def test_lin_frame_decodes_with_master_clock_error(err):
    r = la.run_lin_frame(spec_block(0), 115200, err, PAYLOAD, rate_cache=CACHE_115200)
    assert r["measurement"].ok, (r["measurement"].reason, r["measurement"].ticks)
    assert r["ok"], (r["received"].hex(), r["statuses"])
    assert not r["flags"]["late_ovr"] and r["flags"]["conflict"] == 0
    true_bit = 60e6 / (115200 * (1 + err))
    assert abs(r["measurement"].bit_cycles - true_bit) / true_bit < 0.01          # measured bit time within 1%
    assert r["latency_slack_cycles"] > 0


def test_missing_break_is_rejected_not_guessed():
    """A header without a break (a sync field alone) must not retune: measure() refuses and the receiver stays disarmed."""
    r = la.run_lin_frame(spec_block(0), 115200, 0.0, PAYLOAD, break_bits=1, rate_cache=CACHE_115200)
    assert r["measurement"] is not None and not r["measurement"].ok and not r["ok"]


def test_host_latency_budget_and_sweep_window():
    """The retune has to land before the first data character starts (about 2 bit times after the last logged fall).
    The error window is swept at 115200 baud nominal; the record is written to data/processed/v3_autobaud/."""
    base_slack = la.run_lin_frame(spec_block(0), 115200, 0.0, PAYLOAD, rate_cache=CACHE_115200, host_latency_cycles=500)
    assert base_slack["ok"]
    slack = base_slack["latency_slack_cycles"]
    late = la.run_lin_frame(spec_block(0), 115200, 0.0, PAYLOAD, rate_cache=CACHE_115200, host_latency_cycles=500 + slack + 100)
    assert not late["ok"]                                                      # too slow a host loses the first character
    errs = [round(e / 100, 2) for e in range(-60, 81, 20)]
    results = {}
    for e in errs:
        r = la.run_lin_frame(spec_block(0), 115200, e, PAYLOAD, rate_cache=CACHE_115200)
        results[e] = bool(r["ok"])
    passing = [e for e in errs if results[e]]
    lo, hi = min(passing), max(passing)
    assert all(results[e] for e in errs if lo <= e <= hi), results             # one contiguous window
    assert lo <= -0.5 and hi >= 0.5, (lo, hi, results)                       # at least the +-14% a Loom LIN slave claims; measured -60%..+80% at this host latency
    out = ROOT / "data" / "processed" / "v3_autobaud"
    out.mkdir(parents=True, exist_ok=True)
    (out / "lin_sweep_115200.json").write_text(json.dumps({
        "evidence": "verified in simulation: v2 cycle-level model + reference UART codec; not RTL, not hardware",
        "nominal_baud": 115200, "tick_cycles": 12, "payload": PAYLOAD.hex(), "step": 0.20,
        "master_error_vs_pass": {str(k): v for k, v in results.items()},
        "pass_window": [lo, hi], "latency_slack_cycles_at_zero_error": slack}, indent=1), encoding="utf-8")
