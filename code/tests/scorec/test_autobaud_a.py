"""Autobaud plan A (v4, scorec/autobaud_a.py): the chip measures the LIN sync field and retunes its own receiver
through the v4 CW configuration writes. No host action after the image load.

Evidence class: verified in simulation on the v2/v3 cycle-level model extended with the v4 additions (SPEC v2 13,
model only) + the reference UART codec. No RTL for CW or replay yet, not hardware.

    python -m pytest code/tests/scorec/test_autobaud_a.py -q
"""
import json
import sys

import pytest
from harness import *

sys.path.insert(0, str(ROOT / "code" / "host2" / "autobaud"))
import lin_autobaud as la  # noqa: E402

PAYLOAD = bytes([0x3C, 0x01, 0x80, 0xFE, 0x55])
CACHE: dict = {}


def run(err, nominal=115200, **kw):
    return la.run_lin_frame_onchip(spec_block(0), nominal, err, PAYLOAD, rate_cache=CACHE, **kw)


def clean(r):
    return (not any(r["flags"].values())) and r["contract"] == []


def test_normal_form_image():
    import scorec
    c = scorec.compile_score(spec_block(0), "receiver", "tx=P5", rate_hz=115200, autobaud={"plan": "A"})
    assert c.errors == [] and c.host["autobaud"]["plan"] == "A"
    line0 = c.mas.split(".line 0")[1].split(".end")[0]
    assert "inc 8" in line0 and "mod 4167" in line0 and "taps 65535 2083 65535" in line0 and "preset 24" in line0
    assert "ctl arm" not in line0                         # armed by the firmware, not the loader
    assert "mark 44" in c.mas.split(".stream 0")[1].split(".end")[0]


@pytest.mark.parametrize("err", [0.0, 0.07, -0.07, 0.14, -0.14, 0.5, -0.5])
def test_lin_frame_retunes_on_chip(err):
    r = run(err)
    assert r["ok"], (r["received"].hex(), r["statuses"])
    assert clean(r), (r["flags"], r["contract"])
    true_bit = 60e6 / (115200 * (1 + err))
    assert abs(r["bit_cycles"] - true_bit) / true_bit < 0.002          # 8-bit-time measurement, 1-cycle resolution
    assert r["armed_at"] < r["data_start"]


@pytest.mark.parametrize("nominal,gap", [(9600, 0), (19200, 0), (460800, 3)])
def test_other_nominal_rates(nominal, gap):
    # 460800: the firmware needs ~350 cycles after the last sync edge, more than the 2 bit times (260 cycles) before a
    # back-to-back data byte, so a LIN response space of 3 bit times is given (allowed by LIN; see the latency test)
    for err in (0.0, 0.2, -0.2):
        r = run(err, nominal=nominal, gap_bits=gap)
        assert r["ok"] and clean(r), (nominal, err, r["received"].hex(), r["statuses"], r["flags"])


def test_back_to_back_limit_at_460800():
    """Back to back at 460800 the first data byte is lost (the firmware is still retuning): a stated limit, not hidden."""
    r = run(0.0, nominal=460800)
    assert not r["ok"] and r["statuses"][0] != 0 and r["statuses"][1:] == [0] * (len(r["statuses"]) - 1)


def test_missing_break_is_rejected_and_capture_restarts():
    """A sync field without a break (a delimiter-length low only) must not retune: line 0 stays disarmed."""
    r = run(0.0, break_bits=1)
    assert r["armed_at"] is None and r["statuses"] == []      # S0 still holds capture records, not received bytes
    ch = r["chip"]
    assert ch.CEN == 1                                          # still (re)capturing, waiting for a real header


def test_short_break_rejected_long_break_accepted():
    assert run(0.0, break_bits=10)["armed_at"] is None          # 10 bits < 12: a data byte can be 9 bits low
    assert run(0.0, break_bits=13)["ok"]
    assert run(0.0, break_bits=40)["ok"]


def test_mutant_wrong_shift_fails(monkeypatch):
    import scorec.autobaud_a as aa
    monkeypatch.setattr(aa, "SHIFT", 4)
    r = la.run_lin_frame_onchip(spec_block(0), 115200, 0.0, PAYLOAD, rate_cache={})
    assert not r["ok"]


def test_error_window_and_latency_record():
    """Sweep the master clock error at 115200 nominal; record the window, the bit-time error and the firmware latency
    (bit-7 fall of the sync to the receiver armed). Written to data/processed/v4_autobaud/."""
    errs = [round(e / 100, 2) for e in range(-80, 201, 20)]
    res = {}
    for e in errs:
        r = run(e)
        bit = 60e6 / (115200 * (1 + e))
        b7_fall = r["data_start"] - round(2 * bit)               # sync bit-7 fall: 2 bit times before the data start
        res[e] = {"ok": bool(r["ok"] and clean(r)), "bit_err_ppm": round((r["bit_cycles"] / bit - 1) * 1e6),
                  "latency_cycles": (r["armed_at"] - b7_fall) if r["armed_at"] else None,
                  "slack_cycles": (r["data_start"] - r["armed_at"]) if r["armed_at"] else None}
    passing = [e for e in errs if res[e]["ok"]]
    lo, hi = min(passing), max(passing)
    assert all(res[e]["ok"] for e in errs if lo <= e <= hi), res
    assert lo <= -0.6 and hi >= 0.8, (lo, hi)                   # at least plan B's -60 %..+80 % window
    lat = max(v["latency_cycles"] for v in res.values() if v["latency_cycles"] is not None)
    out = ROOT / "data" / "processed" / "v4_autobaud"
    out.mkdir(parents=True, exist_ok=True)
    (out / "lin_onchip_sweep_115200.json").write_text(json.dumps({
        "evidence": "verified in simulation: v2/v3 cycle-level model with the v4 model additions (CW, SPEC v2 13) + "
                    "reference UART codec; no RTL for v4, not hardware",
        "nominal_baud": 115200, "payload": PAYLOAD.hex(), "data_gap_bits": 0,
        "per_error": {str(k): v for k, v in res.items()}, "pass_window": [lo, hi],
        "max_latency_cycles": lat,
        "back_to_back_rate_limit_hz_calculated": round(60e6 / (lat / 2)),
    }, indent=1), encoding="utf-8")
