"""Stage 1 on-chip inference firmware (transcribe/fw_stage1.py) on the cycle model (v4 additions, SPEC v2 13).

The chip captures 64 edges itself, runs the bit-time inference with no host action, writes the learned beat to line 0
and a result block to RAM. Checked bit-exact against the integer reference `chipinfer.stage1` run on the very words
the chip captured, and against the true rate. Evidence: cycle model + reference codec waveforms; no RTL, no hardware.
"""
import json
from pathlib import Path

import pytest

from harness import Codec, load, parse  # noqa: E402
from metronome2 import Chip  # noqa: E402
from metronome2_tools.asm import assemble_text  # noqa: E402
from metronome2_tools.check import check  # noqa: E402
from test_transcribe import CASES, FS, capture, hidden_text, rand_bytes  # noqa: E402
from transcribe.chipinfer import stage1  # noqa: E402
from transcribe.fw_stage1 import FRAME_RES, RES, count_insns, source  # noqa: E402

PIN, NREC = 5, 64
ROOT = Path(__file__).resolve().parents[3]
_PROG = {}


def prog():
    if "p" not in _PROG:
        _PROG["t"] = source(PIN, NREC)
        _PROG["p"] = assemble_text(_PROG["t"])
    return _PROG["p"]


def run_fw(levels, max_cycles=3_000_000, *, pin=PIN, framing=False, output=None, reply=None):
    ch = Chip()
    image = prog() if not framing and pin == PIN else assemble_text(
        source(pin, NREC, framing=framing, transmit=output is not None, reply=reply))

    def step(level):
        if pin < 8:
            return ch.step(0x02, level << pin)
        return ch.step(0x02 | (level << (pin - 5)), 0)

    for _ in range(3):
        step(levels[0])
    load(ch, image)
    t = 0
    tail = levels[-1]
    done_at = None
    while t < max_cycles:
        lv = levels[t] if t < len(levels) else tail
        was_sending = ch.lines[0].RUN
        uo, _, _ = step(lv)
        if output is not None and (was_sending or output):
            output.append((uo >> 2) & 1)
        t += 1
        complete = ch.host.OUTV if framing else not ch.threads[0].EN
        if complete and t > 10:
            done_at = t
            break
    words = [int.from_bytes(ch.mem.data[4 * i:4 * i + 4], "little") for i in range(NREC)]
    res = list(ch.mem.data[RES:RES + 6])
    return ch, words, res, done_at


def test_fits_and_passes_static_check():
    n = count_insns(source(PIN, NREC))
    assert n[0] <= 256 and n[1] <= 256, n
    rep = check(prog())
    errs = [e for e in getattr(rep, "errors", [])]
    assert errs == [], errs


@pytest.mark.parametrize(("pin", "width", "parity", "stops", "idle"),
                         [(5, 8, None, 1, 1), (10, 7, "even", 2, 1), (5, 8, "odd", 1, 0)])
def test_framing_firmware(pin, width, parity, stops, idle):
    rate = 460_800
    hidden = hidden_text(rate, width, parity, stops, idle)
    payload = rand_bytes(32, width, 7)
    levels = capture(hidden, payload, rate, 0.015, 2)
    output = []
    ch, _, result, done = run_fw([idle] * 1000 + levels, pin=pin, framing=True, output=output)
    assert done is not None
    assert result[:2] == [1, idle]
    status, decoded_width, decoded_parity, frames, decoded_stops = ch.mem.data[FRAME_RES:FRAME_RES+5]
    assert (status, decoded_width, decoded_parity, decoded_stops) == (
        1, width, (None, "even", "odd").index(parity), stops)
    assert frames >= 4
    assert ch.host.OUTB == 1
    assert output and output[-1] == idle
    replay = Codec(parse(hidden)).decode("receiver", {"tx": output + [idle] * int(4 * FS / rate)})
    assert replay.ok, replay.notes
    assert [value for field, value in replay.events if field == "data"] == payload[:frames]
    assert not any(s.STARVED for s in ch.mem.streams)
    assert not (ch.ctrl.CWOVR or ch.ctrl.MEMHAZ or ch.ctrl.CONFLICT)
    assert not any(t.LATE or t.OVR for t in ch.threads)
    assert ch.contract_violations == []


def test_framing_image_fits_and_passes_static_check():
    text = source(framing=True, transmit=True)
    assert max(count_insns(text).values()) <= 256
    assert check(assemble_text(text)).errors == []


@pytest.mark.parametrize(("rate", "width", "parity", "stops", "idle", "clock_error", "jitter"), [
    (115200, 8, None, 1, 1, 0.015, 2),
    (460800, 7, "even", 2, 0, 0.015, 2),
    (1000000, 9, "odd", 1, 1, 0.0, 0),
    (3750000, 8, None, 1, 1, 0.0, 0),
])
def test_firmware_encodes_a_held_out_uart_byte(rate, width, parity, stops, idle, clock_error, jitter):
    reply = 0x42
    training = [byte for byte in rand_bytes(32, width, 7) if byte != reply]
    hidden = hidden_text(rate, width, parity, stops, idle)
    levels = capture(hidden, training, rate, clock_error, jitter)
    output = []
    text = source(framing=True, transmit=True, reply=reply)
    assert max(count_insns(text).values()) <= 256
    assert check(assemble_text(text)).errors == []
    ch, _, result, done = run_fw([idle] * 1000 + levels, framing=True, output=output, reply=reply)
    assert done is not None
    assert result[:2] == [1, idle]
    assert list(ch.mem.data[FRAME_RES:FRAME_RES+3]) == [1, width, (None, "even", "odd").index(parity)]
    assert ch.host.OUTB == 1
    assert output[-1] == idle
    decoded = Codec(parse(hidden)).decode("receiver", {"tx": output + [idle] * int(4 * FS / rate)})
    assert decoded.ok, decoded.notes
    assert [value for field, value in decoded.events if field == "data"] == [reply]
    assert not any(stream.STARVED for stream in ch.mem.streams)
    assert not any(thread.LATE or thread.OVR for thread in ch.threads)
    assert not (ch.ctrl.CWOVR or ch.ctrl.MEMHAZ or ch.ctrl.CONFLICT or ch.contract_violations)


def test_firmware_rejects_reply_that_does_not_fit_learned_width():
    rate = 460800
    hidden = hidden_text(rate, 7, "even", 2)
    levels = capture(hidden, rand_bytes(32, 7, 7), rate)
    output = []
    ch, _, _, done = run_fw([1] * 1000 + levels, framing=True, output=output, reply=0x80)
    assert done is not None
    assert list(ch.mem.data[FRAME_RES:FRAME_RES+3]) == [1, 7, 1]
    assert ch.host.OUTB == 5
    assert output == []


def test_framing_rejects_a_run_outside_its_range():
    rate = 1_000_000
    hidden = hidden_text(rate)
    words = rand_bytes(32, 8, 7)
    levels = [1] * 1000 + capture(hidden, words[:4], rate)
    levels += [1] * int(18 * FS / rate) + capture(hidden, words[4:], rate)
    ch, _, result, done = run_fw(levels, framing=True)
    assert done is not None
    assert result[0] == 1
    assert ch.host.OUTB == ch.mem.data[FRAME_RES] == 2


@pytest.mark.parametrize(("bit_period", "status"), [(8, 4), (16, 1)])
def test_framing_transmit_period_limit(bit_period, status):
    rate = int(FS // bit_period)
    hidden = hidden_text(rate)
    payload = rand_bytes(32, 8, 7)
    output = []
    ch, _, result, done = run_fw([1] * 1000 + capture(hidden, payload, rate), framing=True, output=output)
    assert done is not None
    assert result[:4] == [1, 1, (32 * bit_period) & 255, (32 * bit_period) >> 8]
    assert ch.mem.data[FRAME_RES] == 1
    assert ch.host.OUTB == status
    if status == 1:
        decoded = Codec(parse(hidden)).decode("receiver", {"tx": output + [1] * (4 * bit_period)})
        assert decoded.ok, decoded.notes
        assert [value for field, value in decoded.events if field == "data"] == payload[:ch.mem.data[FRAME_RES + 3]]
        assert not any(thread.LATE or thread.OVR for thread in ch.threads)
    else:
        assert output == []


@pytest.mark.parametrize("case", CASES, ids=lambda c: "%d-%d%s%d-idle%d" % (c[0], c[1], (c[2] or "none")[0].upper(), c[3], c[4]))
@pytest.mark.parametrize("err,jit", [(0.0, 0), (0.015, 2)])
def test_firmware_matches_reference(case, err, jit):
    rate, bits, parity, stops, idle = case
    lv = capture(hidden_text(rate, bits, parity, stops, idle), rand_bytes(24, bits, 7), rate, err, jit)
    lv = [lv[0]] * 2000 + lv                                    # idle before the traffic
    ch, words, res, done = run_fw(lv)
    assert done is not None, "firmware did not finish"
    ref = stage1(words, PIN)
    status, fidle, tlo, thi, used, mult = res
    flags = (ch.ctrl.CONFLICT, ch.ctrl.MEMHAZ, ch.ctrl.CWOVR, any(t.LATE or t.OVR for t in ch.threads))
    assert flags == (0, 0, 0, False), flags
    assert ch.contract_violations == []
    if not ref.ok:
        assert status == (2 if "too long" in ref.reason else 3), (status, ref.reason)
        return
    assert status == 1, (status, ref)
    assert (fidle, tlo | thi << 8, used, mult) == (ref.idle, ref.TU, ref.used, ref.mult)
    assert (ch.lines[0].INC, ch.lines[0].MOD) == (32, ref.TU)          # learned beat applied by CW
    assert abs((FS * 32 / ref.TU) / (rate * (1 + err)) - 1) < 0.005


def test_record_size_and_time():
    """Instruction counts and firmware run time for one case, recorded for the plan (data/processed/v4_phase0)."""
    rate, bits = 115200, 8
    lv = capture(hidden_text(rate, bits), rand_bytes(24, bits, 7), rate, 0.015, 2)
    lv = [lv[0]] * 2000 + lv
    ch, words, res, done = run_fw(lv)
    n = count_insns(source(PIN, NREC))
    cap_end = None
    out = ROOT / "data" / "processed" / "v4_phase0"
    out.mkdir(parents=True, exist_ok=True)
    (out / "fw_stage1.json").write_text(json.dumps({
        "evidence": "cycle model with v4 additions (SPEC v2 13); not RTL, not hardware",
        "instructions": {"core0": n[0], "core1": n[1], "total": n[0] + n[1], "limit_per_core": 256},
        "records": NREC, "pin": PIN, "case": "115200 8N1, +1.5 % clock, +-2 sample jitter",
        "cycles_load_to_done": done, "result": res}, indent=1), encoding="utf-8")
    assert res[0] == 1
