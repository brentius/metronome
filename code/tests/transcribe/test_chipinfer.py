"""Integer reference of on-chip UART inference (transcribe/chipinfer.py) against the host tool (infer.py) on the
transcription corpus. Evidence level: model level (reference codec waveforms), nothing on RTL or hardware."""
import pytest

from test_transcribe import CASES, FS, capture, hidden_text, rand_bytes
from transcribe import transcribe
from transcribe.chipinfer import ChipInferenceError, div, infer, records_from_levels


@pytest.mark.parametrize("case", CASES, ids=lambda c: "%d-%d%s%d-idle%d" % (c[0], c[1], (c[2] or "none")[0].upper(), c[3], c[4]))
@pytest.mark.parametrize("err,jit", [(0.0, 0), (0.015, 2), (-0.015, 2)])
def test_matches_host_tool(case, err, jit):
    rate, bits, parity, stops, idle = case
    lv = capture(hidden_text(rate, bits, parity, stops, idle), rand_bytes(24, bits, 7), rate, err, jit)
    h = transcribe(lv, FS).uart
    c = infer(records_from_levels(lv))
    assert (c.data_bits, c.parity, c.stop_bits, c.idle) == (h.data_bits, h.parity, h.stop_bits, h.idle_level)
    assert c.words == h.words
    berr = (FS * c.inc / c.mod) / (rate * (1 + err)) - 1
    assert abs(berr) < 0.005, berr                       # learned beat within 0.5 % of the true rate (host bound)
    assert c.mod <= 0xFFFF and c.inc < c.mod


def test_division_routine():
    for n, d in [(0, 1), (12345678, 77), ((1 << 32) - 1, (1 << 24) - 1), (100, 101)]:
        assert div(n, d) == divmod(n, d)


def test_garbage_and_too_few_edges_fail():
    with pytest.raises(ChipInferenceError):
        infer(records_from_levels([1] * 50 + [0] * 3 + [1] * 50))
    import random
    r = random.Random(3)
    lv, cur = [], 1
    for _ in range(200):
        lv += [cur] * r.randint(4, 400)
        cur ^= 1
    with pytest.raises(ChipInferenceError):
        infer(records_from_levels(lv))


# ---- stage 1 (firmware algorithm) -------------------------------------------------------------------------------
from transcribe.chipinfer import stage1  # noqa: E402

N_REC = 64


def words_from_levels(levels, pin=5, n=N_REC):
    """The capture words S0 would hold for these levels on pin `pin` (DC from the trace start, PIN = level after)."""
    out, last = [], 0
    for i in range(1, len(levels)):
        if levels[i] != levels[i - 1]:
            out.append((min(i - last, (1 << 19) - 1) << 13) | ((levels[i] & 1) << pin))
            last = i
            if len(out) == n:
                break
    return out


@pytest.mark.parametrize("case", CASES, ids=lambda c: "%d-%d%s%d-idle%d" % (c[0], c[1], (c[2] or "none")[0].upper(), c[3], c[4]))
@pytest.mark.parametrize("err,jit", [(0.0, 0), (0.015, 2), (-0.015, 2)])
def test_stage1_bit_time(case, err, jit):
    rate, bits, parity, stops, idle = case
    lv = capture(hidden_text(rate, bits, parity, stops, idle), rand_bytes(24, bits, 7), rate, err, jit)
    s = stage1(words_from_levels(lv), 5)
    if FS / rate >= 2048:
        assert not s.ok and "too long" in s.reason          # stated limit: bit time < 2048 cycles (>= 29.3 kbaud)
        return
    assert s.ok, s.reason
    assert s.idle == idle
    berr = (FS * 32 / s.TU) / (rate * (1 + err)) - 1     # learned beat INC = 32, MOD = TU
    assert abs(berr) < 0.005, berr
