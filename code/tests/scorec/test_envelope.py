"""Cross-check a calculated 8N1 timing bound against the archived model sweep."""

import json
from fractions import Fraction

import pytest

from harness import ROOT
from scorec.envelope import uart8n1_envelope
from test_sweep import sh


def test_bound_tracks_programmed_tap_and_rearm():
    compiled = sh.receiver(50)
    envelope = uart8n1_envelope(compiled)
    assert envelope.sample_cycles == tuple(27 + 60 * index for index in range(10))
    assert envelope.rearm_cycles == compiled.check_report.threads[0].resp_last
    envelope.require(Fraction(4, 100))
    with pytest.raises(ValueError, match="rate error"):
        envelope.require(Fraction(5, 100))


def test_archived_model_sweep_covers_calculated_envelope():
    sweep = json.loads((ROOT / "data/processed/v3_rival/uart_shmoo.json").read_text(encoding="utf-8"))
    for sample in sweep["samples_pct"]:
        envelope = uart8n1_envelope(sh.receiver(sample))
        guaranteed = [ok for rate, ok in zip(sweep["errors"], sweep["grid"][str(sample)])
                      if envelope.low_error < rate < envelope.high_error]
        assert guaranteed and all(guaranteed), (sample, envelope)


def test_receiver_with_insufficient_rearm_margin_is_rejected():
    compiled = sh.receiver(80)
    # Timing checker latency bound plus synchronizer/rounding guard leaves
    # less margin than the requested 3% on contiguous back-to-back frames.
    envelope = uart8n1_envelope(compiled)
    with pytest.raises(ValueError, match="rate error"):
        envelope.require(Fraction(3, 100))
    assert uart8n1_envelope(compiled, idle_bits=1).high_error > envelope.high_error
