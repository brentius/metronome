"""Spot checks of the UART shmoo (code/host2/sweep/uart_shmoo.py): the compiled receiver at a 50% sample point passes
inside the calculated tolerance window and fails outside it (full sweep: data/processed/v3_rival/uart_shmoo.json)."""
import sys

import pytest
from harness import ROOT

sys.path.insert(0, str(ROOT / "code" / "host2" / "sweep"))
import uart_shmoo as sh  # noqa: E402


@pytest.mark.parametrize("err,ok", [(-0.04, True), (0.04, True), (-0.065, False), (0.065, False)])
def test_uart_receiver_tolerance_edges(err, ok):
    assert sh.passes(50, err) is ok


def test_late_sample_point_shifts_the_window():
    assert sh.passes(80, -0.07) and not sh.passes(80, 0.03)
