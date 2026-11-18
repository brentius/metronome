"""Rate acceptance must not silently disable the protocol's dispatch event."""
import pytest

from harness import spec_block, scorec
from scorec.plan import CompileError


def test_i2c_quantized_boundary_tap_is_rejected():
    # At a two-cycle beat, the 75% dispatch tap rounds to MOD and never fires.
    # The old compiler returned a program with a warning instead of a protocol.
    with pytest.raises(CompileError, match='tap|phase|quantiz|timing'):
        scorec.compile_score(spec_block(1), 'controller', 'scl=P0/O0 sda=P1/O1', rate_hz=30e6)


@pytest.mark.parametrize('rate',[10e6,15e6,20e6,25e6,30e6,40e6])
def test_i2c_impossible_rates_cannot_compile_an_inactive_dispatcher(rate):
    with pytest.raises(CompileError):
        scorec.compile_score(spec_block(1), 'controller', 'scl=P0/O0 sda=P1/O1', rate_hz=rate)


def test_rate_report_does_not_advertise_a_burst_bound_as_a_supported_maximum():
    compiled=scorec.compile_score(spec_block(1), 'controller', 'scl=P0/O0 sda=P1/O1', rate_hz=1e6)
    assert 'burst-only' in compiled.report
    assert 'fastest generated rate that fits' not in compiled.report
    assert 'not a validated maximum' in compiled.report
