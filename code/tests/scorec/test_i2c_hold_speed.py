"""Raw-pin timing regressions for compiled open-drain I2C targets (60 MHz model)."""
import pytest
from harness import *
from test_i2c import (run_target, run_controller, clean, wand, od, checker_view, ind,
                      rx_records, want_records, PyTarget, expected_events)

@pytest.mark.parametrize('rate', [25e3, 100e3, 400e3])
def test_target_raw_hold(rate):
    ev = [('start',), ('addr', 0x33), ('rw', 1), ('ack', 0),
          ('data', 0xA5), ('more', 0), ('data', 0x5A), ('more', 1), ('stop',)]
    _, chip, bus = run_target(ev, 0x33, b'\xa5\x5a', rate=rate)
    last_fall = None
    holds = []
    for t in range(1, len(bus['scl'])):
        if bus['scl'][t - 1] and not bus['scl'][t]:
            last_fall = t
        if bus['sda'][t] != bus['sda'][t - 1] and not bus['scl'][t]:
            # The controller releases SDA at the low phase midpoint; every change
            # on this read trace must still satisfy the target hold constraint.
            assert last_fall is not None
            holds.append(t - last_fall)
    assert holds and min(holds) >= 18, holds
    clean(chip)


@pytest.mark.parametrize("rate", [25e3, 100e3, 400e3])
def test_target_oe_hold_with_paused_clock(rate):
    """Check target-originated OE transitions, independent decode and stopped SCL.

    Each low and high pause remains below the declared maximum falling-edge
    interval. Stopping high or low must not manufacture another transition.
    """
    my = 0x25
    ev = [('start',), ('addr', my), ('rw', 0), ('ack', 0),
          ('data', 0xA5), ('dack', 0), ('rstart',), ('start',),
          ('addr', my), ('rw', 1), ('ack', 0), ('data', 0xA5),
          ('more', 0), ('data', 0x5A), ('more', 1), ('stop',)]
    period = int(60e6 / rate)
    c = scorec.compile_score(spec_block(1), 'target', 'scl=P0 sda=P1/O1',
                             rate_hz=rate, follow_period=8 * period,
                             params={'my_addr': my})
    chip = new_chip(c)
    chip.backdoor_write(HM['DATA_BASE'], b'\xa5\x5a')
    stream_reg(chip, 0, 'LEN', 2, 2)
    stream_rewind(chip, 0)
    stream_rewind(chip, 1)
    ctl = Codec(parse(spec_block(1)), params={'my_addr': my}, rate=rate).encode_all(
        ev, lead=2 * period, tail=4 * period).drives['controller']
    scl_trace, sda_trace, oe_trace = [], [], []
    uo, out, oe = chip.step(IDLE, 3)
    falls, previous = 0, 1
    for t in range(ctl.n):
        scl = wand(ctl['scl'][t])
        if previous and not scl:
            falls += 1
        # Stretch once after the address and pause once during a read high.
        repeats = 1 + (3 * period if falls in (10, 30) and t > 0 and
                       scl != previous else 0)
        previous = scl
        for _ in range(repeats):
            sda = wand(ctl['sda'][t], od(oe, out, 1))
            scl_trace.append(scl)
            sda_trace.append(sda)
            oe_trace.append((oe >> 1) & 1)
            uo, out, oe = chip.step(IDLE, scl | (sda << 1))
    fall = None
    changes = []
    for t in range(1, len(scl_trace)):
        if scl_trace[t - 1] and not scl_trace[t]:
            fall = t
        if oe_trace[t] != oe_trace[t - 1]:
            assert scl_trace[t] == 0, (t, 'target changes drive while SCL high')
            assert fall is not None and t - fall >= 18, (t, fall)
            changes.append(t)
            # SDA must be stable for >=100 ns before the following rising edge.
            rise = next((r for r in range(t + 1, len(scl_trace)) if scl_trace[r]), None)
            assert rise is not None and rise - t >= 6
    assert len(changes) >= 12
    decoded = ind.i2c_decode(scl_trace, sda_trace)
    assert len(decoded) == 1 and decoded[0].events == checker_view(ev)
    assert rx_records(chip, my) == want_records(ev, my)
    clean(chip)


@pytest.mark.parametrize("rate", [100e3, 400e3])
@pytest.mark.parametrize("nack", [False, True])
def test_controller_hold_tap_dispatch(rate, nack):
    """The capture tap also dispatches staging: sampled data survives stretch/restart."""
    my = 0x31
    reqs = [(my ^ int(nack), 'r', 2), (my, 'w', b'\xa5\x5a')]
    c = scorec.compile_score(spec_block(1), 'controller', 'scl=P0/O0 sda=P1/O1', rate_hz=rate)
    assert 'trigger L0.TAP1' in c.mas
    peer = PyTarget(my, [0x96, 0x0F], stretch=int(3 * 60e6 / rate))
    chip, bus = run_controller(c, reqs, peer, extra=2000)
    want = expected_events(reqs, my, peer.reads)
    assert ind.i2c_decode(bus['scl'], bus['sda'])[0].events == checker_view(want)
    assert chip.host.OUTV and chip.host.OUTB == int(nack)
    clean(chip)
