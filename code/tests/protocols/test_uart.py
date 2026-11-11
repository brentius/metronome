"""End-to-end protocol evidence on the reference model: example programs loaded over pin-level SPI, protocol pins
decoded by the independent checkers (code/tests/checkers/protocols.py).
All numbers here are "verified in simulation against the reference model" (cycle model, not RTL, not hardware)."""
import statistics

import pytest
from driver import CLK, Driver
from protocols import uart_decode, uart_encode
from scenarios import ctrl_reg

BAUD = 115200
CPB = CLK / BAUD            # 520.833 clocks per bit (calculated)
HOSTIN, HOSTOUT, HOSTSTAT = (ctrl_reg(n) for n in ("HOSTIN", "HOSTOUT", "HOSTSTAT"))


def edges(lv):
    return [t for t in range(1, len(lv)) if lv[t] != lv[t - 1]]


def test_blink():
    d = Driver()
    d.load("blink.mas")
    d.idle(4 * 60000 + 2000)    # first commit is 2 beats after RUN (stage then commit), then a toggle per beat
    lv = d.out_bit(8)
    e = edges(lv)
    assert len(e) >= 2, "O8 did not toggle"
    widths = [b - a for a, b in zip(e, e[1:])]
    assert all(abs(w - 60000) <= 1 for w in widths), widths
    print(f"blink: half period {widths} clocks (verified in simulation against the reference model)")


def test_uart_tx():
    d = Driver()
    d.load("uart_tx.mas")
    data = [0x55, 0xA3, 0x00, 0xFF, 0x4B]
    for b in data:
        for _ in range(100):                  # poll HOSTSTAT bit0 (INV) over SPI until clear
            if not d.hoststat() & 1:
                break
            d.idle(300)
        else:
            pytest.fail("HOSTSTAT.INV never cleared")
        d.write(HOSTIN, [b])
        d.idle(int(CPB * 2))                  # let the byte be consumed; polling continues next iteration
    d.idle(int(CPB * 24))   # drain: last byte waits for the previous frame to finish
    lv = d.out_bit(8)
    start = next(t for t, tr in enumerate(d.trace) if t > 100)       # skip reset
    frames = uart_decode(lv[start:], CPB)
    assert [f.value for f in frames] == data
    assert not any(f.framing_error for f in frames)
    # Edge error vs the ideal bit grid anchored at each frame's own start edge, and bit widths between edges.
    seg = lv[start:]
    e = edges(seg)
    errs, widths = [], []
    for f in frames:
        fe = [t for t in e if f.start_cycle <= t < f.start_cycle + 10 * CPB - 1]
        for t in fe:
            errs.append((t - f.start_cycle) - round((t - f.start_cycle) / CPB) * CPB)
        for a, b in zip(fe, fe[1:]):
            widths.append((b - a) / round((b - a) / CPB))
    span = (frames[-1].start_cycle - frames[0].start_cycle) / (len(frames) - 1)
    print(f"uart_tx: {len(frames)} bytes ok; mean bit width {statistics.mean(widths):.3f} clocks (ideal {CPB:.3f}); "
          f"edge error vs ideal grid {min(errs):+.2f}..{max(errs):+.2f} clocks (jitter p-p {max(errs)-min(errs):.2f}); "
          f"frame pitch {span:.1f} clocks (ideal {10 * CPB:.1f}) "
          f"(verified in simulation against the reference model)")
    assert max(abs(x) for x in errs) <= 1.0 + 1e-9
    assert abs(statistics.mean(widths) - CPB) < 0.5
    assert abs(span - 10 * CPB) < 2.0


def rx_frame(d, byte, ppm_err, bad_stop=False):
    cpb = CPB * (1 + ppm_err)
    w = uart_encode(bytes([byte]), cpb, idle_cycles=30)
    if bad_stop:
        a, b = 30 + int(9 * cpb), 30 + int(10 * cpb)
        w[a:b] = [0] * (b - a)
        # the stop bit is held low, so release to idle afterwards (rising edge)
    d.idle(len(w), p8=w)


def read_byte(d):
    st = d.hoststat()
    if not st & 2:
        return None, st
    v = d.read(HOSTOUT)[0]
    d.write(HOSTSTAT, [0x02])
    return v, st


@pytest.mark.parametrize("err", [0.0, +0.02, -0.02])
def test_uart_rx_good(err):
    d = Driver()
    d.load("uart_rx.mas")
    d.idle(100)
    for b in [0xA5, 0x3C, 0x00, 0xFF]:
        rx_frame(d, b, err)
        v, st = read_byte(d)
        assert v == b, f"err {err:+.0%}: sent {b:#x}, got {v}, HOSTSTAT {st:#x}"
        assert not d.chip.flags.F & 4
    print(f"uart_rx: 4 bytes ok at {err:+.0%} baud error (verified in simulation against the reference model)")


def test_uart_rx_bad_stop_then_recovery():
    d = Driver()
    d.load("uart_rx.mas")
    d.idle(100)
    rx_frame(d, 0x5A, 0.0, bad_stop=True)
    v, st = read_byte(d)
    assert v is None, f"bad-stop frame delivered {v:#x}"
    assert d.chip.flags.F & 4, "framing-error flag F2 not set (model-internal flag, not host-visible)"
    d.idle(2000)
    rx_frame(d, 0x96, 0.0)
    v, st = read_byte(d)
    assert v == 0x96
    print("uart_rx: bad stop bit dropped, F2 set (model-internal), next frame ok "
          "(verified in simulation against the reference model)")
