"""Mailbox-landing phase sweeps for senders with an idle loop (root cause of the 'HOSTIN drop', V3 track D finding).

The old idle loop sampled HOST.INV twice ("stage the first symbol if INV", then "jump if INV").  A byte landing between
the two samples was consumed by the next state without the first symbol being staged, so the frame was lost (UART at
10 Mbaud: one landing phase in 12 cycles; 5 Mbaud: one in 24).  The loop now makes one decision from one sample.
These tests land the byte at every phase of the idle loop."""
import pytest
from harness import *

from test_i2c import CTL_BIND, PyTarget, od, wand

UART = parse(spec_block(0))


def uart_byte_ok(compiled, rate, delay, byte=0xA5):
    chip = new_chip(compiled)
    for _ in range(100 + delay):
        chip.step(IDLE, 0)
    hostin(chip, byte)
    P = 60e6 / rate
    tr = []
    for _ in range(int(14 * P) + 60):
        uo, _, _ = chip.step(IDLE, 0)
        tr.append((uo >> 2) & 1)
    r = Codec(UART, rate=rate).decode("receiver", {"tx": tr})
    return r.ok and r.events == [("data", byte)]


@pytest.mark.parametrize("rate,stride", [(10_000_000, 1), (6_000_000, 1), (5_000_000, 1), (3_000_000, 1),
                                         (1_000_000, 1), (115_200, 7)])
def test_uart_tx_accepts_a_byte_at_every_idle_loop_phase(rate, stride):
    c = scorec.compile_score(spec_block(0), "sender", "tx=O8", rate_hz=rate)
    loop = int(2 * 60e6 / rate) + 6              # two idle beats, plus margin
    bad = [d for d in range(0, loop, stride) if not uart_byte_ok(c, rate, d)]
    assert bad == [], f"{rate} baud: byte lost at HOSTIN phases {bad}"


def test_i2c_controller_go_byte_at_every_idle_loop_phase():
    c = scorec.compile_score(spec_block(1), "controller", CTL_BIND)
    from scorec.bus import controller_tx
    bad = []
    for d in range(0, 1200, 9):                  # two idle beats of 600 cycles; stride 9 is coprime with them
        chip = new_chip(c)
        for _ in range(20):
            chip.step(IDLE, 0b11)
        tx = controller_tx([(0x42, "w", b"\x01")])
        chip.backdoor_write(HM["DATA_BASE"], tx)
        stream_reg(chip, 0, "LEN", len(tx), 2)
        stream_rewind(chip, 0)
        stream_rewind(chip, 1)
        for _ in range(40 + d):
            chip.step(IDLE, 0b11)
        hostin(chip, 1)
        peer, started = PyTarget(0x42, []), False
        uo, uio, oe = chip.step(IDLE, 0b11)
        for _ in range(2600):
            ps, pd = peer.scl, peer.sda
            scl, sda = wand(od(oe, uio, 0), ps), wand(od(oe, uio, 1), pd)
            if scl and not sda:
                started = True
                break
            uo, uio, oe = chip.step(IDLE, scl | (sda << 1))
            peer.step(scl, sda)
        if not started:
            bad.append(d)
    assert bad == [], f"go byte lost at phases {bad[:20]}"


# ---- flatten / coding diagnostics (V3 track C follow-ups) -------------------------------------------------------------
def test_repeat_copies_steps_so_merge_does_not_mutate_the_repeats():
    from scorec.flatten import frame_shape, merge_syms
    src = spec_block(0).replace("bit(1)                     # stop bit", "bit(1) x 3                 # stop bit")
    src = src.replace("bit(1) x 3 ", "bit(1) x 3")
    from score import parse as _p
    sc = _p(src)
    shape = frame_shape(sc)
    stops = [s for s in shape.frame if s.kind == "sym" and s.args == (1,)]
    assert [s.count for s in stops] == [3]
    again = frame_shape(sc)                                  # flattening twice must not carry mutated counts
    assert [s.count for s in again.frame if s.kind == "sym" and s.args == (1,)] == [3]


def test_stuff_and_differential_coding_are_refused_not_ignored():
    from scorec.plan import CompileError
    for coding in ("bits lsb first, differential on 0", "bits lsb first, stuff 0 after 5 ones"):
        src = spec_block(0).replace("bits lsb first", coding)
        with pytest.raises(CompileError) as e:
            scorec.compile_score(src, "sender", "tx=O8")
        assert e.value.code == "E-UNSUPPORTED"
