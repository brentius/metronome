"""Mailbox fields of different widths in one Score sender frame."""
import pytest
from harness import *


def mailbox_score(order):
    return f'''protocol mailbox_widths
roles sender, receiver
wire tx out push-pull idle high by sender
clock 1 MHz
  sender: generated
  receiver: started by tx fall
  tolerance 3%
symbols
  bit(d) tx "d" sample tx at 50%
bits {order} first
grammar
  line = frame*
  frame = bit(0) narrow:u5 wide:u8 bit(1) gap 0 beats
'''


def run_mailbox_frames(text, values, frames=3, rate=1e6):
    compiled = scorec.compile_score(text, "sender", "tx=O8", rate_hz=rate)
    chip = new_chip(compiled)
    pending = list(values)
    trace = []
    for _ in range(int(frames * 20 * 60e6 / rate) + 500):
        if pending and chip.host.INV == 0:
            hostin(chip, pending.pop(0))
        uo, _, _ = chip.step(IDLE, 0)
        trace.append((uo >> 2) & 1)
    assert not pending, f"mailbox input was not consumed: {pending}"
    assert all(t.LATE == 0 and t.OVR == 0 for t in chip.threads)
    assert chip.ctrl.CONFLICT == 0
    assert not any(s.STARVED for s in chip.mem.streams)
    return compiled, trace


@pytest.mark.parametrize('order,rate', [('lsb', 7.5e6), ('msb', 6e6)])
def test_mailbox_configuration_needs_no_idle_instructions(order, rate):
    text = mailbox_score(order)
    pairs = [(0x15, 0xA6), (0x03, 0x5B), (0x1C, 0xE1)]
    _, trace = run_mailbox_frames(text, [v for p in pairs for v in p], rate=rate)
    result = Codec(parse(text), rate=rate).decode('receiver', {'tx': trace})
    assert result.ok, result.notes
    assert [e for e in result.events if e[0] in ('narrow', 'wide')] == [
        e for a,b in pairs for e in (('narrow',a),('wide',b))]


def test_lsb_mailbox_fields_keep_each_width_across_repeated_frames():
    text = mailbox_score("lsb")
    pairs = [(0x15, 0xA6), (0x03, 0x5B), (0x1C, 0xE1)]
    values = [v for pair in pairs for v in pair]
    compiled, trace = run_mailbox_frames(text, values)
    decoded = Codec(parse(text)).decode("receiver", {"tx": trace})
    assert decoded.ok, decoded.notes
    assert [e for e in decoded.events if e[0] in ("narrow", "wide")] == [
        event for a, b in pairs for event in (("narrow", a), ("wide", b))
    ]
    assert compiled.host["mailbox_in"] == ["narrow", "wide"]


def test_msb_mailbox_narrow_field_alignment_and_mixed_widths():
    text = mailbox_score("msb")
    pairs = [(0x15, 0xA6), (0x03, 0x5B), (0x1C, 0xE1)]
    values = [v for pair in pairs for v in pair]
    compiled, trace = run_mailbox_frames(text, values)
    decoded = Codec(parse(text)).decode("receiver", {"tx": trace})
    assert decoded.ok, decoded.notes
    assert [e for e in decoded.events if e[0] in ("narrow", "wide")] == [
        event for a, b in pairs for event in (("narrow", a), ("wide", b))
    ]
    assert compiled.host["mailbox_in"] == ["narrow", "wide"]


def test_wide_first_mailbox_restores_width_on_frame_loop():
    text = mailbox_score('lsb').replace('narrow:u5 wide:u8', 'wide:u8 narrow:u5')
    pairs = [(0xa6, 0x15), (0x5b, 3), (0xe1, 0x1c)]
    _, trace = run_mailbox_frames(text, [v for pair in pairs for v in pair])
    result = Codec(parse(text)).decode('receiver', {'tx':trace})
    assert result.ok, result.notes
    assert [e for e in result.events if e[0] in ('narrow','wide')] == [
        e for a,b in pairs for e in (('wide',a),('narrow',b))]
