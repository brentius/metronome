"""Program and score mutation testing: do the independent checkers have teeth?

RTL mutants are covered elsewhere (wiki/VERIFICATION.md 3).  Here the *inputs* to the chip are mutated:

1. Score mutants: a plausible mistake in the protocol description (wrong bit order, wrong field width, wrong rate,
   missing stop bit, wrong preamble).  The mutant score is compiled by the real compiler; the reference codec of the
   ORIGINAL score must reject or mis-decode what the mutant chip sends.  Every mutant must be killed.
2. Image mutants: one bit flipped in the compiled host image (program words and configuration).  Some flips are
   equivalent (unused fields, don't-care bits), so the kill rate is recorded, not required to be 100%; survivors are
   listed in the result file for inspection.

Evidence class: verified in simulation (v2 cycle-level model plus reference codec).
"""
import json
import random
import zlib

import pytest
from harness import *

from test_uart import run_receiver, run_sender

UART_SCORE_MUTANTS = [
    ("msb first", "bits lsb first", "bits msb first"),
    ("7-bit data", "data:u8", "data:u7"),
    ("half rate", "clock 115200 Hz", "clock 57600 Hz"),
    ("4% fast", "clock 115200 Hz", "clock 119808 Hz"),
    ("start bit high", "bit(0)                     # start bit", "bit(1)                     # start bit"),
]


def uart_ok(trace, data):
    r = Codec(parse(spec_block(0))).decode("receiver", {"tx": trace})
    return r.ok and r.events == [("data", b) for b in data]


@pytest.mark.parametrize("name,old,new", UART_SCORE_MUTANTS, ids=[m[0] for m in UART_SCORE_MUTANTS])
def test_uart_score_mutant_sender_is_killed(name, old, new):
    src = spec_block(0)
    assert old in src
    data = bytes([0x35, 0xC6, 0x0F])
    _, nominal = run_sender(scorec.compile_score(src, "sender", "tx=O8"), data)
    assert uart_ok(nominal, data)                                   # the checker accepts the real thing
    _, mut = run_sender(scorec.compile_score(src.replace(old, new), "sender", "tx=O8"), data)
    assert not uart_ok(mut, data), f"score mutant '{name}' survived"


# "4% fast" is an equivalent mutant on the receiver side: a UART receiver resynchronised by every start bit decodes a
# 4% rate error correctly (the sampling point drifts under half a bit over 10 bits), so it is not in this list.
RX_MUTANTS = [m for m in UART_SCORE_MUTANTS[:4] if m[0] != "4% fast"]


@pytest.mark.parametrize("name,old,new", RX_MUTANTS, ids=[m[0] for m in RX_MUTANTS])
def test_uart_score_mutant_receiver_is_killed(name, old, new):
    data = bytes([0x35, 0xC6, 0x0F])
    enc = Codec(parse(spec_block(0))).encode_all([("data", b) for b in data])
    chip, statuses = run_receiver(scorec.compile_score(spec_block(0).replace(old, new), "receiver", "tx=P5"),
                                  enc.bus["tx"])
    got = bytes(chip.mem.data[0x400:0x400 + chip.mem.streams[0].POS])
    assert got != data or any(statuses), f"score mutant '{name}' survived"


ETH_SCORE_MUTANTS = [
    ("preamble byte", "const 55 55 55 55 55 55 55 D5", "const 55 55 55 55 55 55 55 D7"),
    ("inverted Manchester", 'bit(d)   td "!dd"', 'bit(d)   td "d!d"'),
    ("half rate", "clock 10 MHz", "clock 5 MHz"),
]
# Killed by the compiler before any waveform exists (also a kill: the mistake never reaches a pin).
ETH_COMPILE_REJECTED = [
    ("msb first", "bits lsb first", "bits msb first", "E-UNSUPPORTED"),    # crc32 refin/refout must match bit order
    ("double rate", "clock 10 MHz", "clock 20 MHz", "E-TIME"),             # 3 cycles per beat: symbol would be LATE
]


def eth_trace(src, body):
    c = scorec.compile_score(src, "sender", "td=O0 tdn=O1", skip_periodic=True)
    chip = new_chip(c)
    for _ in range(20):
        chip.step(IDLE, 0)
    send_frame_go(chip, body)
    return [chip.step(IDLE, 0)[1] & 1 for _ in range((64 + 8 * len(body) + 32 + 2 + 110) * 6 + 300)]


def eth_ok(trace, body):
    r = Codec(parse(spec_block(3))).decode("receiver", {"td": trace})
    if not r.ok:
        return False
    d = dict((e[0], e[1] if len(e) > 1 else None) for e in r.events)
    return d.get("body") == body and d.get("fcs") == zlib.crc32(body)


@pytest.mark.parametrize("name,old,new", ETH_SCORE_MUTANTS, ids=[m[0] for m in ETH_SCORE_MUTANTS])
def test_ethernet_score_mutant_sender_is_killed(name, old, new):
    src = spec_block(3)
    assert old in src
    body = bytes(range(0x30, 0x30 + 12))
    assert eth_ok(eth_trace(src, body), body)
    assert not eth_ok(eth_trace(src.replace(old, new), body), body), f"score mutant '{name}' survived"


@pytest.mark.parametrize("name,old,new,code", ETH_COMPILE_REJECTED, ids=[m[0] for m in ETH_COMPILE_REJECTED])
def test_ethernet_score_mutant_rejected_by_compiler(name, old, new, code):
    from scorec.plan import CompileError
    with pytest.raises(CompileError) as e:
        scorec.compile_score(spec_block(3).replace(old, new), "sender", "td=O0 tdn=O1", skip_periodic=True)
    assert e.value.code == code


def test_uart_sender_image_bit_flips(tmp_path):
    """One bit flipped in the compiled image, 80 sampled mutants.  Killed = the checker rejects the output, or the
    chip raises LATE/OVR/CONFLICT, or nothing at all comes out.  The rate and the survivors are written to
    data/processed.  A survivor whose pins match the unmutated run on every cycle is equivalent (no observer could
    tell); the test requires every NON-equivalent mutant to be killed, i.e. the checker has no gap here."""
    c = scorec.compile_score(spec_block(0), "sender", "tx=O8")
    writes = list(host_writes(c.program))
    bits = [(i, j) for i, (_, d, _) in enumerate(writes) for j in range(len(d) * 8)]
    rng = random.Random(1234)
    sample = rng.sample(bits, 80)
    data = bytes([0x35, 0xC6])
    ncyc = int(len(data) * 10 * 520.9 + 3000)

    def run(writes_):
        chip = Chip()
        for addr, d, _ in writes_:
            chip.backdoor_write(addr, d)
        pending, tr = list(data), []
        for _ in range(ncyc):
            if pending and chip.host.INV == 0:
                hostin(chip, pending.pop(0))
            uo, uio, oe = chip.step(IDLE, 0)
            tr.append((uo, uio, oe))
        return chip, tr

    _, nominal = run(writes)
    killed, survivors, equivalent = 0, [], []
    for i, j in sample:
        mw = list(writes)
        addr, d, name = mw[i]
        d = bytearray(d)
        d[j // 8] ^= 1 << (j % 8)
        mw[i] = (addr, bytes(d), name)
        chip, pins = run(mw)
        flags = any(t.LATE or t.OVR for t in chip.threads) or chip.ctrl.CONFLICT
        where = f"{name} byte {j // 8} bit {j % 8}"
        if flags or not uart_ok([(p[0] >> 2) & 1 for p in pins], data):
            killed += 1
        elif pins == nominal:
            equivalent.append(where)          # every output pin identical on every cycle: no observer can tell
        else:
            survivors.append(where)           # the pins differ but the checker accepts: a checker gap
    out = {"what": "UART sender image single-bit-flip mutants, v2 cycle model + reference codec",
           "sampled": len(sample), "population_bits": len(bits), "seed": 1234, "cycles": ncyc, "killed": killed,
           "equivalent_at_pins": len(equivalent), "survivors_pins_differ": survivors,
           "equivalent": equivalent,
           "note": "equivalent = uo_out/uio_out/uio_oe identical to the unmutated image on every cycle of the run "
                   "(unused program words, don't-care fields, settings this role never reads)"}
    dst = ROOT / "data" / "processed" / "v3_rival" / "image_mutants_uart.json"
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(json.dumps(out, indent=1), encoding="utf-8")
    assert not survivors, out
