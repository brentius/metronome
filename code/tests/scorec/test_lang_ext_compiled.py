"""Language extensions (SPEC_V2_SCORE.md part A 18) on compiled images in the v2 cycle-level model:
the timing certificate of real pin traces (18.1), a layered protocol over a compiled carrier (18.2), and how the
compiler treats enums and state (18.3)."""
import random
from pathlib import Path

import pytest
from harness import *
from test_i2c import PyTarget, run_controller, run_target

from scorec import CompileError, certify, compile_layered
from score.layer import LayeredCodec

MODBUS = (ROOT / "code/score/examples/modbus_rtu.score").read_text(encoding="utf-8")

UART_C = """
constrain
  tBIT     tx change -> tx change    >= 8.5 us
  tSTART   tx fall -> tx rise        >= 8.5 us
"""

I2C_C = """
constrain
  fSCL     scl rise -> scl rise                  >= 10 us
  tLOW     scl fall -> scl rise                  >= 4.7 us
  tHIGH    scl rise -> scl fall                  >= 4 us
  tSU_DAT  sda change when scl low -> scl rise   >= 250 ns
  tHD_DAT  scl fall -> sda change when scl low   >= 0 ns
  tHD_DEV  scl fall -> sda change when scl low   >= 300 ns
  tHD_STA  start_c -> scl fall                   >= 4 us
  tSU_STA  scl rise -> start_c                   >= 4.7 us
"""


def by_name(lines):
    return {ln.name: ln for ln in lines}


def test_uart_sender_certificate_as_written_and_as_compiled():
    src = spec_block(0) + UART_C
    data = bytes([0x55, 0x00, 0xFF, 0xA5, 0x01])
    c = scorec.compile_score(spec_block(0), "sender", "tx=O8")
    chip = new_chip(c)
    pending, trace = list(data), []
    for _ in range(int(len(data) * 10 * 520.9 + 3000)):
        if pending and chip.host.INV == 0:
            hostin(chip, pending.pop(0))
        uo, uio, oe = chip.step(IDLE, 0)
        trace.append((uo >> 2) & 1)
    w = by_name(certify.written(src, [("data", b) for b in data]))
    k = by_name(certify.compiled(src, {"tx": trace}))
    print(certify.report(src, written_lines=list(w.values()), compiled_lines=list(k.values())))
    for name in ("tBIT", "tSTART"):
        assert w[name].status == "PASS" and k[name].status == "PASS"
    # one bit is 520.83 cycles: the chip's edges are 520 or 521 cycles apart (one cycle of quantisation)
    assert 520 * 1e9 / 60e6 - 1 <= k["tBIT"].worst_ns <= 521 * 1e9 / 60e6 + 1
    assert k["tBIT"].pairs >= 20


def test_i2c_controller_certificate_meets_start_timing():
    """The compiled controller places START and the two-beat repeated START exactly as the score's wave strings say
    (spec 16.2, O7 closed): tHD;STA 5.0 us and tSU;STA 10 us at 100 kHz, both measured on the chip's own trace."""
    src = spec_block(1) + I2C_C
    my = 0x2A
    peer = PyTarget(my, [0x11, 0x22])
    chip, bus = run_controller(scorec.compile_score(spec_block(1), "controller", "scl=P0/O0 sda=P1/O1"),
                               [(my, "w", b"\x81\x7e"), (my, "r", 2)], peer)
    k = by_name(certify.compiled(src, bus))
    print(certify.report(src, compiled_lines=list(k.values())))
    for name in ("fSCL", "tLOW", "tHIGH", "tSU_DAT", "tHD_DAT"):
        assert k[name].status == "PASS", k[name]
    # tHD_DEV is not asserted here: on this bus the Python test peer (PyTarget) drives its ACK one cycle after SCL
    # falls, so the worst hold belongs to the peer model, not to the chip (the controller changes SDA mid-low)
    one = 1e9 / 60e6
    assert k["tHD_STA"].status == "PASS" and k["tHD_STA"].pairs == 2
    assert abs(k["tHD_STA"].worst_ns - 5000) <= 2 * one
    assert k["tSU_STA"].status == "PASS" and abs(k["tSU_STA"].worst_ns - 10_000) <= 2 * one


def test_i2c_target_certificate_meets_device_hold():
    """The compiled FOLLOW target retains its previous drive for at least 300 ns."""
    my = 0x33
    ev = [("start",), ("addr", my), ("rw", 1), ("ack", 0), ("data", 0xA5), ("more", 0), ("data", 0x5A), ("more", 1),
          ("stop",)]
    c, chip, bus = run_target(ev, my, bytes([0xA5, 0x5A]))
    src = spec_block(1) + I2C_C
    k = by_name(certify.compiled(src, bus))
    print(certify.report(src, compiled_lines=list(k.values())))
    assert k["tHD_DAT"].status == "PASS"
    assert k["tHD_DEV"].status == "PASS" and k["tHD_DEV"].worst_ns >= 300
    assert k["tSU_DAT"].status == "PASS"


def run_layered_sender(lc_compiled, events, chars_cycles):
    """Host side of a layered sender: push each byte run, then hold the line idle for the upper gap."""
    chip = new_chip(lc_compiled.lower)
    trace = []
    for run, gap in lc_compiled.host_runs(events):
        pending = list(run)
        while pending or chip.host.INV:
            if pending and chip.host.INV == 0:
                hostin(chip, pending.pop(0))
            uo, uio, oe = chip.step(IDLE, 0)
            trace.append((uo >> 2) & 1)
        idle = int(11 * 521) + (int(gap.value * chars_cycles) if gap is not None else 0)
        for _ in range(idle):
            uo, uio, oe = chip.step(IDLE, 0)
            trace.append((uo >> 2) & 1)
    return chip, trace


@pytest.mark.parametrize("seed", range(3))
def test_modbus_over_compiled_uart_sender(seed):
    rng = random.Random(seed)
    ev = []
    for _ in range(rng.randrange(1, 4)):
        slave = rng.randrange(1, 248)
        kind = rng.choice(["READ_HOLDING", "WRITE_SINGLE", "WRITE_MULTIPLE"])
        ev += [("slave", slave), ("func", kind)]
        if kind == "READ_HOLDING":
            ev += [("start", rng.randrange(65536)), ("count", rng.randrange(1, 126))]
        elif kind == "WRITE_SINGLE":
            ev += [("reg", rng.randrange(65536)), ("value", rng.randrange(65536))]
        else:
            n = rng.randrange(1, 5)
            ev += [("start", rng.randrange(65536)), ("count", n), ("regs", bytes(rng.randrange(256) for _ in range(2 * n)))]
    lcomp = compile_layered(MODBUS, "master", "tx=O8")
    assert lcomp.lower_role == "sender" and lcomp.payload == "data"
    codec = LayeredCodec(parse(MODBUS))
    chip, trace = run_layered_sender(lcomp, ev, codec.char_cycles)
    out, ok, notes = codec.decode("slave", {"tx": trace})
    assert ok, notes
    members = codec.score.enums["fn"].members
    want = []
    for k, v in ev:
        want.append((k, members[v] if isinstance(v, str) else v))
        if k == "count" and want[-3] == ("func", 16):
            want.append(("nbytes", 2 * v))
    assert out == want
    assert all(t.LATE == 0 and t.OVR == 0 for t in chip.threads) and chip.ctrl.CONFLICT == 0


def test_layered_score_is_refused_by_compile_score():
    with pytest.raises(CompileError) as e:
        scorec.compile_score(MODBUS, "master", "tx=O8")
    assert e.value.code == "E-LAYER"


ENUM_UART = spec_block(0).replace("bits lsb first", """bits lsb first

enum cmd : u8
  PING = 0x50
  ECHO = 0x45""").replace("data:u8", "data:cmd")


def test_enum_typed_field_compiles_like_its_integer_type():
    a = scorec.compile_score(ENUM_UART, "sender", "tx=O8")
    b = scorec.compile_score(spec_block(0), "sender", "tx=O8")
    assert a.ok and a.mas.split("\n", 1)[1] == b.mas.split("\n", 1)[1]


def test_state_update_is_refused_by_the_compiler_not_miscompiled():
    src = spec_block(0).replace("bits lsb first", "bits lsb first\n\nstate\n  n : u8 = 0").replace(
        "gap 0 beats", "gap 0 beats\n           n <- n + 1")
    with pytest.raises(CompileError) as e:
        scorec.compile_score(src, "sender", "tx=O8")
    assert e.value.code == "E-UNSUPPORTED" and "state update" in str(e.value)
