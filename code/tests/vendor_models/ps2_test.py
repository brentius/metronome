"""Blind challenge: PS/2 keyboard receive, from the spec only, against an independent device peer.

Two controller programs for the same protocol, both written from the same public specification:
  * `ps2_keyboard_rx.mas` (assembly) follows the device's own clock edge by edge and frames 11 bits with its
    own bit counter;
  * `ps2_keyboard.score` (Score, compiled here by scorec) is the compiler's fixed-rate receive template: it
    samples at 50% of a declared 16.667 kHz beat, exactly like the UART receive template.

The peer (ps2_keyboard_peer.v) is written from the IBM PS/2 interface specification, not from either program:
11 bits per frame (start 0, 8 data LSB first, odd parity, stop 1), device-generated clock at 16.7 kHz, data
valid on the falling edge (spec: "Keyboard-to-System Communication"; mirrored text
https://www.burtonsys.com/ps2_chapweske.htm, "Communication: Device-to-Host").  The testbench also records the
data level at every falling clock edge, so the chip's receive log can be compared with the wire bit for bit.
"""
import sys
from pathlib import Path

import cocotb

sys.path.insert(0, str(Path(__file__).resolve().parent))
from vendor_common import Bench, HM, srt_addr, stream_addr   # noqa: E402

ASM_PROGRAM = "code/host2/examples/vendor/ps2_keyboard_rx.mas"
SCORE_PROGRAM = "code/tests/vendor_models/ps2_keyboard.score"
SCORE_BIND = "clk=P0 data=P1"
ASM_RX_BASE, ASM_RX_STREAM = 0x100, 1
SCORE_RX_BASE, SCORE_RX_STREAM = 0x400, 0
FRAME_BITS = 11
SCORE_FRAME_BITS = 9                 # the score captures data:u8 and parity:bit; start/stop are constants
BIT_NS = 60_000                      # 16.7 kHz, the fast end of the PS/2 range
FRAME_NS = FRAME_BITS * BIT_NS + 150_000                 # one frame plus an inter-frame gap
FRAME_CYCLES = int(round(FRAME_NS / 16.666))             # ... in 60 MHz chip cycles
FRAMES = [(0x1C, False), (0x5A, False), (0xE0, True)]    # 'a', 'Z', and a frame with a bad parity bit


def root() -> Path:
    return Path(__file__).resolve().parents[3]


def assemble():
    from metronome2_tools import asm
    return asm.assemble_text((root() / ASM_PROGRAM).read_text(encoding="utf-8"), "ps2_keyboard_rx")


def compile_score():
    import scorec
    return scorec.compile_score((root() / SCORE_PROGRAM).read_text(encoding="utf-8"), "host", SCORE_BIND,
                                rate_hz=16_667)


def decode_frames(bits, n):
    """Independent decode of n 11-bit device-to-host frames: start, 8 data bits LSB first, odd parity, stop."""
    out = []
    for k in range(n):
        f = bits[k * FRAME_BITS:(k + 1) * FRAME_BITS]
        assert len(f) == FRAME_BITS, f"frame {k}: only {len(f)} bits logged"
        start, data, par, stop = f[0], f[1:9], f[9], f[10]
        byte = sum(b << i for i, b in enumerate(data))
        out.append({"start": start, "byte": byte, "parity_ok": (sum(f[1:10]) % 2) == 1, "stop": stop})
    return out


def expect(decoded, sent, what: str):
    assert decoded["start"] == 0, f"{what}: start bit {decoded['start']}"
    assert decoded["stop"] == 1, f"{what}: stop bit {decoded['stop']}"
    assert decoded["byte"] == sent, f"{what}: byte {decoded['byte']:#04x}, expected {sent:#04x}"


async def send_frames(b):
    for code, bad in FRAMES:
        b.dut.ps2_din.value = code
        b.dut.ps2_bad_parity.value = 1 if bad else 0
        await b.pulse("ps2_go", settle=0)
        await b.wait(FRAME_CYCLES)


def wire_bits(dut):
    """The data level at every falling clock edge, as recorded by the testbench."""
    return [int(dut.seen_bits.value.to_unsigned() >> i) & 1 for i in range(int(dut.seen_n.value))]


def check_no_faults(dut, b):
    assert int(dut.bus_fault.value) == 0, "the chip drove a '1' onto an open-drain PS/2 wire"


@cocotb.test()
async def ps2_assembly_receiver(dut):
    """The hand-written assembly receiver: follows the device clock, logs raw bits, reports the byte."""
    b = Bench(dut)
    await b.start()
    await b.load(assemble())
    await b.write(stream_addr(ASM_RX_STREAM, "LEN"), [64, 0])
    await b.write(srt_addr(ASM_RX_STREAM, "CTL"), [1])
    await b.idle(20)
    await send_frames(b)

    pos = await b.read(srt_addr(ASM_RX_STREAM, "POSL"), 3)
    assert not (pos[1] & 0x80), "receive stream STARVED"
    # The last frame leaves a partial byte in the stream's shift register; a flush commits it to data RAM.
    await b.write(srt_addr(ASM_RX_STREAM, "CTL"), [0x02])
    await b.idle(20)
    pos = await b.read(srt_addr(ASM_RX_STREAM, "POSL"), 3)
    nbytes, bidx = pos[0] | ((pos[1] & 0x0F) << 8), pos[1] >> 4
    nbits = nbytes * 8 + bidx
    assert nbits >= len(FRAMES) * FRAME_BITS, f"only {nbits} bits logged"

    data = bytes(await b.read(HM["DATA_BASE"] + ASM_RX_BASE, nbytes + 1))
    bits = [(data[i >> 3] >> (i & 7)) & 1 for i in range(nbits)]
    wire = wire_bits(dut)
    assert bits[:len(wire)] == wire, f"logged {''.join(map(str, bits))}, wire {''.join(map(str, wire))}"
    assert not any(bits[len(wire):]), "padding bits after the last frame are not zero"
    frames = decode_frames(bits, 3)
    for k, f in enumerate(frames):
        dut._log.info(f"asm frame {k}: start={f['start']} byte={f['byte']:#04x} parity_ok={f['parity_ok']} "
                      f"stop={f['stop']}")
    expect(frames[0], FRAMES[0][0], "frame 0")
    expect(frames[1], FRAMES[1][0], "frame 1")
    assert frames[0]["parity_ok"] and frames[1]["parity_ok"], "good frames failed the odd-parity check"

    try:                                                   # negative control: the checker rejects a wrong byte
        expect(frames[1], FRAMES[0][0], "deliberately wrong expectation")
    except AssertionError:
        pass
    else:                                                  # pragma: no cover
        raise AssertionError("the checker accepted a wrong byte: the positive control is vacuous")

    # Negative control: the injected parity error is caught by the host decode from the raw log (the program
    # itself does not check parity - recorded in the README).
    expect(frames[2], FRAMES[2][0], "frame 2 (bad parity)")
    assert not frames[2]["parity_ok"], "the host parity check did not catch the injected parity error"

    out = await b.read_u8(HM["CTRL_BASE"] + 5)             # HOST.OUT: last assembled byte
    assert out == FRAMES[2][0], f"HOST.OUT {out:#04x}, expected the last received byte"
    check_no_faults(dut, b)
    ctrl = await b.read(HM["CTRL_BASE"], 2)
    assert ctrl[0] & 1, "RUN_global"
    assert not (ctrl[1] & 0x05), f"sticky CONFLICT/MEMHAZ: {ctrl[1]:#04x}"
    dut._log.info(f"asm: {b.cycle} cycles, {nbits} captured bits, {len(FRAMES)} frames")


@cocotb.test()
async def ps2_score_receiver(dut):
    """The Score receiver for the same protocol: fixed-rate sampling, status byte per frame."""
    b = Bench(dut)
    await b.start()
    compiled = compile_score()
    assert compiled.ok, compiled.report
    assert "clock      started" in compiled.report, compiled.report
    await b.load(compiled.program)
    await b.write(stream_addr(SCORE_RX_STREAM, "LEN"), [64, 0])
    await b.write(srt_addr(SCORE_RX_STREAM, "CTL"), [1])
    await b.idle(20)

    # The one-byte mailbox holds the frame status; the program only writes when it is empty, so read and
    # clear it (write 1 to HOSTSTAT bit 1) after every frame.
    statuses = []
    for code, bad in FRAMES:
        dut.ps2_din.value = code
        dut.ps2_bad_parity.value = 1 if bad else 0
        await b.pulse("ps2_go", settle=0)
        await b.wait(FRAME_CYCLES)
        stat = await b.read(HM["CTRL_BASE"] + 6, 1)
        statuses.append(await b.read_u8(HM["CTRL_BASE"] + 5) if stat[0] & 0x02 else None)
        await b.write(HM["CTRL_BASE"] + 6, [0x02])
    for k, st in enumerate(statuses):
        dut._log.info(f"score frame {k}: status={st!r}")
        assert st == 0, f"frame {k}: status {st!r} (bit0 start/stop constant mismatch, bit1 violation)"

    pos = await b.read(srt_addr(SCORE_RX_STREAM, "POSL"), 3)
    assert not (pos[1] & 0x80), "receive stream STARVED"
    await b.write(srt_addr(SCORE_RX_STREAM, "CTL"), [0x02])
    await b.idle(20)
    pos = await b.read(srt_addr(SCORE_RX_STREAM, "POSL"), 3)
    nbytes, bidx = pos[0] | ((pos[1] & 0x0F) << 8), pos[1] >> 4
    nbits = nbytes * 8 + bidx
    assert nbits >= len(FRAMES) * SCORE_FRAME_BITS, f"only {nbits} captured bits"

    data = bytes(await b.read(HM["DATA_BASE"] + SCORE_RX_BASE, nbytes + 1))
    bits = [(data[i >> 3] >> (i & 7)) & 1 for i in range(nbits)]
    got_bytes = []
    for k, (code, bad) in enumerate(FRAMES):
        f = bits[k * SCORE_FRAME_BITS:(k + 1) * SCORE_FRAME_BITS]
        byte = sum(b << i for i, b in enumerate(f[:8]))
        parity = f[8]
        odd_ok = ((sum(f[:8]) + parity) % 2) == 1
        got_bytes.append(byte)
        dut._log.info(f"score frame {k}: byte={byte:#04x} captured_parity={parity} odd_ok={odd_ok}")
        assert byte == code, f"score frame {k}: byte {byte:#04x}, expected {code:#04x}"
        assert odd_ok != bad, f"score frame {k}: parity check {'should' if bad else 'should not'} fail"

    try:                                                   # negative control: wrong expected byte fails
        expect_bytes = list(got_bytes)
        expect_bytes[0] = 0xFF if got_bytes[0] != 0xFF else 0x00
        assert expect_bytes[0] == FRAMES[0][0], "deliberately wrong expectation"
    except AssertionError:
        pass
    else:                                                  # pragma: no cover
        raise AssertionError("the checker accepted a wrong byte: the positive control is vacuous")

    check_no_faults(dut, b)
    ctrl = await b.read(HM["CTRL_BASE"], 2)
    assert ctrl[0] & 1, "RUN_global"
    assert not (ctrl[1] & 0x05), f"sticky CONFLICT/MEMHAZ: {ctrl[1]:#04x}"
    dut._log.info(f"score: {b.cycle} cycles, {nbits} captured bits, {len(FRAMES)} frames")
