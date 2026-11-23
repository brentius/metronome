"""Scenarios, jitter injection and protocol decoders for the CDC bench.

Stimulus is built with the existing lockstep scenario machinery (``code/tests/lockstep_v2/scenarios.py`` and
``scenarios_v4.py``, imported, never edited).  Every result is decoded from the chip's pins only - MISO of the SPI
host link and the O8 UART transmitter - so the same bench runs on the RTL and on a gate-level netlist.

Decoders
    ``decode_spi``  groups MISO and MOSI into chip-select transactions at the *ideal* SCK rising edges, sampling
                    MISO one cycle before each rise (the chip's own host link does the same; see
                    ``metronome2.spi.decode_read``).  A +-1 cycle input slip keeps that sample inside the valid
                    bit window because SCK is at most clk/16 in the SPI scenarios.
    ``decode_uart`` finds idle-high -> start bits and samples at bit centres with a float bit period taken from the
                    firmware's learned TU, so a 2% baud error and a non-integer period are covered.
"""
from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[3]
for _p in (ROOT / "code/tests/lockstep_v2", ROOT / "sim/reference", ROOT / "code/host2"):
    if str(_p) not in sys.path:
        sys.path.insert(0, str(_p))

from metronome2 import m                                   # noqa: E402
from metronome2.spi import SCK, CSN                      # noqa: E402
from scenarios import HM, IDLE, Scn, reg_addr            # noqa: E402
import scenarios_v4                                      # noqa: E402
from check_uart_peer import TRAINING                     # noqa: E402

MISO = 0          # uo_out bit 0
O8 = 2            # uo_out bit 2: firmware output pin O8


# ---------------------------------------------------------------------------------------------------- decoders
def _bits_to_bytes(bits: list[int]) -> bytes:
    out = bytearray()
    for j in range(0, len(bits) - 7, 8):
        value = 0
        for b in bits[j:j + 8]:
            value = (value << 1) | b
        out.append(value)
    return bytes(out)


def decode_spi(frames: list[int], miso: list[int | None]) -> tuple[list[tuple[bytes, bytes]], list[tuple[int, bytes]]]:
    """Decode the host link from the ideal ui_in frames and the observed MISO level per cycle.

    Returns (transactions, reads) where transactions are (mosi_bytes, miso_bytes) per chip-select frame and reads
    are (address, data) for every 0x03 command.  MISO is sampled one cycle before each rising SCK edge.
    """
    txns: list[tuple[bytes, bytes]] = []
    reads: list[tuple[int, bytes]] = []
    mosi_bits: list[int] = []
    miso_bits: list[int] = []
    active = False
    prev_sck = False
    for t, f in enumerate(frames):
        cs = bool(f & CSN)                       # CS_N high = idle
        sck = bool(f & SCK)
        if not cs:
            active = True
            if sck and not prev_sck:
                mosi_bits.append(1 if f & 4 else 0)
                sample = miso[t - 1] if t else None
                if mosi_bits[:8] == [0, 0, 0, 0, 0, 0, 1, 1] and len(mosi_bits) > 24:
                    assert sample is not None, f"unresolved SPI read data at cycle {t - 1}"
                miso_bits.append(sample or 0)
        elif active:
            mosi, data = _bits_to_bytes(mosi_bits), _bits_to_bytes(miso_bits)
            txns.append((mosi, data))
            if len(mosi) >= 3 and mosi[0] == 0x03:
                reads.append(((mosi[1] << 8) | mosi[2], data[3:]))
            mosi_bits, miso_bits, active = [], [], False
        prev_sck = sck and not cs
    if active:                                   # a frame cut off by the end of the scenario still counts
        mosi, data = _bits_to_bytes(mosi_bits), _bits_to_bytes(miso_bits)
        txns.append((mosi, data))
        if len(mosi) >= 3 and mosi[0] == 0x03:
            reads.append(((mosi[1] << 8) | mosi[2], data[3:]))
    return txns, reads


class UartError(AssertionError):
    pass


def decode_uart(trace: list[int | None], period: float, max_frames: int = 64) -> list[int]:
    """Decode O8 as an 8N1 stream at `period` clocks per bit (LSB first, idle high).

    A start bit must be preceded by at least 8 idle-high cycles.  Samples at bit centres; a non-1 stop bit is a
    framing error (raised, never silently dropped).
    """
    if period < 4:
        raise UartError(f"implausible bit period {period}")
    frames: list[int] = []
    i = 8
    n = len(trace)
    while len(frames) < max_frames:
        start = None
        while i < n:
            if trace[i] == 0 and i >= 8 and all(trace[i - 8:i]):
                start = i
                break
            i += 1
        if start is None:
            break
        bits = [0]
        for k in range(1, 10):
            idx = start + int(round((k + 0.5) * period))
            if idx >= n or trace[idx] is None:
                raise UartError(f"missing or unresolved UART sample at cycle {idx}")
            bits.append(trace[idx])
        if bits[9] != 1:
            raise UartError(f"framing error: stop bit 0 at cycle {start} (samples {bits})")
        frames.append(sum(bits[1 + b] << b for b in range(8)))
        i = idx + 1  # resume inside the stop bit so a fractional period cannot skip the next start
    return frames


def read_at(reads: list[tuple[int, bytes]], address: int) -> bytes:
    """The data of the last read transaction at `address`."""
    for addr, data in reversed(reads):
        if addr == address:
            return data
    raise AssertionError(f"no host read of {address:#06x} in {[hex(a) for a, _ in reads]}")


# ---------------------------------------------------------------------------------------------------- scenarios
@dataclass
class CdcScenario:
    name: str
    scn: Scn
    mask: int = 0xFFFF            # raw-input bits to jitter: bit k<8 = uio_in[k], bit k>=8 = ui_in[k-8]
    rst_jitter: bool = True
    uart_start: int | None = None  # first cycle of the O8 observation window
    validate: Callable[[list[tuple[int, bytes]], list[int]], dict] | None = None
    notes: str = ""
    retain_program: bool = False  # only for scenarios that load one image before running it

    def __post_init__(self):
        assert self.validate is not None, f"{self.name}: no protocol validator"


def _ctrl_offsets():
    names = ("RUN", "STICKY", "IRQEN", "DOORBELL", "HOSTIN", "HOSTOUT", "HOSTSTAT", "ID", "ERRSUM")
    return {n: reg_addr("CTRL", 0, n)[0] for n in names}


def spi_host() -> CdcScenario:
    """Host link at SCK = clk/16: RAM load/readback, register readback, two write bursts, write-only config reads 0."""
    # Exercise every non-host input independently while the emulator is stopped.
    s = Scn("cdc_spi_host", half=8, pins_hi=lambda t, _: ((t // 7) & 0x1F) << 3)
    s.uio = lambda t, _: (t // 11) & 0xFF
    s.reset()
    payload = bytes([0xA5, 0x5A, 0x00, 0xFF, 0x81, 0x7E, 0x33, 0xCC])
    s.data(0x40, payload)                                 # one 8-byte data-RAM write
    s.blk("CTRL", IRQEN=1, HOSTIN=0x5A)
    s.blk("LINE", 0, INC=1, MOD=200)                      # config latch path (async clear, gated clock)
    c = _ctrl_offsets()
    line_inc = reg_addr("LINE", 0, "INC")[0]
    ctrl = bytearray(c["ERRSUM"] - c["RUN"] + 1)
    for name, value in dict(RUN=0, STICKY=0, IRQEN=1, DOORBELL=0, HOSTIN=0x5A, HOSTOUT=0, HOSTSTAT=1,
                            ID=0xA0 | (m.VERSION & 0x0F), ERRSUM=0).items():
        ctrl[c[name] - c["RUN"]] = value
    s.read(HM["DATA_BASE"] + 0x40, 8)
    s.read(c["RUN"], len(ctrl))
    s.blk("CTRL", HOSTIN=0x3C)                            # second write burst after a read burst
    s.read(c["HOSTIN"], 2)                                # HOSTIN, HOSTOUT
    s.read(HM["DATA_BASE"] + 0x40, 8)                     # readback again: RAM retained
    s.read(line_inc, 4)                                   # write-only configuration reads 0
    s.idle(8)

    def validate(reads, tx):
        expected = [
            (HM["DATA_BASE"] + 0x40, payload),
            (c["RUN"], bytes(ctrl)),
            (c["HOSTIN"], bytes([0x3C, 0])),
            (HM["DATA_BASE"] + 0x40, payload),
            (line_inc, bytes(4)),
        ]
        assert reads == expected, (f"SPI readback mismatch:\n got {[(hex(a), d.hex()) for a, d in reads]}"
                                   f"\n exp {[(hex(a), d.hex()) for a, d in expected]}")
        return {"spi_reads": [(a, d.hex()) for a, d in reads]}

    return CdcScenario("spi_host", s, mask=0xFFFF, validate=validate,
                       notes="every raw input bit jittered; SCK = clk/16, MOSI changes 8 cycles before the rise")


def _uart_common(reads, ctrl_address):
    """Fields the v4 firmware writes to data RAM and CTRL (SPEC v2 13 / transcribe fw_stage1)."""
    from transcribe.fw_stage1 import RES
    res = read_at(reads, HM["DATA_BASE"] + RES)
    assert len(res) >= 11, res.hex()
    status, idle = res[0], res[1]
    tu = int.from_bytes(res[2:4], "little")
    frame = res[6:11]
    ctrl = read_at(reads, ctrl_address)
    c = _ctrl_offsets()
    return dict(status=status, idle=idle, tu=tu, frame=frame, ctrl=ctrl, res=res,
                hoststat=ctrl[c["HOSTSTAT"] - c["RUN"]] if len(ctrl) > 6 else None,
                errsum=ctrl[c["ERRSUM"] - c["RUN"]] if len(ctrl) > 8 else None,
                ident=ctrl[c["ID"] - c["RUN"]] if len(ctrl) > 7 else None)


def uart_tx_rx() -> CdcScenario:
    """v4 stage 2 (scenarios_v4.stage2): learn 8N1 framing from training frames, re-transmit them on O8."""
    s = scenarios_v4.stage2()

    def validate(reads, tx):
        info = _uart_common(reads, HM["CTRL_BASE"])
        assert (info["status"], info["idle"]) == (1, 1), f"stage-2 status {info['status']}/{info['idle']}"
        assert 736 <= info["tu"] <= 800, f"learned bit time {info['tu']} outside 23?25 cycles"
        frame = info["frame"]
        assert (frame[0], frame[1], frame[2], frame[4]) == (1, 8, 0, 1), f"framing {tuple(frame)}"
        assert 4 <= frame[3] < len(TRAINING), f"captured {frame[3]} frames"
        assert info["errsum"] == 0, f"ERRSUM {info['errsum']:#04x} after the run"
        assert info["hoststat"] == 2, f"HOSTSTAT {info['hoststat']:#04x}: OUTV=1, INV=0 expected"
        assert info["ident"] == 0xA0 | (m.VERSION & 0x0F)
        frames = decode_uart(tx, info["tu"] / 32)
        assert frames == list(TRAINING[:frame[3]]), f"O8 frames {bytes(frames).hex()} != {TRAINING[:frame[3]].hex()}"
        return {"status": info["status"], "tu": info["tu"], "frame": list(frame), "uart": frames,
                "errsum": info["errsum"]}

    window = next(i for i, step in enumerate(s.steps) if callable(step[2]))
    return CdcScenario("uart_tx_rx", s, mask=1 << 5, uart_start=window, validate=validate,
                       notes="P5 (uio_in[5]) jittered, 24 clocks/bit; SPI readback not jittered",
                       retain_program=True)


def uart_reply() -> CdcScenario:
    """v4 reply learner (scenarios_v4.stage2(reply=0x42)): answer the held-out byte on O8."""
    s = scenarios_v4.stage2(reply=0x42)

    def validate(reads, tx):
        info = _uart_common(reads, HM["CTRL_BASE"])
        assert (info["status"], info["idle"]) == (1, 1), f"stage-2 status {info['status']}/{info['idle']}"
        frame = info["frame"]
        assert (frame[0], frame[1], frame[2], frame[4]) == (1, 8, 0, 1), f"framing {tuple(frame)}"
        assert 736 <= info["tu"] <= 800, f"learned bit time {info['tu']} outside 23?25 cycles"
        assert info["errsum"] == 0 and info["hoststat"] == 2, f"CTRL {info['ctrl'].hex()}"
        frames = decode_uart(tx, info["tu"] / 32)
        assert frames == [0x42], f"reply frames {[hex(f) for f in frames]}"
        return {"status": info["status"], "tu": info["tu"], "frame": list(info["frame"]), "uart": frames,
                "errsum": info["errsum"]}

    window = next(i for i, step in enumerate(s.steps) if callable(step[2]))
    return CdcScenario("uart_reply", s, mask=1 << 5, uart_start=window, validate=validate,
                       notes="P5 jittered; reply 0x42 at the learned rate", retain_program=True)


def uart_rx_baud() -> CdcScenario:
    """UART RX with a 2% baud error: 8N1 framed at alternating 24/25-cycle bits (24.5 average), plus input jitter.

    The firmware measures bit intervals instead of sampling at a nominal baud, so the re-transmitted bytes on O8
    must still be the bytes that were sent.  The model runs confirm the same 11 frames and the same 8N1 framing at
    24.0 and 24.5 cycles/bit; only the learned bit time moves (768 -> 783 in 1/32-cycle units).
    """
    from metronome2_tools.asm import assemble_text
    from metronome2_tools.image import host_writes
    from transcribe.fw_stage1 import RES, source

    pin = 5
    payload = TRAINING
    s = Scn("cdc_uart_rx_baud")
    s.uio = 1 << pin
    s.reset()
    for address, data, _ in host_writes(assemble_text(source(pin, framing=True, transmit=True))):
        s.write(address, data)
    s.idle(100)
    for word in payload:
        for bit_i, level in enumerate([0] + [(word >> b) & 1 for b in range(8)] + [1]):
            s.uio = level << pin
            s.idle(24 + (bit_i & 1))                 # bit period alternates 24, 25, 24, ... (~2% slower)
    window = len(s.steps)
    s.uio = 1 << pin
    s.idle(45_000)
    s.read(HM["DATA_BASE"] + RES, 13)

    def validate(reads, tx):
        data = read_at(reads, HM["DATA_BASE"] + RES)
        assert len(data) == 13, data.hex()
        status, idle = data[0], data[1]
        tu = int.from_bytes(data[2:4], "little")
        frame = data[6:11]
        assert (status, idle) == (1, 1), f"status {status}/{idle}"
        assert (frame[0], frame[1], frame[2], frame[4]) == (1, 8, 0, 1), f"framing {tuple(frame)}"
        count = frame[3]
        assert 4 <= count < len(payload), f"captured {count} frames"
        assert 740 <= tu <= 800, f"learned bit time {tu} (1/32 cycle) is not the 24.5-cycle stream"
        frames = decode_uart(tx, tu / 32)
        assert frames == list(payload[:count]), f"O8 {bytes(frames).hex()} != {payload[:count].hex()}"
        return {"status": status, "tu": tu, "frame": list(frame), "uart": frames}

    return CdcScenario("uart_rx_baud", s, mask=1 << 5, uart_start=window, validate=validate,
                       notes="P5 jittered; bit period alternates 24/25 cycles (2% baud error); a 1-cycle slip is "
                             "4% of one bit", retain_program=True)


def uart_rx_baud_train24() -> CdcScenario:
    """Control for `uart_rx_baud`: the same stream at exactly 24 cycles/bit (no baud error), jitter only."""
    from metronome2_tools.asm import assemble_text
    from metronome2_tools.image import host_writes
    from transcribe.fw_stage1 import RES, source

    pin = 5
    payload = TRAINING
    s = Scn("cdc_uart_rx_control")
    s.uio = 1 << pin
    s.reset()
    for address, data, _ in host_writes(assemble_text(source(pin, framing=True, transmit=True))):
        s.write(address, data)
    s.idle(100)
    for word in payload:
        for level in [0] + [(word >> b) & 1 for b in range(8)] + [1]:
            s.uio = level << pin
            s.idle(24)
    window = len(s.steps)
    s.uio = 1 << pin
    s.idle(45_000)
    s.read(HM["DATA_BASE"] + RES, 13)

    def validate(reads, tx):
        data = read_at(reads, HM["DATA_BASE"] + RES)
        status, idle = data[0], data[1]
        tu = int.from_bytes(data[2:4], "little")
        frame = data[6:11]
        assert (status, idle) == (1, 1), f"status {status}/{idle}"
        assert (frame[0], frame[1], frame[2], frame[4]) == (1, 8, 0, 1), f"framing {tuple(frame)}"
        assert 736 <= tu <= 800, f"bit time {tu}"
        count = frame[3]
        assert 4 <= count < len(payload), f"captured {count} frames"
        frames = decode_uart(tx, tu / 32)
        assert frames == list(payload[:count]), f"O8 {bytes(frames).hex()} != {payload[:count].hex()}"
        return {"status": status, "tu": tu, "frame": list(frame), "uart": frames}

    return CdcScenario("uart_rx_control", s, mask=1 << 5, uart_start=window, validate=validate,
                       notes="P5 jittered only; 24 clocks/bit", retain_program=True)


def uart_example() -> CdcScenario:
    """Receive with a fixed baud setting and send through the shipped UART TX example."""
    sys.path.insert(0, str(ROOT / "code/scorec"))
    sys.path.insert(0, str(ROOT / "code/score"))
    from metronome2_tools.asm import assemble_text
    from metronome2_tools.image import host_writes
    from scorec import compile_score

    nominal = 60_000_000 / 115_200
    payload = bytes([0x00, 0xFF, 0xA5, 0x80])
    score = (ROOT / "code/score/lib/uart_8n1.score").read_text(encoding="utf-8")
    receiver = compile_score(score, "receiver", "tx=P5").program
    sender = assemble_text((ROOT / "code/host2/examples/uart_tx.mas").read_text(encoding="utf-8"))
    s = Scn("cdc_uart_example")
    s.uio = 1 << 5
    s.reset()
    for address, data, _ in host_writes(receiver):
        s.write(address, data)
    s.idle(100)
    for word in payload:
        for level in [0] + [(word >> bit) & 1 for bit in range(8)] + [1]:
            s.uio = level << 5
            s.idle(531)  # 1.90% below nominal baud, calculated at 60 MHz
    address = HM["DATA_BASE"] + 0x400
    s.read(address, len(payload))

    s.reset()
    for addr, data, _ in host_writes(sender):
        s.write(addr, data)
    window = len(s.steps)
    for word in payload:
        s.blk("CTRL", HOSTIN=word)
        s.idle(6000)

    def validate(reads, tx):
        received = read_at(reads, address)
        sent = decode_uart(tx, nominal)
        assert received == payload, f"UART RX {received.hex()} != {payload.hex()}"
        assert sent == list(payload), f"UART TX {bytes(sent).hex()} != {payload.hex()}"
        return {"rx": received.hex(), "tx": bytes(sent).hex()}

    return CdcScenario("uart_example", s, mask=1 << 5, uart_start=window, validate=validate,
                       notes="P5 jittered, RX 531 cycles/bit vs nominal 520.833; stock TX example on O8")


def spi_host_fast() -> CdcScenario:
    """Negative control: a host write at the narrowest possible setup (SCK half period = 1 cycle).

    `spi.write_frames` holds MOSI for `half` cycles before each rising SCK edge, so at half=1 the pin has exactly one
    cycle of setup; at the default half=8 it has eight.  Both SCK and MOSI cross the same two-flop synchroniser, so a
    late MOSI resolution eats setup but does not break the pipeline.  The address is first written at the safe rate
    (sentinel) and read back, then overwritten at half=1 and read back again: the two reads must show two different
    values, and SRAM retention across the pass boundary cannot mask a lost fast write.

    Used only by `test_negative_control`, which requires the decoded readback of the jittered pass to differ from the
    unperturbed control.  This is not a spec-conformant host (SPEC v2 assumes SCK well below clk/2); it exists to
    prove that the comparison in `test_cdc_jitter` can report a difference at all.
    """
    addr = HM["DATA_BASE"] + 0x20
    sentinel = bytes([0x5A, 0x5A])
    payload = bytes([0xA5, 0x3C])
    s = Scn("cdc_spi_fast")
    s.reset()
    s.write(addr, sentinel)                               # clk/16: 8 cycles of MOSI setup
    s.read(addr, len(sentinel))
    s.write(addr, payload, half=1)                        # clk/2: 1 cycle of MOSI setup
    s.read(addr, len(payload))
    s.idle(8)

    def validate(reads, tx):
        expected = [(addr, sentinel), (addr, payload)]
        assert reads == expected, (f"negative-control readback {[(hex(a), d.hex()) for a, d in reads]}"
                                   f" != {[(hex(a), d.hex()) for a, d in expected]}")
        return {"spi_reads": [(a, d.hex()) for a, d in reads]}

    return CdcScenario("spi_host_fast", s, mask=1 << 10, rst_jitter=False, validate=validate,
                       notes="negative control: sentinel write at clk/16, overwrite at clk/2 with MOSI edges "
                             "delayed (see jitter_depth_cycles), both read back")


DEFAULT_SCENARIOS = ("spi_host", "uart_example")
EXTENDED_SCENARIOS = ("uart_rx_control", "uart_rx_baud", "uart_tx_rx", "uart_reply")
NEGATIVE_CONTROL = "spi_host_fast"


BUILDERS = {
    "spi_host": spi_host,
    "uart_example": uart_example,
    "uart_tx_rx": uart_tx_rx,
    "uart_reply": uart_reply,
    "uart_rx_baud": uart_rx_baud,
    "uart_rx_control": uart_rx_baud_train24,
    "spi_host_fast": spi_host_fast,
}


def build(name: str) -> CdcScenario:
    if name not in BUILDERS:
        raise KeyError(f"unknown CDC scenario {name!r}; choose from {sorted(BUILDERS)}")
    return BUILDERS[name]()
