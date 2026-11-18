"""Program-loaded v2 pin-waveform campaign and protocol-independent cell oracle.

Each image contains an unrolled sequence of 4-bit output symbols in program SRAM.
The programmable line engine paces the core; output LUTs map each symbol to GPIO
pins. This is a waveform-replay demonstration, not a set of fixed protocol blocks.
"""
from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path[:0] = [str(ROOT / "code/tests/lockstep_v2"), str(ROOT / "sim/reference")]
import scenarios as base  # noqa: E402
from metronome2 import m  # noqa: E402

I, HM = base.I, m.HOST_MAP


@dataclass(frozen=True)
class Case:
    name: str
    period: int
    cells: tuple[int, ...]       # GPIO O0..O3 values, one per beat
    note: str
    od_mask: int = 0             # pins released when their output symbol bit is 1
    sample_pin: int = 0           # input pin mirrored from one output for a simple RX check
    oe_override: tuple[int, ...] = ()  # optional per-cell 4-bit drive enable map


def bits(v: int, width: int, lsb: bool = False) -> list[int]:
    return [((v >> i) if lsb else (v >> (width - 1 - i))) & 1 for i in range(width)]


def uart() -> Case:
    cells = [1, 1]
    for b in (0xA6, 0x39):
        cells += [0] + bits(b, 8, True) + [1]
    return Case("uart", 60, tuple(cells), "UART 8N1, two frames at 1 Mbit/s on a 60 MHz clock")


def spi(mode: int) -> Case:
    cpol, cpha = mode >> 1, mode & 1
    out = [(cpol << 0) | (1 << 2)]  # CS_N idle high, SCK idles at CPOL
    previous = 0
    for byte in (0x96, 0x2D):
        for bit in bits(byte, 8):
            # Each state is one SCK half-period. CPHA chooses the data launch
            # relationship; the sampling edge is validated from captured pins.
            sck0 = cpol
            sck1 = 1 - cpol
            launch = previous if cpha else bit
            out += [(sck0 << 0) | (launch << 1), (sck1 << 0) | (bit << 1)]
            previous = bit
    # Include the final trailing edge while CS is still active. CPHA=1 samples
    # there; CPHA=0 has already sampled on each leading edge.
    out += [(cpol << 0) | (previous << 1), (cpol << 0) | (1 << 2)]
    return Case(f"spi_mode{mode}", 12, tuple(out),
                f"SPI mode {mode}, CPOL={cpol}/CPHA={cpha}, MOSI 96 2D, active-low CS")


def i2c(freq: int) -> Case:
    # O0=SCL, O1=SDA. This is a precomposed bus trace, including target ACK lows;
    # it demonstrates the electrical line states, not a dynamic target responder.
    period = 300 if freq == 100 else 50
    c = [0b11, 0b11, 0b01]  # bus-free high, then START: SDA falls while SCL high
    for byte in (0xA0, 0xA5):
        for b in bits(byte, 8):
            c += [(0 << 0) | (b << 1)] * (2 if freq == 400 else 1)
            c += [(1 << 0) | (b << 1)]
        c += ([0b00, 0b00, 0b01] if freq == 400 else [0b00, 0b01])  # target ACK
    c += [0b00, 0b01, 0b11, 0b11, 0b11]  # STOP and bus-free tBUF
    return Case(f"i2c_{freq}k", period, tuple(c),
                f"I2C {freq} kHz: START, 0x50 write, precomputed ACK, A5, ACK, STOP", od_mask=0b11)


def usb_ls() -> Case:
    # USB LS D-/D+ are O0/O1. J=01, K=10, SE0=00. DATA0 packet carries
    # sync, complemented PID C3, payload 5A, and CRC16 in little-endian bit order.
    payload = bytes([0x5A])
    crc = 0xFFFF
    for value in payload:
        for bit in range(8):
            feedback = (crc ^ (value >> bit)) & 1
            crc >>= 1
            if feedback:
                crc ^= 0xA001
    crc ^= 0xFFFF
    packet = bytes([0x80, 0xC3]) + payload + crc.to_bytes(2, "little")
    raw = [b for value in packet for b in bits(value, 8, True)]
    states, j, ones = [0b01] * 2, 0b01, 0
    for b in raw:
        if b == 0:
            j = 0b10 if j == 0b01 else 0b01
        states.append(j)
        ones = ones + 1 if b else 0
        if ones == 6:
            j = 0b10 if j == 0b01 else 0b01
            states.append(j)  # stuffed zero
            ones = 0
    states += [0, 0, 0b01, 0b01]  # SE0 then J
    return Case("usb_ls", 40, tuple(states), "USB low-speed DATA0 NRZI/J-K pair, CRC16, stuffing, SE0 EOP")


def ethernet() -> Case:
    # O0/O1 are the differential pair. Manchester output comes from the line's
    # SEG x input LUT at 6 cycles/bit (two 3-cycle halves), preserving 10 Mbit/s.
    bits_out = [b for x in [0x55] * 7 + [0xD5, 0x12, 0xA6] for b in bits(x, 8, True)]
    return Case("ethernet_10baset", 6, tuple(bits_out),
                "10BASE-T Manchester, 10 Mbit/s, preamble/SFD/body only (no MAC FCS)")


def jtag() -> Case:
    # TCK/TMS/TDI on O0/O1/O2. TAP reset -> idle -> DR select/capture/shift/update;
    # TDI is zero. Each clock has low/high half-cells.
    tms = [1] * 5 + [0, 1, 0] + [0] * 32 + [1, 1, 0]
    cells = []
    for t in tms:
        cells += [(0 << 0) | (t << 1), (1 << 0) | (t << 1)]
    return Case("jtag", 12, tuple(cells), "JTAG TCK/TMS TAP reset and bounded DR shift; TDI=0")


def swd() -> Case:
    # SWCLK/SWDIO on O0/O1, request 0xA. Host drives the request push-pull then
    # releases SWDIO after its park bit for four turnaround clocks. O3 mirrors OE.
    f = [1, 1, 0, 1, 0]
    req = [1, *f[1:], sum(f[1:]) & 1, 0, 1] + [1] * 4
    cells = []
    for i, b in enumerate([1] * 4 + req):
        drive = int(i < 12)  # idle + request through park; release during four turnaround clocks
        marker = drive << 3
        cells += [(0 << 0) | (b << 1) | marker, (1 << 0) | (b << 1) | marker]
    oe = (0x0F,) * (len(cells) - 8) + (0x0D,) * 8
    return Case("swd", 12, tuple(cells), "SWD SWCLK/SWDIO host request 0xA, parity, park and released turnaround",
                oe_override=oe)


def ps2() -> Case:
    d = bits(0x5A, 8, True)
    frame = [0, *d, 1 ^ (sum(d) & 1), 1]
    # Change DATA on each rising edge, then hold it for a full high half-cycle
    # before the next falling-edge sample (PS/2 setup time is one half period).
    cells = [0b11, 0b01]  # idle, then prepare the start bit while clock remains high
    for i, b in enumerate(frame):
        next_bit = frame[i + 1] if i + 1 < len(frame) else 1
        cells += [(0 << 0) | (b << 1), (1 << 0) | (next_bit << 1)]
    return Case("ps2", 1800, tuple(cells), "PS/2 11-bit frame, 16.7 kHz, clock/data open-drain", od_mask=0b11)


def can() -> Case:
    # O0 is a recessive-high/dominant-low bus level. 11-bit ID 0x123, DLC1/A5,
    # CRC-15/CAN, bit stuffing, ACK slot and EOF; no analog transceiver is modeled.
    f = [0] + bits(0x123, 11) + [0, 0, 0] + bits(1, 4) + bits(0xA5, 8)
    crc = 0
    for b in f:
        fb = ((crc >> 14) & 1) ^ b
        crc = (crc << 1) & 0x7FFF
        if fb:
            crc ^= 0x4599
    f += bits(crc, 15)
    stuffed, run, prev = [], 0, None
    for b in f:
        stuffed.append(b)
        run = run + 1 if b == prev else 1
        prev = b
        if run == 5:
            prev ^= 1
            stuffed.append(prev)
            run = 1
    return Case("can", 120, tuple(stuffed + [1] * 10),
                "CAN classic 500 kbit/s, 123/DLC1/A5, CRC15/stuffing/NACK/EOF; bus abstraction", od_mask=1)


def custom_hdlc() -> Case:
    data = [0x7E, 0x7D, 0xA5]
    raw = [b for x in data for b in bits(x, 8)]
    crc = 0xFFFF
    for b in raw:
        top = ((crc >> 15) & 1) ^ b
        crc = (crc << 1) & 0xFFFF
        if top:
            crc ^= 0x1021
    raw += bits(crc, 16)
    stuffed, ones = [], 0
    for b in raw:
        stuffed.append(b)
        ones = ones + 1 if b else 0
        if ones == 5:
            stuffed.append(0)
            ones = 0
    flag = bits(0x7E, 8)
    return Case("custom_hdlc", 12, tuple([1] * 2 + flag + stuffed + flag + [1] * 2),
                "Custom HDLC-like CRC16 frame, explicitly non-standard")


def custom_diffman() -> Case:
    raw = [b for x in (0x55, 0xD5, 0x3C) for b in bits(x, 8, True)]
    states, level = [], 1
    for b in raw:
        if b == 0:
            level ^= 1
        states.append(level)
        level ^= 1
        states.append(level)
    return Case("custom_diffman", 12, tuple((v | ((v ^ 1) << 1)) for v in states + [1, 1]),
                "Custom differential-Manchester preamble/sync/data, convention defined in README")


CASES = {c.name: c for c in (uart(), *(spi(m) for m in range(4)), i2c(100), i2c(400), usb_ls(), ethernet(),
                             jtag(), swd(), ps2(), can(), custom_hdlc(), custom_diffman())}


class DecodeError(AssertionError):
    pass


def check_cells(actual: list[int], expected: tuple[int, ...]):
    if len(actual) != len(expected):
        raise DecodeError(f"pin-cell count {len(actual)} != expected {len(expected)}")
    for i, (got, want) in enumerate(zip(actual, expected)):
        if got != want:
            raise DecodeError(f"cell {i}: GPIO state {got:#x} != {want:#x}")


def lut(fn):
    return sum((fn(i) & 1) << i for i in range(32))


def build(name: str):
    c = CASES[name]
    s = base.Scn("proto_" + name)
    s.proto = c
    s.reset()
    is_eth = c.name == "ethernet_10baset"
    s.blk("LINE", 0, INC=1, MOD=c.period, T0=(1 if is_eth else 0xFFFF),
          T1=(c.period // 2 if is_eth else 0xFFFF), T2=(c.period * 2 // 3 if is_eth else 0xFFFF),
          PINS=0, SNAP=0)
    # Four independent output pins expose the unrolled symbol bits. Open-drain
    # symbols release a line when its value is 1; board/testbench pull-ups resolve it.
    for pin in range(4):
        sel = pin | (pin << 2) | (pin << 4)
        if c.name == "swd" and pin == 1:
            # Data comes from symbol[1], while output-enable follows symbol[3].
            sel = 1 | (1 << 2) | (3 << 4)
        s.blk("OUT", pin, BIND=0b100, SEL=sel, LUT=lut(lambda idx: idx & 1),
              OE=(lut(lambda idx: (idx >> 2) & 1) if c.name == "swd" and pin == 1 else
                  lut(lambda idx, p=pin: (0 if (c.od_mask >> p) & 1 and (idx & 1) else 1))) )
    if c.name == "ethernet_10baset":
        # The current line SEG is 0 before T1 and 1 afterwards. Use alternating
        # data/table values for a Manchester mid-bit transition; exact pin decode
        # is performed by the tester against the generated half-cell vector.
        s.blk("OUT", 0, BIND=0b100, SEL=0 | (0 << 2) | (1 << 4),
              LUT=lut(lambda idx: 1 ^ (idx & 1) ^ ((idx >> 4) & 1)), OE=0xFFFFFFFF)
        s.blk("OUT", 1, BIND=0b100, SEL=0 | (0 << 2) | (1 << 4),
              LUT=lut(lambda idx: (idx & 1) ^ ((idx >> 4) & 1)), OE=0xFFFFFFFF)
    words = []
    for i, sym in enumerate(c.cells):
        if i == len(c.cells) - 1:
            words.append(I(("IMM", "L.SYM"), ("ZERO", "T.STOP"), imm=sym, pause=1))
        else:
            words.append(I(("IMM", "L.SYM"), imm=sym, pause=1))
    s.program(0, words)
    s.thread(0, core=0, line=0, trig="L0.BEAT")
    s.blk("CTRL", RUN=1)
    s.campaign_start = len(s.steps)
    s.blk("LRT", 0, CTL=1)
    s.uio = lambda t, o: ((o[1] & 0x0F) | (0xFF & ~o[2]))
    s.idle((len(c.cells) + 4) * c.period + 40)
    s.campaign_end = len(s.steps)
    if is_eth:
        expected = []
        for bit in c.cells:
            expected += [(1 - bit) | (bit << 1), bit | ((1 - bit) << 1)]
        cell_cycles = 3
    else:
        expected = list(c.cells)
        cell_cycles = c.period
    oe = []
    for i, symbol in enumerate(expected):
        enable = 0x0F
        for pin in range(4):
            if (c.od_mask >> pin) & 1 and ((symbol >> pin) & 1):
                enable &= ~(1 << pin)
        if c.oe_override and i < len(c.oe_override):
            enable = c.oe_override[i]
        oe.append(enable)
    s.campaign = {
        "name": c.name,
        "note": c.note,
        "expected_words": expected,
        "cell_cycles": cell_cycles,
        "capture_start": s.campaign_start,
        "capture_end": s.campaign_end,
        "oe_expected": oe,
        "oe_mask": 0x0F,
        "pullups": c.od_mask | (0x02 if c.oe_override else 0),
        "pins_mask": 0x0F,
        "warning_assert": {"tapmiss": 0, "late": 0, "overrun": 0, "starved": 0},
    }
    # Include runtime warning/status register reads in the pin trace for actual
    # RTL and gate-level comparison; exclude them from the protocol capture window.
    s.readback_all()
    return s


ALL_CASES = list(CASES)


def validate_case(name: str, words: list[int]) -> None:
    """Independent pin-vector oracle, used by the simulator and negative self-check."""
    expected = build(name).campaign["expected_words"]
    if len(words) != len(expected):
        raise AssertionError(f"{name}: {len(words)} words, expected {len(expected)}")
    for i, (got, want) in enumerate(zip(words, expected)):
        if got != want:
            raise AssertionError(f"{name}: cell {i} got {got:#x}, expected {want:#x}")

