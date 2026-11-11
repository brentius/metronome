"""Independent protocol checkers and stimulus generators.

These decode (or produce) per-clock-cycle pin samples. They deliberately share no code with the chip's programs,
the assembler, the machine description or the reference model, so that a bug in any of those cannot hide here.
Conventions follow the protocol standards, written from the standards' definitions:

- UART: idle high, start bit 0, data LSB first, stop bit 1 (8N1 unless stated).
- SPI: mode 0..3 per (CPOL, CPHA); MSB first unless stated; CS active low.
- I2C: START = SDA falls while SCL high; STOP = SDA rises while SCL high; data valid while SCL high, MSB first,
  9th clock is ACK (SDA low = ACK).
- 10BASE-T (IEEE 802.3 clause 7/14 Manchester): mid-bit transition low->high = 1, high->low = 0. Frame = 7 bytes
  preamble 0x55, SFD 0xD5, then bytes LSB first; FCS = CRC-32 (zlib.crc32) of the frame, transmitted LSB first.
"""
from __future__ import annotations

import zlib
from dataclasses import dataclass, field


# --------------------------------------------------------------------------------------------------------------
# UART
# --------------------------------------------------------------------------------------------------------------
@dataclass
class UartFrame:
    value: int
    start_cycle: int
    framing_error: bool = False


def uart_decode(samples: list[int], cycles_per_bit: float, data_bits: int = 8, idle: int = 1) -> list[UartFrame]:
    """Decode an idle-high UART line sampled once per clock. Samples each bit at its centre (from the start edge)."""
    out: list[UartFrame] = []
    i, n = 0, len(samples)
    while i < n - 1:
        if samples[i] == idle and samples[i + 1] != idle:      # falling edge = start of start bit
            s = i + 1
            centre = lambda k: s + int((k + 0.5) * cycles_per_bit)  # noqa: E731
            if centre(data_bits + 1) >= n:
                break
            if samples[centre(0)] == idle:                      # glitch, not a start bit
                i += 1
                continue
            v = 0
            for b in range(data_bits):
                v |= (samples[centre(1 + b)] & 1) << b
            stop_ok = samples[centre(1 + data_bits)] == idle
            out.append(UartFrame(v, s, not stop_ok))
            i = centre(1 + data_bits)
        else:
            i += 1
    return out


def uart_encode(data: bytes, cycles_per_bit: float, idle_cycles: int = 20, data_bits: int = 8) -> list[int]:
    """Per-cycle line levels for 8N1 frames (stimulus for receivers). Fractional bit times accumulate exactly."""
    bits: list[int] = []
    for byte in data:
        bits += [0] + [(byte >> b) & 1 for b in range(data_bits)] + [1]
    out = [1] * idle_cycles
    t = 0.0
    for k, bit in enumerate(bits):
        end = (k + 1) * cycles_per_bit
        while t < end:
            out.append(bit)
            t += 1
    return out + [1] * idle_cycles


# --------------------------------------------------------------------------------------------------------------
# SPI
# --------------------------------------------------------------------------------------------------------------
def spi_decode(sck: list[int], mosi: list[int], miso: list[int], cs_n: list[int], mode: int = 0,
               msb_first: bool = True, bits: int = 8) -> list[tuple[list[int], list[int]]]:
    """Return one (mosi_bytes, miso_bytes) per CS-low transaction. Samples on the mode's sampling edge."""
    cpol, cpha = (mode >> 1) & 1, mode & 1
    sample_on_rise = (cpol == cpha)          # modes 0 and 3 sample on the rising edge
    txs, cur_o, cur_i, bo, bi, nb = [], [], [], 0, 0, 0
    active = False
    for t in range(1, len(sck)):
        if cs_n[t] == 0 and not active:
            active, cur_o, cur_i, bo, bi, nb = True, [], [], 0, 0, 0
        elif cs_n[t] == 1 and active:
            active = False
            txs.append((cur_o, cur_i))
            continue
        if not active:
            continue
        edge = (sck[t - 1] == 0 and sck[t] == 1) if sample_on_rise else (sck[t - 1] == 1 and sck[t] == 0)
        if edge:
            if msb_first:
                bo, bi = (bo << 1) | mosi[t], (bi << 1) | miso[t]
            else:
                bo, bi = bo | (mosi[t] << nb), bi | (miso[t] << nb)
            nb += 1
            if nb == bits:
                cur_o.append(bo)
                cur_i.append(bi)
                bo = bi = nb = 0
    if active:
        txs.append((cur_o, cur_i))
    return txs


# --------------------------------------------------------------------------------------------------------------
# I2C
# --------------------------------------------------------------------------------------------------------------
@dataclass
class I2cTransaction:
    events: list[tuple] = field(default_factory=list)   # ("S",), ("Sr",), ("B", byte, ack_bool), ("P",)


def i2c_decode(scl: list[int], sda: list[int]) -> list[I2cTransaction]:
    """Decode a wired-AND bus (lists are the resolved line levels). Checks SDA stability while SCL is high."""
    txs: list[I2cTransaction] = []
    cur: I2cTransaction | None = None
    bits: list[int] = []
    for t in range(1, len(scl)):
        if scl[t] == 1 and scl[t - 1] == 1 and sda[t] != sda[t - 1]:
            if sda[t] == 0:          # START or repeated START
                if cur is None:
                    cur = I2cTransaction([("S",)])
                else:
                    cur.events.append(("Sr",))
                bits = []
            else:                    # STOP
                if cur is not None:
                    cur.events.append(("P",))
                    txs.append(cur)
                cur, bits = None, []
            continue
        if cur is not None and scl[t - 1] == 0 and scl[t] == 1:
            bits.append(sda[t])
            if len(bits) == 9:
                v = 0
                for b in bits[:8]:
                    v = (v << 1) | b
                cur.events.append(("B", v, bits[8] == 0))
                bits = []
    if cur is not None:
        txs.append(cur)
    return txs


# --------------------------------------------------------------------------------------------------------------
# 10BASE-T Manchester
# --------------------------------------------------------------------------------------------------------------
@dataclass
class EthFrame:
    data: bytes                 # destination .. payload (without FCS)
    fcs_ok: bool
    start_cycle: int


def manchester_bits(samples: list[int], cycles_per_bit: float) -> list[tuple[int, int]]:
    """Recover (bit, cycle) pairs from a Manchester line by finding mid-bit transitions.

    Uses transitions only: a transition is a mid-bit transition if it is at least 0.75 bit times after the previous
    mid-bit transition (boundary transitions occur half a bit after a mid-bit one).
    """
    out: list[tuple[int, int]] = []
    last_mid = None
    for t in range(1, len(samples)):
        if samples[t] != samples[t - 1]:
            if last_mid is None or t - last_mid >= 0.75 * cycles_per_bit:
                out.append((1 if samples[t] == 1 else 0, t))
                last_mid = t
    return out


def eth_decode(samples: list[int], cycles_per_bit: float = 6.0) -> list[EthFrame]:
    """Find preamble + SFD, assemble bytes LSB first until the line goes idle (> 2 bit times without transitions)."""
    bits = manchester_bits(samples, cycles_per_bit)
    frames: list[EthFrame] = []
    i = 0
    while i < len(bits):
        # look for the SFD pattern ...1,0,1,0,1,0,1,1 (0xD5 LSB first) preceded by alternating bits
        if i >= 8 and [b for b, _ in bits[i - 8:i]] == [1, 0, 1, 0, 1, 0, 1, 1]:
            start = bits[i][1]
            data_bits: list[int] = []
            j = i
            while j < len(bits):
                if j > i and bits[j][1] - bits[j - 1][1] > 2 * cycles_per_bit:
                    break
                data_bits.append(bits[j][0])
                j += 1
            nbytes = len(data_bits) // 8
            raw = bytes(sum(data_bits[8 * k + b] << b for b in range(8)) for k in range(nbytes))
            if len(raw) >= 4:
                body, fcs = raw[:-4], int.from_bytes(raw[-4:], "little")
                frames.append(EthFrame(body, zlib.crc32(body) == fcs, start))
            i = j
        else:
            i += 1
    return frames


def eth_encode(body: bytes, cycles_per_bit: int = 6, idle_cycles: int = 60, append_fcs: bool = True) -> list[int]:
    """Manchester waveform of preamble + SFD + body (+ FCS), idle low before and after (stimulus for receivers)."""
    frame = bytes([0x55] * 7 + [0xD5]) + body
    if append_fcs:
        frame += zlib.crc32(body).to_bytes(4, "little")
    half = cycles_per_bit // 2
    out = [0] * idle_cycles
    for byte in frame:
        for b in range(8):
            bit = (byte >> b) & 1
            first, second = (0, 1) if bit else (1, 0)
            out += [first] * half + [second] * (cycles_per_bit - half)
    return out + [1] * (2 * cycles_per_bit) + [0] * idle_cycles   # end-of-frame: hold high ~2 bits, then idle
