"""SPI mode-0 transaction generators for the host link (bit0 SCK, bit1 CS_N, bit2 MOSI of ui_in). Copied from v1; SPEC v2 9.

Frames are lists of per-cycle ui_in values. CS_N idles high, SCK idles low, data is MSB first. Self-contained so the
same generators drive the RTL testbench.
"""
SCK, CSN, MOSI = 1, 2, 4
IDLE = CSN                      # CS_N high, SCK low, MOSI 0


def _bytes_frames(bs, half_period, lead=4, trail=4):
    f = [IDLE] * lead + [0] * 4                 # CS_N falls, SCK low
    for b in bs:
        for i in range(7, -1, -1):
            mosi = MOSI if (b >> i) & 1 else 0
            f += [mosi] * half_period           # data set up while SCK low
            f += [mosi | SCK] * half_period     # SCK high: slave samples on the rising edge
    f += [0] * half_period                      # SCK back low, CS_N still low
    f += [IDLE] * trail
    return f


def write_frames(addr, data, half_period=8):
    return _bytes_frames([0x02, (addr >> 8) & 0xFF, addr & 0xFF, *bytes(data)], half_period)


def read_frames(addr, n, half_period=8):
    """Read command followed by n dummy bytes during which MISO carries the data."""
    return _bytes_frames([0x03, (addr >> 8) & 0xFF, addr & 0xFF] + [0] * n, half_period)


def decode_read(frames, outs, n):
    """Collect read data: sample MISO on every SCK rising edge of `frames`.

    outs[i] is the (uo, uio_out, uio_oe) tuple (or bare uo value) returned by step(frames[i]); it is the pin value
    during cycle i+1, so the MISO value during cycle i is outs[i-1]. The first 24 sampled bits are the command and
    address; the next 8*n bits are data, MSB first.
    """
    bits = []
    prev = 0
    for i, f in enumerate(frames):
        if (f & SCK) and not prev:
            o = outs[i - 2] if i >= 2 else 0       # MISO during the cycle before the rising edge (stable)
            o = o[0] if isinstance(o, tuple) else o
            bits.append(o & 1)
        prev = f & SCK
    bits = bits[24:24 + 8 * n]
    return [int("".join(map(str, bits[8 * j:8 * j + 8])), 2) for j in range(len(bits) // 8)]


def spi_write(chip, addr, data, half_period=8):
    return chip.run(write_frames(addr, data, half_period))


def spi_read(chip, addr, n, half_period=8):
    fr = read_frames(addr, n, half_period)
    return decode_read(fr, chip.run(fr), n)
