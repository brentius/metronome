"""Self-tests of the independent checkers: encode -> decode round trips and hand-built waveforms."""
import zlib

from protocols import (eth_decode, eth_encode, i2c_decode, spi_decode, uart_decode, uart_encode)


def test_uart_roundtrip_fractional_baud():
    cpb = 60e6 / 115200            # 520.83 cycles per bit
    data = bytes([0x00, 0x55, 0xA5, 0xFF, 0x3C])
    frames = uart_decode(uart_encode(data, cpb), cpb)
    assert [f.value for f in frames] == list(data)
    assert not any(f.framing_error for f in frames)


def test_uart_framing_error_detected():
    cpb = 16
    wave = uart_encode(b"\x41", cpb)
    stop_centre = 20 + int(9.5 * cpb)
    wave[stop_centre] = 0
    assert uart_decode(wave, cpb)[0].framing_error


def _spi_wave(tx: list[int], rx: list[int], mode: int, half: int = 4):
    cpol, cpha = (mode >> 1) & 1, mode & 1
    sck, mosi, miso, cs = [], [], [], []

    def emit(n, c, o, i, s):
        for _ in range(n):
            sck.append(c); mosi.append(o); miso.append(i); cs.append(s)

    emit(4, cpol, 0, 0, 1)
    for bo, bi in zip(tx, rx):
        for k in range(7, -1, -1):
            o, i = (bo >> k) & 1, (bi >> k) & 1
            if cpha == 0:
                emit(half, cpol, o, i, 0)
                emit(half, 1 - cpol, o, i, 0)
            else:
                emit(half, 1 - cpol, o, i, 0)
                emit(half, cpol, o, i, 0)
    emit(4, cpol, 0, 0, 1)
    return sck, mosi, miso, cs


def test_spi_all_modes():
    for mode in range(4):
        tx, rx = [0x9F, 0x00, 0xA5], [0xFF, 0xEF, 0x40]
        txs = spi_decode(*_spi_wave(tx, rx, mode), mode=mode)
        assert txs == [(tx, rx)], (mode, txs)


def test_i2c_write_with_ack():
    scl, sda = [], []

    def hold(c, d, n=4):
        scl.extend([c] * n); sda.extend([d] * n)

    hold(1, 1)
    hold(1, 0)                                  # START
    for byte, ack in [(0xA0, 1), (0x3C, 1)]:
        for k in range(7, -1, -1):
            b = (byte >> k) & 1
            hold(0, b); hold(1, b); hold(0, b)
        hold(0, 0 if ack else 1); hold(1, 0 if ack else 1); hold(0, 0)
    hold(1, 0)
    hold(1, 1)                                  # STOP
    txs = i2c_decode(scl, sda)
    assert txs[0].events == [("S",), ("B", 0xA0, True), ("B", 0x3C, True), ("P",)]


def test_eth_roundtrip_and_fcs():
    body = bytes(range(64))
    frames = eth_decode(eth_encode(body))
    assert len(frames) == 1 and frames[0].data == body and frames[0].fcs_ok
    bad = eth_decode(eth_encode(body, append_fcs=False))   # last 4 body bytes are taken as a (wrong) FCS
    assert len(bad) == 1 and not bad[0].fcs_ok


def test_crc32_reference_value():
    # IEEE 802.3 / zlib CRC-32 check value for "123456789"
    assert zlib.crc32(b"123456789") == 0xCBF43926
