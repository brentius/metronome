"""Rocksoft-model CRC (width, poly, init, refin, refout, xorout), bit-serial reference implementation."""
from __future__ import annotations

from .ast import CrcDecl

STD = {
    "crc32_ethernet": CrcDecl("crc32_ethernet", 32, 0x04C11DB7, 0xFFFFFFFF, True, True, 0xFFFFFFFF),
    "crc16_ccitt": CrcDecl("crc16_ccitt", 16, 0x1021, 0xFFFF, False, False, 0x0000),          # CCITT-FALSE
    "crc16_usb": CrcDecl("crc16_usb", 16, 0x8005, 0xFFFF, True, True, 0xFFFF),
    "crc5_usb": CrcDecl("crc5_usb", 5, 0x05, 0x1F, True, True, 0x1F),
    "crc8_smbus": CrcDecl("crc8_smbus", 8, 0x07, 0x00, False, False, 0x00),
    "crc15_can": CrcDecl("crc15_can", 15, 0x4599, 0x0000, False, False, 0x0000),
}


def _reflect(v: int, w: int) -> int:
    r = 0
    for i in range(w):
        if v >> i & 1:
            r |= 1 << (w - 1 - i)
    return r


def crc_bytes(c: CrcDecl, data: bytes) -> int:
    """CRC of a byte string. refin: each byte is processed LSB first; otherwise MSB first."""
    reg, top, mask = c.init, 1 << (c.width - 1), (1 << c.width) - 1
    for byte in data:
        for i in range(8):
            bit = (byte >> i & 1) if c.refin else (byte >> (7 - i) & 1)
            fb = ((reg & top) != 0) ^ bit
            reg = (reg << 1) & mask
            if fb:
                reg ^= c.poly
    if c.refout:
        reg = _reflect(reg, c.width)
    return reg ^ c.xorout
