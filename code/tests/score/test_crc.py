import os
import zlib

from score.crc import STD, crc_bytes


def test_crc32_matches_zlib():
    for n in (0, 1, 7, 64, 1500):
        d = os.urandom(n)
        assert crc_bytes(STD["crc32_ethernet"], d) == zlib.crc32(d)


def test_rocksoft_check_values():
    d = b"123456789"
    assert crc_bytes(STD["crc32_ethernet"], d) == 0xCBF43926
    assert crc_bytes(STD["crc16_ccitt"], d) == 0x29B1
    assert crc_bytes(STD["crc16_usb"], d) == 0xB4C8
    assert crc_bytes(STD["crc8_smbus"], d) == 0xF4
    assert crc_bytes(STD["crc5_usb"], d) == 0x19
    assert crc_bytes(STD["crc15_can"], d) == 0x059E
