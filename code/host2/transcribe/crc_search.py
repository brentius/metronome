"""Brute-force CRC parameter search over captured frames (last W bytes are the CRC)."""
from __future__ import annotations

from dataclasses import dataclass

# Polynomials of the common catalogue CRCs of each width.
POLYS = {
    8: [0x07, 0x31, 0x1D, 0x9B, 0xD5, 0x2F, 0x39, 0xEA, 0xA7, 0x49],
    16: [0x1021, 0x8005, 0x3D65, 0xC867, 0x0589, 0x755B, 0x1DCF, 0xA097, 0x8BB7, 0x080B, 0x5935],
    32: [0x04C11DB7, 0x1EDC6F41, 0xA833982B, 0x741B8CD7, 0x814141AB, 0x000000AF],
}
EXTRA_INITS = {16: [0x1D0F, 0xB2AA, 0xC6C6, 0x89EC], 8: [], 32: []}

NAMES = {
    (8, 0x07, 0x00, False, False, 0x00): "CRC-8/SMBUS",
    (8, 0x07, 0x00, False, False, 0x55): "CRC-8/ITU",
    (8, 0x07, 0xFF, False, False, 0x00): "CRC-8/ROHC-LIKE",
    (8, 0x31, 0x00, True, True, 0x00): "CRC-8/MAXIM-DOW",
    (8, 0x1D, 0xFF, False, False, 0xFF): "CRC-8/SAE-J1850",
    (16, 0x1021, 0xFFFF, False, False, 0x0000): "CRC-16/CCITT-FALSE",
    (16, 0x1021, 0x0000, False, False, 0x0000): "CRC-16/XMODEM",
    (16, 0x1021, 0x0000, True, True, 0x0000): "CRC-16/KERMIT",
    (16, 0x1021, 0xFFFF, True, True, 0xFFFF): "CRC-16/X-25",
    (16, 0x1021, 0x1D0F, False, False, 0x0000): "CRC-16/AUG-CCITT",
    (16, 0x8005, 0x0000, True, True, 0x0000): "CRC-16/ARC",
    (16, 0x8005, 0xFFFF, True, True, 0x0000): "CRC-16/MODBUS",
    (16, 0x8005, 0xFFFF, True, True, 0xFFFF): "CRC-16/USB",
    (16, 0x8005, 0x0000, False, False, 0x0000): "CRC-16/BUYPASS",
    (32, 0x04C11DB7, 0xFFFFFFFF, True, True, 0xFFFFFFFF): "CRC-32/ETHERNET",
    (32, 0x04C11DB7, 0xFFFFFFFF, False, False, 0x00000000): "CRC-32/MPEG-2",
    (32, 0x04C11DB7, 0xFFFFFFFF, False, False, 0xFFFFFFFF): "CRC-32/BZIP2",
    (32, 0x1EDC6F41, 0xFFFFFFFF, True, True, 0xFFFFFFFF): "CRC-32C",
}


@dataclass(frozen=True)
class CrcMatch:
    width: int
    poly: int
    init: int
    refin: bool
    refout: bool
    xorout: int
    byteorder: str                      # how the CRC bytes sit at the end of the frame

    @property
    def name(self) -> str:
        return NAMES.get((self.width, self.poly, self.init, self.refin, self.refout, self.xorout), "crc_found")

    def decl(self, ident: str | None = None) -> str:
        """Score syntax (spec section 9): crc NAME width W poly P init I [refin] [refout] xorout X."""
        nm = ident or self.name.lower().replace("/", "_").replace("-", "_")
        h = self.width // 4
        return (f"crc {nm} width {self.width} poly 0x{self.poly:0{h}X} init 0x{self.init:0{h}X}"
                f"{' refin' if self.refin else ''}{' refout' if self.refout else ''} xorout 0x{self.xorout:0{h}X}")


def _refl(v, w):
    return int(format(v, f"0{w}b")[::-1], 2)


def _table(width, poly):
    top, mask, t = 1 << (width - 1), (1 << width) - 1, []
    for b in range(256):
        r = b << (width - 8)
        for _ in range(8):
            r = ((r << 1) ^ poly) & mask if r & top else (r << 1) & mask
        t.append(r)
    return t


_R8 = [_refl(b, 8) for b in range(256)]


def _raw(table, width, init, data, refin):
    mask, r, sh = (1 << width) - 1, init, width - 8
    for b in data:
        b = _R8[b] if refin else b
        r = ((r << 8) & mask) ^ table[((r >> sh) ^ b) & 0xFF]
    return r


def search_crc(frames: list[bytes], crc_len: int | None = None, extra_polys: dict | None = None) -> list[CrcMatch]:
    """Every catalogue parameter set under which all frames' trailing crc_len bytes equal the CRC of the rest.

    crc_len None tries 1, 2 and 4 bytes. Both byte orders are tried. Needs >= 2 distinct frames. Candidates are the
    catalogue polynomials x init {0, all-ones, a few known} x xorout {0, all-ones, known} x refin x refout, so a
    CRC outside that set is not found (the search is not a general polynomial solver).
    """
    frames = [bytes(f) for f in frames]
    if len(set(frames)) < 2:
        raise ValueError("need at least 2 distinct frames")
    out = []
    for W in ([crc_len] if crc_len else [1, 2, 4]):
        width = 8 * W
        if width not in POLYS or any(len(f) <= W for f in frames):
            continue
        mask = (1 << width) - 1
        polys = list(POLYS[width]) + list((extra_polys or {}).get(width, []))
        inits = sorted({0, mask, *EXTRA_INITS.get(width, [])})
        xors = {0, mask, *{k[5] for k in NAMES if k[0] == width}}
        pays = [f[:-W] for f in frames]
        for order in ("big", "little"):
            vals = [int.from_bytes(f[-W:], order) for f in frames]
            for poly in polys:
                tab = _table(width, poly)
                for refin in (False, True):
                    for init in inits:
                        raws = [_raw(tab, width, init, p, refin) for p in pays]
                        for refout in (False, True):
                            fin = [_refl(r, width) if refout else r for r in raws]
                            x = fin[0] ^ vals[0]
                            if x in xors and all((a ^ x) == v for a, v in zip(fin, vals)):
                                out.append(CrcMatch(width, poly, init, refin, refout, x, order))
    return out
