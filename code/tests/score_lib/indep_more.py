"""More independent decoders (continuation of indep.py), written from each standard's own definitions.  Same rules:
no import of the score parser, codec, compiler or machine model."""
from __future__ import annotations

from indep import CLK, NS, edges, runs  # noqa: F401


# ---------------------------------------------------------------------------------------------------------------
# DMX512-A (ANSI E1.11): 250 kbit/s (4 us), BREAK low >= 92 us, MAB high >= 12 us, slots of 11 bits: start bit 0, eight
# data bits LSB first, two stop bits 1.  Slot 0 is the start code.
# ---------------------------------------------------------------------------------------------------------------
def dmx_decode(s, baud=250_000):
    """-> list of packets {brk_us, mab_us, slots:[...], errors:[...]} (slots[0] is the start code)."""
    T = CLK / baud
    n = len(s)
    rs = runs(s)
    pk, i = [], 0
    while i < len(rs):
        lvl, st, ln = rs[i]
        if lvl == 0 and ln * NS >= 92_000 and i + 1 < len(rs):
            p = {"brk_us": ln * NS / 1000, "mab_us": rs[i + 1][2] * NS / 1000, "slots": [], "errors": []}
            if rs[i + 1][0] != 1 or p["mab_us"] < 12:
                p["errors"].append("mab")
            pos = rs[i + 1][1] + rs[i + 1][2]          # the first slot's start bit begins where the MAB ends
            while pos + 11 * T <= n:
                if s[pos] != 0:
                    break
                nxt = next((r for r in rs if r[1] == pos), None)
                if nxt and nxt[2] * NS >= 92_000:      # the next packet's break
                    break

                def at(k, pos=pos):
                    return s[int(pos + (k + 0.5) * T)]

                v = sum(at(1 + b) << b for b in range(8))
                if at(0) != 0 or at(9) != 1 or at(10) != 1:
                    p["errors"].append(("framing", len(p["slots"])))
                p["slots"].append(v)
                pos = int(round(pos + 11 * T))
            pk.append(p)
            i += 2
        else:
            i += 1
    return pk


# ---------------------------------------------------------------------------------------------------------------
# Wiegand (SIA AC-01), 26-bit H10301 format.  D0 low pulse = 0, D1 low pulse = 1.  Pulse 20..100 us, interval between
# pulses 200 us..20 ms.  Bit 1 even parity over bits 2..13, bit 26 odd parity over bits 14..25.
# ---------------------------------------------------------------------------------------------------------------
def wiegand_decode(d0, d1, pulse_us=(20, 100), interval_us=(200, 20_000)):
    """-> (bits, violations)."""
    ev = []
    for w, s in ((0, d0), (1, d1)):
        for lvl, st, ln in runs(s):
            if lvl == 0:
                ev.append((st, ln * NS / 1000, w))
    ev.sort()
    bad, bits = [], []
    for k, (st, us, w) in enumerate(ev):
        bits.append(w)
        if not pulse_us[0] <= us <= pulse_us[1]:
            bad.append(("pulse", us))
        if k and not interval_us[0] <= (st - ev[k - 1][0]) * NS / 1000 <= interval_us[1]:
            bad.append(("interval", (st - ev[k - 1][0]) * NS / 1000))
    return bits, bad


def wiegand26_fields(bits):
    """-> (fc, card, even_ok, odd_ok) of a 26-bit frame given MSB first."""
    assert len(bits) == 26
    even_ok = sum(bits[0:13]) % 2 == 0             # parity bit + the first 12 data bits: an even number of ones
    odd_ok = sum(bits[13:26]) % 2 == 1             # the last 12 data bits + parity bit: an odd number of ones
    num = lambda b: sum(x << (len(b) - 1 - i) for i, x in enumerate(b))  # noqa: E731
    return num(bits[1:9]), num(bits[9:25]), even_ok, odd_ok


def wiegand26_pe(fc, card):
    """The leading even-parity bit the host supplies: even number of ones over fc (8) and the card's top four bits."""
    first12 = [(fc >> (7 - i)) & 1 for i in range(8)] + [(card >> (15 - i)) & 1 for i in range(4)]
    return sum(first12) % 2


# ---------------------------------------------------------------------------------------------------------------
# HDLC (ISO 13239 / ITU-T X.25 LAPB framing): flag 01111110, zero insertion after five ones, FCS-16 = CRC-16/X-25 (poly
# 0x1021 reflected = 0x8408, init 0xFFFF, final complement), transmitted low byte first, data bits LSB first.
# ---------------------------------------------------------------------------------------------------------------
def crc16_x25(data: bytes) -> int:
    c = 0xFFFF
    for b in data:
        c ^= b
        for _ in range(8):
            c = (c >> 1) ^ 0x8408 if c & 1 else c >> 1
    return c ^ 0xFFFF


def hdlc_bits(clk, d):
    """The data bit at every rising clock edge."""
    return [d[i] for i in range(1, len(clk)) if clk[i] and not clk[i - 1]]


def hdlc_decode(bits):
    """Flag-delimited frames, zero deletion, FCS check.  -> (frames, errors); frames are (payload bytes, fcs_ok)."""
    frames, errors = [], []
    ones, cur, inframe = 0, [], False
    for k, b in enumerate(bits):
        if b:
            ones += 1
            cur.append(1)
            if ones == 7:
                errors.append(("abort", k))
                cur, ones, inframe = [], 0, False
            continue
        if ones == 6:                                  # 0 1 1 1 1 1 1 0 : a flag (this is its closing zero)
            body = cur[:-7]                            # the six ones and the zero before them belong to the flag
            if inframe and body:
                if len(body) % 8:
                    errors.append(("length", k, len(body)))
                else:
                    by = bytes(sum(body[i + j] << j for j in range(8)) for i in range(0, len(body), 8))
                    frames.append((by[:-2], len(by) >= 3 and crc16_x25(by[:-2]) == by[-2] | by[-1] << 8))
            cur, inframe, ones = [], True, 0
            continue
        if ones == 5:                                  # the stuffed zero: delete it
            ones = 0
            continue
        ones = 0
        cur.append(0)
    return frames, errors


# ---------------------------------------------------------------------------------------------------------------
# 1-Wire (Maxim app note 126, standard speed): reset low >= 480 us, presence low 60..240 us starting 15..60 us after the
# release, write-0 low 60..120 us, write-1 / read initiation low 1..15 us, line read 15 us after the falling edge,
# LSB first.  CRC-8 = x^8 + x^5 + x^4 + 1 (reflected 0x8C), init 0.
# ---------------------------------------------------------------------------------------------------------------
def crc8_maxim(data: bytes) -> int:
    c = 0
    for b in data:
        c ^= b
        for _ in range(8):
            c = (c >> 1) ^ 0x8C if c & 1 else c >> 1
    return c


def onewire_decode(s, scale=1.0):
    """-> list of transactions {reset_us, presence:(start_us, len_us) | None, bytes:[...], errors:[...]}.
    `scale` > 1 reads a trace that was played `scale` times too fast (every duration is multiplied by it)."""
    us = lambda n: n * NS / 1000 * scale  # noqa: E731
    rs = runs(s)
    out, i = [], 0
    while i < len(rs):
        lvl, st, ln = rs[i]
        if lvl == 0 and us(ln) >= 480 and i + 1 < len(rs):
            t = {"reset_us": us(ln), "presence": None, "bytes": [], "errors": []}
            rel = rs[i + 1][1]                       # first sample after the release
            j = i + 2
            if j < len(rs) and rs[j][0] == 0:
                ps, pl = us(rs[j][1] - rel), us(rs[j][2])
                t["presence"] = (ps, pl)
                if not (15 <= ps <= 60.05 and 60 <= pl <= 240):     # 0.05 us: float rounding of exactly 60 us
                    t["errors"].append(("presence window", ps, pl))
                j += 1
            bits = []
            while j < len(rs):
                if rs[j][0] == 0 and us(rs[j][2]) < 480:
                    f, ln2 = rs[j][1], rs[j][2]
                    if f + int(15_000 / NS / scale) >= len(s):
                        break
                    bit = s[f + int(14_000 / NS / scale)]    # the line 14 us after the falling edge (the 15 us read point)
                    low = us(ln2)
                    if bit == 1 and not 1 <= low <= 15:
                        t["errors"].append(("slot-1 low", low))
                    if bit == 0 and not 15 < low <= 120 and j + 1 < len(rs):
                        t["errors"].append(("slot-0 low", low))
                    bits.append(bit)
                    j += 1
                elif rs[j][0] == 0:
                    break
                else:
                    j += 1
            t["bytes"] = [sum(bits[k + b] << b for b in range(8)) for k in range(0, len(bits) - 7, 8)]
            out.append(t)
            i = j
        else:
            i += 1
    return out


# ---------------------------------------------------------------------------------------------------------------
# ARM Serial Wire Debug (ADIv5.2, IHI 0031): request = start 1, APnDP, RnW, A[2], A[3], parity (even over the four),
# stop 0, park 1; one turnaround; ACK 3 bits LSB first (OK 001, WAIT 010, FAULT 100); read: 32 data bits LSB first +
# even parity, then a turnaround; write: a turnaround, then 32 data bits + even parity.  Every bit is taken on the
# rising SWCLK edge.
# ---------------------------------------------------------------------------------------------------------------
def swd_decode(swclk, swdio):
    bits = [swdio[i] for i in range(1, len(swclk)) if swclk[i] and not swclk[i - 1]]
    out, k = [], 0
    word = lambda b: sum(x << i for i, x in enumerate(b))  # noqa: E731
    while k + 12 <= len(bits):
        if bits[k] != 1:
            k += 1
            continue
        h = bits[k:k + 8]
        t = {"apndp": h[1], "rnw": h[2], "a": word(h[3:5]), "errors": []}
        if (h[1] + h[2] + h[3] + h[4] + h[5]) % 2:
            t["errors"].append("request parity")
        if h[6] != 0 or h[7] != 1:
            t["errors"].append("stop/park")
        k += 8 + 1                                       # the request, then the turnaround
        a = word(bits[k:k + 3])
        k += 3
        t["ack"] = {1: "OK", 2: "WAIT", 4: "FAULT"}.get(a, f"bad{a}")
        if t["ack"] == "OK":
            if t["rnw"]:
                d, p = bits[k:k + 32], bits[k + 32]
                k += 33 + 1                              # data + parity, then the turnaround
            else:
                k += 1                                   # the turnaround
                d, p = bits[k:k + 32], bits[k + 32]
                k += 33
            t["data"] = word(d)
            if sum(d) % 2 != p:
                t["errors"].append("data parity")
        out.append(t)
    return out


# ---------------------------------------------------------------------------------------------------------------
# IEEE 1149.1 TAP controller: sixteen states, advanced on each rising TCK by TMS; TDI is sampled and TDO presented in
# Shift-DR.
# ---------------------------------------------------------------------------------------------------------------
TAP = {
    "TLR": ("RTI", "TLR"), "RTI": ("RTI", "SelDR"), "SelDR": ("CapDR", "SelIR"), "CapDR": ("ShDR", "Ex1DR"),
    "ShDR": ("ShDR", "Ex1DR"), "Ex1DR": ("PauDR", "UpdDR"), "PauDR": ("PauDR", "Ex2DR"), "Ex2DR": ("ShDR", "UpdDR"),
    "UpdDR": ("RTI", "SelDR"), "SelIR": ("CapIR", "TLR"), "CapIR": ("ShIR", "Ex1IR"), "ShIR": ("ShIR", "Ex1IR"),
    "Ex1IR": ("PauIR", "UpdIR"), "PauIR": ("PauIR", "Ex2IR"), "Ex2IR": ("ShIR", "UpdIR"), "UpdIR": ("RTI", "SelDR"),
}


def jtag_decode(tck, tms, tdi, tdo):
    """-> list of data-register scans {tdi:[bits], tdo:[bits], path:[states]} (bit 0 shifted first)."""
    st, scans, cur = "RTI", [], None
    for i in range(1, len(tck)):
        if not (tck[i] and not tck[i - 1]):
            continue
        if st == "ShDR":
            cur["tdi"].append(tdi[i])
            cur["tdo"].append(tdo[i])
        nxt = TAP[st][tms[i]]
        if nxt == "CapDR":
            cur = {"tdi": [], "tdo": [], "path": []}
        if cur is not None:
            cur["path"].append(nxt)
        if st == "UpdDR" and cur is not None:
            scans.append(cur)
            cur = None
        st = nxt
    return scans


# ---------------------------------------------------------------------------------------------------------------
# IEEE 802.3 clause 22 management frame: 32 ones, ST 01, OP 10 (read) / 01 (write), PHYAD, REGAD, TA 10 (write) or
# Z0 (read), 16 data bits MSB first.  MDIO is taken on the rising MDC edge.
# ---------------------------------------------------------------------------------------------------------------
def mdio_decode(mdc, mdio):
    bits = [mdio[i] for i in range(1, len(mdc)) if mdc[i] and not mdc[i - 1]]
    out, k = [], 0
    num = lambda b: sum(x << (len(b) - 1 - i) for i, x in enumerate(b))  # noqa: E731
    while k + 64 <= len(bits):
        if bits[k:k + 32] != [1] * 32 or bits[k + 32:k + 34] != [0, 1]:
            k += 1
            continue
        op, phy, reg = num(bits[k + 34:k + 36]), num(bits[k + 36:k + 41]), num(bits[k + 41:k + 46])
        out.append({"op": {2: "read", 1: "write"}.get(op, op), "phy": phy, "reg": reg, "ta": bits[k + 46:k + 48],
                    "data": num(bits[k + 48:k + 64])})
        k += 64
    return out


# ---------------------------------------------------------------------------------------------------------------
# I2C (NXP UM10204) bus decoder and a controller waveform generator, both written here.
# ---------------------------------------------------------------------------------------------------------------
def i2c_bus_decode(scl, sda):
    """-> list of ('S',) | ('Sr',) | ('B', byte, acked) | ('P',) from a resolved wired-AND bus."""
    ev, bits, active = [], [], False
    for t in range(1, len(scl)):
        if scl[t] and scl[t - 1] and sda[t] != sda[t - 1]:
            if sda[t] == 0:
                ev.append(("Sr",) if active else ("S",))
                active, bits = True, []
            else:
                ev.append(("P",))
                active, bits = False, []
        elif active and scl[t] and not scl[t - 1]:
            bits.append(sda[t])
            if len(bits) == 9:
                ev.append(("B", sum(b << (7 - i) for i, b in enumerate(bits[:8])), bits[8] == 0))
                bits = []
    return ev


def i2c_controller_wave(addr, write_data, beat_cycles):
    """Per-cycle (scl, sda) a standards-conforming controller drives for START, address+W, data bytes, STOP.  The ACK
    beats release SDA (1).  Each bit: SCL low for the first quarter, high for the middle half, low again; SDA changes
    only while SCL is low."""
    q = beat_cycles // 4
    scl, sda = [], []

    def put(a, b, n):
        scl.extend([a] * n)
        sda.extend([b] * n)

    put(1, 1, 2 * q)
    put(1, 0, q)                                         # START: SDA falls while SCL is high
    byte_list = [(addr << 1) | 0] + list(write_data)
    for by in byte_list:
        for b in [(by >> (7 - i)) & 1 for i in range(8)] + [1]:
            put(0, b, q)
            put(1, b, 2 * q)
            put(0, b, q)
    put(0, 0, q)
    put(1, 0, q)
    put(1, 1, 2 * q)                                     # STOP: SDA rises while SCL is high
    return scl, sda


# ---------------------------------------------------------------------------------------------------------------
# SPI mode 0 controller (Motorola): CS_N low, data on MOSI changes after SCK falls, both sides sample on the rising edge.
# ---------------------------------------------------------------------------------------------------------------
def spi0_controller_wave(mosi_bytes, period, lead=8, tail=8):
    """Per-cycle (sck, cs_n, mosi) for one transfer."""
    sck, cs, mo = [], [], []

    def put(a, b, c, n):
        sck.extend([a] * n)
        cs.extend([b] * n)
        mo.extend([c] * n)

    put(0, 1, 0, lead)
    first = mosi_bytes[0] >> 7 if mosi_bytes else 0
    put(0, 0, first, period // 2)
    for bi, by in enumerate(mosi_bytes):
        for i in range(8):
            b = (by >> (7 - i)) & 1
            put(0, 0, b, period // 2) if (bi or i) else None
            put(1, 0, b, period // 2)
    put(0, 0, 0, period // 2)
    put(0, 1, 0, tail)
    return sck, cs, mo


def hdlc_encode(payload: bytes, stuff_tail=True) -> list[int]:
    """Opening flag, payload + FCS (low byte first, bits LSB first) with a zero after every five ones, closing flag.
    ISO 13239 stuffs the last five ones too (the closing flag follows); `stuff_tail=False` drops that final zero."""
    data = payload + bytes([crc16_x25(payload) & 255, crc16_x25(payload) >> 8])
    out, ones = [], 0
    for by in data:
        for i in range(8):
            b = (by >> i) & 1
            out.append(b)
            ones = ones + 1 if b else 0
            if ones == 5:
                out.append(0)
                ones = 0
    if not stuff_tail and out[-6:-1] == [1] * 5 and out[-1] == 0:
        out.pop()
    flag = [0, 1, 1, 1, 1, 1, 1, 0]
    return flag + out + flag
