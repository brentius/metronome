"""Identify one of three CRC profiles and transmit a new frame on O8.

The input is three already decoded records with a known payload length and
frame boundary. They and a new payload arrive as ordinary data SRAM writes
in the image. The firmware tests complete codewords for zero residue, then
uses the selected profile to append a check field and send an 8N1 reply.
HOST.OUT is the profile mask (1 SMBUS, 2 CCITT-FALSE, 4 ARC). Transmission
requires exactly one match. No host action is needed once the image runs.
"""

from __future__ import annotations

REPLY = 0x100
CLOCKS_PER_BIT = 120


def source(frames: list[bytes], reply: bytes) -> str:
    """Build an assembly image for three fixed-length training records."""
    size = len(reply)
    if not 1 <= size <= 32:
        raise ValueError("CRC demo requires a payload of 1 through 32 bytes")
    if len(frames) != 3 or len(set(frames)) != 3:
        raise ValueError("CRC demo requires three distinct training frames")
    if len({len(frame) for frame in frames}) != 1 or len(frames[0]) not in (size + 1, size + 2):
        raise ValueError("training frames must have the reply payload length and a one- or two-byte check field")
    trailer = len(frames[0]) - size
    code = [
        ".clock 60e6",
        ".lfsr 0 poly=0x1021 width=16",
        ".lfsr 1 poly=0x8005 width=16",
        f".data 0 {' '.join(str(byte) for frame in frames for byte in frame)}",
        f".data {REPLY} {' '.join(map(str, reply))}",
        ".line 0", "    inc 1", f"    mod {CLOCKS_PER_BIT}", ".end",
        ".out 8", "    line 0", "    sel 0 0 0", "    lut b0 ^ 1", ".end",
        ".thread 0", "    core 0", "    trigger ALWAYS", "    start main", ".end",
        ".thread 1", "    core 0", "    trigger L0.BEAT", "    start tx_byte", ".end",
        ".core 0", "main:",
    ]

    def emit(*instructions):
        code.extend(line if line.endswith(":") else "        " + line for line in instructions)

    def pointer(address):
        emit(f"#{address >> 8} -> P0.AH", f"#{address & 255} -> P0.AL")

    profiles = (1,) if trailer == 1 else (2, 4)
    emit("ZERO -> R3", "ZERO -> CNT0.HI, ZERO -> CNT1.HI", f"goto train_{profiles[0]}")
    for index, mask in enumerate(profiles):
        next_stage = f"train_{profiles[index + 1]}" if index + 1 < len(profiles) else "select"
        emit(f"train_{mask}:")
        pointer(0)
        emit("#3 -> CNT1.LO", f"#{size + trailer} -> R1", f"goto frame_{mask}", f"reply_{mask}:")
        pointer(REPLY)
        emit("#3 -> FLAGS.SET", f"#{size} -> R1", f"frame_{mask}:", "R1 -> CNT0.LO")

        if mask == 1:
            emit("ZERO -> ACC.LD", "crc8_read:", "pause goto crc8_read ifnot P0.RDY",
                 "P0.D -> ACC.XOR, ZERO -> P0.R", "#8 -> CNT2.LO", "crc8_shift:",
                 "ACC -> ACC.ADD, ZERO -> CNT2.DEC", "when ACC.C ? #7 -> ACC.XOR",
                 "pause goto crc8_shift ifnot CNT2.Z", "ZERO -> CNT0.DEC",
                 "goto crc8_read ifnot CNT0.Z")
        else:
            lf = "LF0" if mask == 2 else "LF1"
            init = "#255" if mask == 2 else "ZERO"
            emit(f"{init} -> {lf}.B0", f"{init} -> {lf}.B1", f"#{16 if mask == 2 else 0} -> SH0.CFG",
                 f"read_{mask}:", f"pause goto read_{mask} ifnot P0.RDY",
                 "P0.D -> SH0.LD, ZERO -> P0.R", f"shift_{mask}:",
                 f"SH0.O -> {lf}.ST, ZERO -> SH0.SH", f"pause goto shift_{mask} ifnot SH0.DONE",
                 "ZERO -> CNT0.DEC", f"goto read_{mask} ifnot CNT0.Z",
                 f"{lf}.B0 -> ACC.LD", f"{lf}.B1 -> ACC.OR")

        emit(f"goto append_{mask} if F3", f"goto {next_stage} ifnot ACC.Z", "ZERO -> CNT1.DEC",
             f"goto frame_{mask} ifnot CNT1.Z", "R3 -> ACC.LD", f"#{mask} -> ACC.OR",
             f"ACC -> R3, goto {next_stage}", f"append_{mask}:")
        if mask == 1:
            emit("ACC -> P0.W")
        elif mask == 2:
            # The normal CRC state is the bit reversal of the LFSR state.
            # Sending high byte first therefore reverses low byte, then high.
            emit("ZERO -> SH0.CFG, #16 -> SH1.CFG")
            for byte in range(2):
                emit(f"LF0.B{byte} -> SH0.LD", f"reverse_{byte}:", "SH0.O -> SH1.SH, ZERO -> SH0.SH",
                     f"pause goto reverse_{byte} ifnot SH0.DONE", "SH1.D -> P0.W")
        else:
            emit("LF1.B0 -> P0.W", "LF1.B1 -> P0.W")
        emit("goto send")

    emit("select:", "R3 -> ACC.LD")
    for mask in profiles:
        emit(f"#{mask} -> ACC.CMP", f"goto reply_{mask} if ACC.Z")
    emit("R3 -> HOST.OUT, ZERO -> T.STOP pause goto select", "send:")
    pointer(REPLY)
    emit(f"#{size + trailer} -> CNT1.LO", "ZERO -> SH0.CFG", "#1 -> L0.CTL", "ZERO -> T.STOP pause goto send",
         "tx_byte:", "pause goto tx_done if CNT1.Z", "pause goto tx_byte ifnot P0.RDY",
         "P0.D -> SH0.LD, ZERO -> P0.R, #1 -> L.DBIT", "pause goto tx_bit",
         "tx_bit:", "goto tx_stop if SH0.DONE", "SH0.O -> ACC.LD, ZERO -> SH0.SH",
         "#1 -> ACC.XOR", "ACC -> L.DBIT pause goto tx_bit",
         "tx_stop:", "ZERO -> L.DBIT, ZERO -> CNT1.DEC pause goto tx_byte",
         "tx_done:", "R3 -> HOST.OUT, ZERO -> L0.CTL, ZERO -> T.STOP pause goto tx_byte")
    return "\n".join(code) + "\n"
