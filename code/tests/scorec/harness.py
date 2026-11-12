"""Shared harness: compile a score role, load the image into the v2 cycle-level model, drive pins, decode with the
reference codec (a black box: the codec is the oracle, the compiler never imports it)."""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
for p in (ROOT / "code" / "scorec", ROOT / "code" / "score", ROOT / "code" / "host2", ROOT / "sim" / "reference"):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))

from metronome2 import Chip, m  # noqa: E402
from metronome2_tools.image import host_writes  # noqa: E402

import scorec  # noqa: E402
from score import Codec, parse  # noqa: E402  (the oracle; tests only)

HM = m.HOST_MAP
IDLE = 0x02            # ui_in: host-link CS_N high


def spec_block(i):
    """The i-th section 16 example of the normative spec (uart, i2c, spi, ethernet, tether)."""
    import re
    txt = (ROOT / "wiki" / "SPEC_V2_SCORE.md").read_text(encoding="utf-8")
    sec = txt.split("## 16. Examples")[1].split("## 17.")[0]
    return re.findall(r"```\n(.*?)```", sec, re.S)[i]


def load(chip, prog):
    for addr, data, _ in host_writes(prog):
        chip.backdoor_write(addr, data)


def new_chip(compiled):
    chip = Chip()
    load(chip, compiled.program)
    return chip


def pins_in(p_levels: dict):
    """{P index: level} -> (ui_in, uio_in)."""
    ui, uio = IDLE, 0
    for k, v in p_levels.items():
        if v:
            if k < 8:
                uio |= 1 << k
            else:
                ui |= 1 << (k - 8 + 3)
    return ui, uio


def out_level(o, uo, uio_out, uio_oe, pulled_up=False):
    """Level on output pin O<o>: (value, driven)."""
    if o < 8:
        d = (uio_oe >> o) & 1
        return ((uio_out >> o) & 1), d
    return (uo >> (o - 8 + 2)) & 1, 1


def hostin(chip, byte):
    chip.backdoor_write(HM["CTRL_BASE"] + 4, bytes([byte]))


def hoststat(chip):
    return chip.backdoor_read(HM["CTRL_BASE"] + 5, 1)[0] if hasattr(chip, "backdoor_read") else None


def stream_reg(chip, k, reg, value, n):
    from metronome2_tools.image import stream_addr
    chip.backdoor_write(stream_addr(k, reg), int(value).to_bytes(n, "little"))


def stream_rewind(chip, k):
    from metronome2_tools.image import srt_addr
    chip.backdoor_write(srt_addr(k, "CTL"), b"\x01")


def send_frame_go(chip, body: bytes, base=0, settle=40):
    """Host side of 'frame from RAM': write the body, set the stream length, rewind, then write the go byte."""
    chip.backdoor_write(HM["DATA_BASE"] + base, body)
    stream_reg(chip, 0, "LEN", len(body), 2)
    stream_rewind(chip, 0)
    for _ in range(settle):
        chip.step(IDLE, 0)
    hostin(chip, 0x01)
