"""Extracts the section 16 score examples from the normative spec text."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SPEC = ROOT / "wiki/SPEC_V2_SCORE.md"


def spec_examples():
    """The five score examples of spec section 16, in order: uart, i2c, spi, ethernet, tether."""
    txt = SPEC.read_text(encoding="utf-8")
    sec = txt.split("## 16. Examples")[1].split("## 17.")[0]
    blocks = re.findall(r"```\n(.*?)```", sec, re.S)
    assert len(blocks) == 5, len(blocks)
    return blocks
