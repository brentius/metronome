import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path[:0] = [str(ROOT / "code/score"), str(ROOT / "code/tests/checkers")]

import pytest  # noqa: E402

from spec_blocks import spec_examples  # noqa: E402


@pytest.fixture(scope="session")
def examples():
    from score import parse
    names = ["uart", "i2c", "spi", "ethernet", "tether"]
    return dict(zip(names, (parse(b) for b in spec_examples())))
