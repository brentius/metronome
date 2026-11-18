import subprocess
import sys
from itertools import chain, repeat
from pathlib import Path
from random import Random

import pytest

from metronome2 import Chip
from metronome2_tools.asm import assemble_text
from metronome2_tools.image import host_writes, image_writes, read_image, spi_streams
from test_transcribe import Codec, capture, hidden_text, parse
from transcribe.fw_stage1 import source


@pytest.fixture
def demo_image(tmp_path):
    host = Path(__file__).resolve().parents[2] / "host2"
    destination = tmp_path / "resident-uart.json"
    result = subprocess.run(
        [sys.executable, "-m", "transcribe", "demo-image", str(destination)],
        cwd=host,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr
    return read_image(destination)


def test_demo_image_exports_the_resident_uart_spi_load(demo_image):
    qualified_program = assemble_text(source(5, framing=True, transmit=True))
    expected = [(address, data) for address, data, _ in host_writes(qualified_program)]
    assert image_writes(demo_image) == expected
    assert spi_streams(image_writes(demo_image), coalesce=False) == [
        bytes((0x02, address >> 8, address & 0xFF)) + data for address, data in expected
    ]
    assert demo_image["clock_hz"] == 60_000_000
    assert [(entry["core"], len(entry["words"])) for entry in demo_image["program"]] == [(0, 243), (1, 233)]


def test_documented_uart_burst_replays_from_nonzero_sram(demo_image):
    chip = Chip()
    rng = Random(4)
    chip.mem.data[:] = rng.randbytes(len(chip.mem.data))
    for core in chip.cores:
        core.prog[:] = [rng.getrandbits(64) for _ in core.prog]
    for _ in range(3):
        chip.step(0x02, 1 << 5)
    for address, data in image_writes(demo_image):
        chip.backdoor_write(address, data)

    rate = 115_200
    payload = list(bytes.fromhex("A5 5C 38 E7 13 F4 89 27")) * 4
    uart = hidden_text(rate)
    stimulus = capture(uart, payload, rate)
    clock = int(demo_image["clock_hz"])
    output = []
    for level in chain(repeat(1, clock // 1000), stimulus, repeat(1, clock // 1000)):
        sending = chip.lines[0].RUN
        uo, _, _ = chip.step(0x02, level << 5)
        if sending or output:
            output.append((uo >> 2) & 1)
        if chip.backdoor_read(0x2406) & 2:
            break
    else:
        pytest.fail("firmware did not report completion")

    assert chip.backdoor_read(0x2405) == 1
    assert chip.backdoor_read(0x2408) == 0
    assert chip.contract_violations == []
    rate_result = bytes(chip.backdoor_read(addr) for addr in range(0x1710, 0x1716))
    framing = bytes(chip.backdoor_read(addr) for addr in range(0x1716, 0x171B))
    learned_rate = clock * 32 / int.from_bytes(rate_result[2:4], "little")
    assert rate_result[:2] == bytes((1, 1))
    assert learned_rate == pytest.approx(rate, rel=0.005)
    assert framing == bytes((1, 8, 0, 11, 1))
    output.extend([1] * (4 * clock // rate))
    replay = Codec(parse(uart)).decode("receiver", {"tx": output})
    assert replay.ok, replay.notes
    assert [value for field, value in replay.events if field == "data"] == payload[:11]
