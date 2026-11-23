"""pytest entry: co-simulate the Metronome RTL against third-party device models.

    source code/tools/env.sh
    python -I code/tests/vendor_models/fetch_vendor.py
    python -m pytest code/tests/vendor_models -q

Each test builds the full-chip RTL (Icarus, IHP SRAM behavioural models) with one device model wired to
the pins and drives the chip over its SPI host link, exactly as code/tests/lockstep_v2 does.  The last two
tests are the PS/2 blind challenge (first-party spec-derived peer) and a stand-alone reproduction of a
third-party model defect (FINDINGS.md F1).
"""
from __future__ import annotations

import shutil
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
VENDOR = ROOT / "build" / "vendor"

sys.path.insert(0, str(ROOT / "code" / "tests" / "lockstep_v2"))
sys.path.insert(0, str(HERE))

FLASH = VENDOR / "w25q128jv" / "W25Q128JVxIM.v"
EEPROM = VENDOR / "antikernel" / "models" / "i2c_eeprom" / "24LC256.v"

pytestmark = pytest.mark.skipif(shutil.which("iverilog") is None,
                                reason="needs iverilog (source code/tools/env.sh)")

SEEN = {}


def _chip_sources():
    import os
    from rtl_sources import SRC, rtl_files
    # The IHP SRAM macro models are not under test here; their behavioural arrays are much faster and
    # zero their own contents (code/tests/lockstep_v2: LOCKSTEP_BEHAV_SRAM=1).  Set VENDOR_IHP_SRAM=1 to
    # run against the macro models instead.
    ihp = os.environ.get("VENDOR_IHP_SRAM") == "1"
    files, defines = rtl_files(ihp_sram=ihp)
    return files, defines, SRC


def _run(top: str, module: str, tag: str, extra: list[Path], note: str, preload=None):
    """Build the bench (full-chip RTL + device model) and run it; `preload(build)` writes model files."""
    from cocotb_tools.runner import get_runner
    files, defines, src = _chip_sources()
    build = HERE / "sim_build" / tag
    runner = get_runner("icarus")
    runner.build(sources=list(files) + [Path(f) for f in extra] + [HERE / f"tb_{tag}.v"],
                 hdl_toplevel=top, build_dir=build, includes=[src], defines=defines,
                 timescale=("1ns", "1ps"), always=True)
    if preload is not None:
        preload(build)
    xml = build / f"results_{tag}.xml"
    runner.test(hdl_toplevel=top, test_module=module, build_dir=build, test_dir=HERE,
                results_xml=str(xml))
    root = ET.parse(xml).getroot()
    fails = root.findall(".//failure") + root.findall(".//error")
    assert not fails, f"{note}: {[f.get('message') for f in fails]}"


def _skip_missing(path: Path, script: str):
    if not path.exists():
        pytest.skip(f"third-party model missing ({path}); run {script}")


def _write_flash_preload(_build: Path):
    """The W25Q model reads its arrays from the run directory (its own preload mechanism).

    The cocotb run happens in the test directory, so the files go there; `.gitignore` keeps them out of
    the tree.  NUM_PAGES=256 in tb_spi_flash.v, so MEM.TXT needs 256*256 = 65536 bytes: all 0xFF (erased).
    """
    mem = HERE / "MEM.TXT"
    if not mem.exists() or mem.stat().st_size != 65536 * 3:
        mem.write_text("FF\n" * 65536, encoding="ascii")
    for name in ("SECSI.TXT", "SFDP.TXT", "SREG.TXT"):
        dst = HERE / name
        if not dst.exists():
            shutil.copyfile(FLASH.parent / name, dst)


def test_spi_flash_read_id_program_read():
    """Winbond W25Q128JV model: JEDEC ID, status, WREN-gated page program, WIP, read-back."""
    _skip_missing(FLASH, "python -I code/tests/vendor_models/fetch_vendor.py")
    _run("tb_spi_flash", "flash_test", "spi_flash", [FLASH], "W25Q128JV", preload=_write_flash_preload)


def test_i2c_eeprom_write_poll_read():
    """Microchip 24LC256 model: page write, ack polling across its write cycle, read-back, NACK controls."""
    _skip_missing(EEPROM, "python -I code/tests/vendor_models/fetch_vendor.py")
    _run("tb_i2c_eeprom", "eeprom_test", "i2c_eeprom", [EEPROM], "24LC256")


def test_ps2_keyboard_receive():
    """Blind challenge: PS/2 receive (assembly and Score) against an independently written device peer."""
    _run("tb_ps2", "ps2_test", "ps2", [HERE / "ps2_keyboard_peer.v"], "PS/2")


def test_24lc256_ack_poll_quirk_reproduced():
    """F1 (FINDINGS.md): pin the model's spurious write cycle after an acknowledge-poll transaction.

    This is a one-second run of the model alone; it keeps the finding reproducible and stops the co-simulation
    from silently depending on a behaviour the model should not have.
    """
    import subprocess
    _skip_missing(EEPROM, "python -I code/tests/vendor_models/fetch_vendor.py")
    build = HERE / "sim_build" / "repro_24lc256"
    build.mkdir(parents=True, exist_ok=True)
    vvp = build / "repro.vvp"
    subprocess.run(["iverilog", "-g2012", "-o", str(vvp), str(HERE / "repro_24lc256.v"), str(EEPROM)],
                   check=True, capture_output=True)
    out = subprocess.run(["vvp", str(vvp)], check=True, capture_output=True, text=True).stdout
    lines = {ln.split()[0]: ln for ln in out.splitlines() if ln.split()}
    assert "WriteActive=1" in lines["PAGE"], out                  # the data write starts at the STOP
    assert "WriteActive=0" in lines["IDLE"], out                  # and finishes after tWC
    assert lines["POLL"].endswith("ack=0"), out                   # the poll is acknowledged, as on silicon
    assert "WriteActive=1" in lines["AFTER_POLL"], out            # F1: a second write cycle starts
    assert lines["POLL2"].endswith("ack=1"), out                  # F1: and refuses the next poll
