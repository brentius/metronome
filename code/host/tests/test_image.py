import json
import subprocess
import sys
from pathlib import Path

from metronome_tools import image as I
from metronome_tools._md import M
from metronome_tools.asm import assemble_file, assemble_text
from metronome_tools.disasm import disassemble_image

HOST = Path(__file__).resolve().parents[1]
EX = HOST / "examples"


def test_json_image_structure(tmp_path):
    prog = assemble_file(EX / "uart_tx.mas")
    img = I.build_image(prog)
    out = tmp_path / "x.json"
    I.write_image(img, out)
    back = I.read_image(out)
    assert back["format"] == "metronome-image" and back["machine_version"] == M.VERSION
    assert back["writes"][-1]["note"] == "CTRL.RUN"
    words = [int(w, 16) for w in back["program"][0]["words"]]
    assert words == [prog.code[0][a].word for a in sorted(prog.code[0])]
    # the program words appear in the writes too, little-endian, at core 0's base
    first = back["writes"][0]
    assert first["addr"] == M.HOST_MAP["PROG_BASE"]
    assert bytes.fromhex(first["data"]) == b"".join(w.to_bytes(8, "little") for w in words)


def test_spi_frames_roundtrip_and_coalescing():
    prog = assemble_file(EX / "uart_tx.mas")
    w = I.host_writes(prog)
    frames = I.spi_streams(w)
    assert all(f[0] == 0x02 for f in frames)
    assert len(frames) < len(w)                               # contiguous registers merged
    assert I.apply_writes(I.decode_spi(frames)) == I.apply_writes(w)
    assert I.apply_writes(I.decode_spi(I.spi_streams(w, coalesce=False))) == I.apply_writes(w)
    small = I.spi_streams(w, max_frame=4)
    assert max(len(f) - 3 for f in small) <= 4
    assert I.apply_writes(I.decode_spi(small)) == I.apply_writes(w)
    # RUN is the very last byte clocked in
    assert I.decode_spi(frames)[-1] == (M.HOST_MAP["CTRL_BASE"], b"\x01")


def test_frame_layout_and_read_helpers():
    assert I.spi_write_frame(0x2401, b"\xAA\xBB") == bytes([0x02, 0x24, 0x01, 0xAA, 0xBB])
    assert I.spi_read_frame(0x2407, 2) == bytes([0x03, 0x24, 0x07, 0, 0])
    assert I.spi_read_result(bytes([0, 0, 0, 0xA1, 0x55]), 2) == bytes([0xA1, 0x55])


def test_disassemble_image_reassembles(tmp_path):
    prog = assemble_file(EX / "uart_rx.mas")
    text = disassemble_image(I.build_image(prog))
    again = assemble_text(text)
    assert again.words(0) == prog.words(0)


def test_cli_asm_and_disasm(tmp_path):
    out = tmp_path / "blink.json"
    env_cwd = str(HOST)
    r = subprocess.run([sys.executable, "-m", "metronome_tools.asm", str(EX / "blink.mas"), "-o", str(out)],
                       cwd=env_cwd, capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    assert json.loads(out.read_text())["format"] == "metronome-image"
    r = subprocess.run([sys.executable, "-m", "metronome_tools.disasm", str(out)], cwd=env_cwd,
                       capture_output=True, text=True)
    assert r.returncode == 0 and "ACC -> E.SYM" in r.stdout


def test_cli_rejects_bad_program(tmp_path):
    bad = tmp_path / "bad.mas"
    bad.write_text("s: nop\n goto s\n")
    out = tmp_path / "bad.json"
    r = subprocess.run([sys.executable, "-m", "metronome_tools.asm", str(bad), "-o", str(out)], cwd=str(HOST),
                       capture_output=True, text=True)
    assert r.returncode == 2 and "burst rule" in r.stderr and not out.exists()
    r = subprocess.run([sys.executable, "-m", "metronome_tools.asm", str(bad), "--no-check", "-o", str(out)],
                       cwd=str(HOST), capture_output=True, text=True)
    assert r.returncode == 0 and out.exists()
