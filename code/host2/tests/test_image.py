"""Image order, host-map addresses, JSON/SPI round trips, disassembly of an image and the command line."""
import json

from common import *
from metronome2 import regs
from metronome2_tools import asm as asm_mod
from metronome2_tools import disasm as disasm_mod
from metronome2_tools.image import (apply_writes, build_image, image_to_spi, min_write_gap_cycles, read_image,
                                    spi_streams, write_image)
from test_asm import CFG


def notes(writes):
    return [n for _, _, n in writes]


def test_write_order_run_last_enable_after_thread_config_lines_start_late():
    prog = assemble_text(CFG)
    w = host_writes(prog)
    n = notes(w)
    assert n[-1] == "CTRL.RUN"
    assert n.index("T4.CFG") < n.index("T4.PC") < n.index("T4.EN")
    assert n.index("S1.REWIND") > n.index("S1.MODE") and n.index("S1.REWIND") > n.index("S1.START")   # applies at rewind
    first_prog = min(i for i, x in enumerate(n) if x.startswith("core"))
    assert first_prog == 0 and all(not x.startswith("core") for x in n[n.index("LF0.POLY"):])
    assert n.index("L2.CTL") > n.index("T4.EN") and n.index("L2.CTL") > n.index("L2.LUT1")           # lines start late
    assert n.index("L2.HOLD") > n.index("L2.PINS")


def test_every_write_lands_on_a_mapped_address_of_the_right_kind():
    for name in ("uart_tx", "eth_tx", "spi_target"):
        for addr, data, note in host_writes(example(name)):
            for i in range(len(data)):
                d = regs.decode(addr + i)
                assert d is not None, (name, note, hex(addr + i))
                assert d[0] in ("prog", "data") or regs.is_config(addr + i) or d[0] in ("CTRL", "LRT", "TRT", "SRT")


def test_program_words_are_little_endian_bytes_of_the_model_word():
    prog = example("eth_tx")
    chip = Chip()
    load(chip, prog)
    assert chip.cores[0].prog[0] == prog.code[0][0].word


def test_json_image_round_trip_and_replay(tmp_path):
    prog = example("spi_target")
    img = build_image(prog)
    p = tmp_path / "x.json"
    write_image(img, p)
    back = read_image(p)
    assert back == json.loads(p.read_text())
    ref = apply_writes([(a, d) for a, d, _ in host_writes(prog)])
    assert apply_writes(image_to_spi_decoded(back)) == ref


def image_to_spi_decoded(img):
    from metronome2_tools.image import image_writes
    return image_writes(img)


def test_spi_frames_cover_the_same_bytes_with_and_without_coalescing():
    prog = example("uart_tx")
    w = [(a, d) for a, d, _ in host_writes(prog)]
    for kw in ({}, {"coalesce": False}, {"max_frame": 5}):
        frames = spi_streams(w, **kw)
        assert all(f[0] == 0x02 for f in frames)
        got = {}
        for f in frames:
            for i, b in enumerate(f[3:]):
                got[((f[1] << 8) | f[2]) + i] = b
        assert got == apply_writes(w)


def test_d24_spacing_rests_on_the_spi_link_rate():
    assert min_write_gap_cycles(16) == 128
    assert min_write_gap_cycles(32) == 256


def test_disassembling_an_image_gives_assemblable_source_with_the_same_words():
    prog = example("uart_tx")
    text = disasm_mod.disassemble_image(build_image(prog))
    again = assemble_text(text)
    assert again.words(0) == prog.words(0)


def test_command_line_assemble_check_and_disassemble(tmp_path, capsys):
    out = tmp_path / "u.json"
    assert asm_mod.main([str(EXAMPLES / "uart_tx.mas"), "-o", str(out), "-l"]) == 0
    assert out.exists() and "idle" in capsys.readouterr().out
    assert disasm_mod.main([str(out)]) == 0
    bad = tmp_path / "bad.mas"
    bad.write_text(".line 0\n period 4\n ctl run\n.end\n.thread 0\n trigger L0.BEAT\n start t\n.end\n"
                   ".core 0\nt: nop\n nop\n nop\n nop pause goto t\n")
    out2 = tmp_path / "bad.json"
    assert asm_mod.main([str(bad), "-o", str(out2)]) == 2 and not out2.exists()          # check error: no image
    assert asm_mod.main([str(bad), "-o", str(out2), "--no-check"]) == 0 and out2.exists()
    broken = tmp_path / "broken.mas"
    broken.write_text("nonsense -> nowhere\n")
    assert asm_mod.main([str(broken)]) == 1
