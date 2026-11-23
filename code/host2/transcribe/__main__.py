"""CLI.  python -m transcribe trace TRACE.txt [--fs 60e6] [-o out.score]
        python -m transcribe crc FRAMES.txt [--len W]
        python -m transcribe demo-image IMAGE.json [--reply BYTE]
        python -m transcribe crc-image FRAMES.txt IMAGE.json --reply-hex HEX
TRACE.txt: a string of 0/1 characters (whitespace ignored), one per sample. FRAMES.txt: one hex frame per line."""
import argparse
import sys

from .crc_search import search_crc
from .infer import InferenceError, transcribe


def main(argv=None):
    ap = argparse.ArgumentParser(prog="transcribe")
    sub = ap.add_subparsers(dest="cmd", required=True)
    t = sub.add_parser("trace")
    t.add_argument("file")
    t.add_argument("--fs", type=float, default=60e6)
    t.add_argument("-o", "--out")
    c = sub.add_parser("crc")
    c.add_argument("file")
    c.add_argument("--len", type=int, default=None)
    demo = sub.add_parser("demo-image", help="export the resident Metronome v4 UART demo image")
    demo.add_argument("file", metavar="IMAGE.json")
    demo.add_argument("--reply", type=lambda value: int(value, 0), metavar="BYTE",
                      help="encode this byte in the learned format (decimal or 0x-prefixed)")
    crc_demo = sub.add_parser("crc-image", help="export the on-chip CRC check and reply demo")
    crc_demo.add_argument("frames", metavar="FRAMES.txt")
    crc_demo.add_argument("file", metavar="IMAGE.json")
    crc_demo.add_argument("--reply-hex", type=bytes.fromhex, required=True)
    a = ap.parse_args(argv)
    if a.cmd == "demo-image":
        from metronome2_tools.asm import assemble_text
        from metronome2_tools.image import build_image, write_image

        from .fw_stage1 import source

        try:
            program = assemble_text(source(framing=True, transmit=True, reply=a.reply), name="resident UART demo")
            write_image(build_image(program), a.file)
        except (OSError, ValueError) as e:
            ap.error(str(e))
        return 0
    if a.cmd == "crc-image":
        from pathlib import Path

        from metronome2_tools.asm import assemble_text
        from metronome2_tools.image import build_image, write_image

        from .fw_crc import source

        try:
            lines = Path(a.frames).read_text(encoding="utf-8").splitlines()
            frames = [bytes.fromhex(line) for line in lines if line.strip()]
            program = assemble_text(source(frames, a.reply_hex), name="CRC identification demo")
            write_image(build_image(program), a.file)
        except (OSError, ValueError) as e:
            ap.error(str(e))
        return 0
    if a.cmd == "trace":
        levels = [int(ch) for ch in open(a.file).read() if ch in "01"]
        try:
            r = transcribe(levels, a.fs)
        except InferenceError as e:
            print(f"error: {e}", file=sys.stderr)
            return 2
        print(f"classification: {r.classification.kind} ({r.classification.evidence})")
        if r.classification.bit_rate:
            print(f"manchester bit rate {r.classification.bit_rate:.1f} bit/s (score emission not implemented)")
        if r.score:
            for n in r.uart.notes:
                print("note:", n)
            if a.out:
                open(a.out, "w").write(r.score)
            else:
                print(r.score)
        return 0
    frames = [bytes.fromhex(ln.strip().replace(" ", "")) for ln in open(a.file) if ln.strip()]
    ms = search_crc(frames, a.len)
    if not ms:
        print("no catalogue CRC matches", file=sys.stderr)
        return 1
    for m in ms:
        print(f"# {m.name}, crc bytes {m.byteorder}-endian\n{m.decl()}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
