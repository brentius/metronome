"""Generate the formal-program BMC inputs from a compiled Score program.

    python gen_fv.py --tool-root ROOT --src ROOT --program uart_tx [--mutant NAME] --out DIR

ROOT is a source tree (e.g. the frozen v3 baseline) holding src/, code/scorec, code/score, code/host2, sim/reference.
Writes into DIR: fv_cfg_img.vh (configuration bytes -> constant bank, see rtl_fv/fv_cfg_bank.v), fv_seq.vh (the
non-configuration host writes the sequencer issues), image.json (the complete ordered image, for the record).
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path

HI_BASE_GAP = 18     # cycles between L0.CTL write and HOSTIN write before the symbolic extra delay (idle loop settled)
PROGRAMS = {
    # name: (score file under code/score/lib, role, pin binding, rate_hz)
    "uart_tx": ("uart_8n1.score", "sender", "tx=O8", 10e6),
    "uart_rx": ("uart_8n1.score", "receiver", "tx=P5", 3e6),
}
MUTANTS = {   # name -> (old, new) on the score text
    "none": None,
    "msb_first": ("bits lsb first", "bits msb first"),
    "stop_bit_low": ("bit(1)                     # stop bit", "bit(0)                     # stop bit"),
    "start_bit_high": ("bit(0)                     # start bit", "bit(1)                     # start bit"),
    "data7": ("data:u8", "data:u7"),      # (not compilable at 10 Mbaud: the compiler's own E-TIME check rejects it)
}
# image-level mutants: byte patches on the compiled host-write list, (address, old byte, new byte)
IMG_MUTANTS = {
    "img_mod7": (0x2002, 0x06, 0x07),            # beat 7 clk instead of 6: every frame edge lands 1 clk late per bit
    "img_stop_low": (0x2184, 0xFB, 0xF3),        # output LUT index 3 (idle / stop symbol) drives 0
}


def load(root: Path):
    for p in ("code/scorec", "code/score", "code/host2", "sim/reference"):
        sys.path.insert(0, str(root / p))
    import scorec  # noqa
    from metronome2_tools.image import host_writes  # noqa
    from metronome2_tools._md import M  # noqa
    return scorec, host_writes, M


def build(root: Path, program: str, mutant: str):
    scorec, host_writes, M = load(root)
    fname, role, pins, rate = PROGRAMS[program]
    text = (root / "code/score/lib" / fname).read_text()
    if MUTANTS.get(mutant):
        old, new = MUTANTS[mutant]
        assert old in text, f"mutant {mutant}: pattern not found"
        text = text.replace(old, new)
    c = scorec.compile_score(text, role, pins, rate_hz=rate)
    ws = host_writes(c.program)
    if mutant in IMG_MUTANTS:
        a0, old, new = IMG_MUTANTS[mutant]
        patched = []
        for a, d, n in ws:
            d = bytearray(d)
            if a <= a0 < a + len(d):
                assert d[a0 - a] == old, (mutant, hex(a0), d[a0 - a])
                d[a0 - a] = new
            patched.append((a, bytes(d), n))
        ws = patched
    return c, ws, M


def split_writes(ws, M, skip_prog=False):
    cfg_lo, cfg_bytes = 0x2000, 480
    cfg = bytearray(cfg_bytes)
    seq = []   # (addr, data) non-config, byte granular, image order
    prog_bytes = 0
    for addr, data, note in ws:
        for i, b in enumerate(data):
            a = addr + i
            if cfg_lo <= a < cfg_lo + cfg_bytes:
                cfg[a - cfg_lo] = b
            elif a < 0x1000:                      # program memory: every byte of every image word is written (zero bytes
                if not skip_prog:                 # too): the proof does not assume memory powers up as zero
                    seq.append((a, b, "prog"))
                    prog_bytes += 1
            elif a < 0x2000:
                raise SystemExit("data RAM preload not supported by this generator")
            else:
                seq.append((a, b, note))
    return bytes(cfg), seq


def emit(out: Path, root: Path, program: str, mutant: str):
    c, ws, M = build(root, program, mutant)
    n, ncfg = emit_writes(out, ws, M, hostin=True, skip_prog=False)
    (out / "image.json").write_text(json.dumps({
        "program": program, "mutant": mutant, "mas": c.mas, "report": c.report,
        "writes": [[hex(a), d.hex(), nt] for a, d, nt in ws]}, indent=1))
    return n, ncfg


def emit_writes(out: Path, ws, M, hostin: bool, skip_prog: bool):
    """Write fv_cfg_img.vh and fv_seq.vh for an ordered host-write list.  hostin: append the HOSTIN row whose data is
    the symbolic payload (rtl_fv/fv_host.v); skip_prog: program bytes are preloaded by the testbench instead."""
    cfg, seq = split_writes(ws, M, skip_prog)
    out.mkdir(parents=True, exist_ok=True)
    (out / "fv_cfg_img.vh").write_text(
        "localparam [8*BYTES-1:0] CFG_IMG = {8*BYTES{1'b0}} | 3840'h" + cfg[::-1].hex() + ";" + chr(10))
    rows = [(a, b, 0 if n == "prog" else 3) for a, b, n in seq]
    if hostin:
        rows.append((M.HOST_MAP["CTRL_BASE"] + 4, 0, HI_BASE_GAP))   # CTRL.HOSTIN; data = symbolic payload
    n = len(rows)
    addr = "".join(f"{a:04x}" for a, _, _ in reversed(rows))
    data = "".join(f"{b:02x}" for _, b, _ in reversed(rows))
    gaps = "".join(f"{g:04x}" for _, _, g in reversed(rows))
    (out / "fv_seq.vh").write_text(
        f"localparam integer NSEQ = {n};" + chr(10) + f"localparam HAS_HI = {int(hostin)};" + chr(10) +
        f"localparam [{16*n-1}:0] SEQ_ADDR = {16*n}'h{addr};" + chr(10) +
        f"localparam [{8*n-1}:0] SEQ_DATA = {8*n}'h{data};" + chr(10) +
        f"localparam [{16*n-1}:0] SEQ_GAP = {16*n}'h{gaps};" + chr(10))
    return n, sum(1 for x in cfg if x)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--tool-root", required=True)
    ap.add_argument("--program", default="uart_tx")
    ap.add_argument("--mutant", default="none")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    print(emit(Path(a.out), Path(a.tool_root), a.program, a.mutant))
