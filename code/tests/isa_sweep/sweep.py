"""Exhaustive single-instruction sweep (V3 plan 7.9): the RTL against the v2 cycle-level model, state compared every cycle.

    python sweep.py --root SRC_ROOT --out DIR [--group exhaustive|tstop|random|all] [--quick]

SRC_ROOT: a tree with src/, sim/reference/, code/host2, code/md2, code/tests/formal_programs (e.g. the frozen v3
baseline snapshot, or the v3 tree).  The sweep never edits it.

The 64-bit instruction word has 2^64 encodings, so it cannot be enumerated; one move (guard 2 bits, source 6, destination
6) has 2^14 = 16,384.  The sweep therefore enumerates, per move slot (3 slots):
  exhaustive   every (guard, source, destination) in each slot (all 4 guards x 64 sources x 64 destinations, including
               out-of-table indices, which SPEC 9a.1 gives defined behaviour), the other two slots idle, cond = TRUE,
               one instruction per burst, one thread, after a preamble that loads distinguishable values into every
               unit.  Destination T.STOP (disables the thread, so it would end the batch) is excluded here ...
  tstop        ... and swept separately: 4 guards x 64 sources, six threads per batch, one T.STOP word per thread.
  cond         slot 0, all 4 guards x 64 sources x 64 cond values with destination ACC.LD (guard conditions, incl. the
               out-of-table cond indices).
  random       seeded fully random 64-bit words (all fields, jumps, pause, out-of-table jump conditions) in batches:
               a stratified SAMPLE of the 2^64 space, for cross-slot interactions (write-group conflicts, same-source
               fan-out, jump + move).  Destination T.STOP is replaced by NULL.
Per cycle both sides report pins and architectural state (ACC, R0-3, flags, shifters, counters, LFSRs, pointer, stream
positions, thread PC/EN/READY/..., line phase/staged/committed, host mailbox, conflict, memory hazard); the traces must
be identical.  The RTL uses the formal preload structure (constant configuration bank, write sequencer for the
runtime start writes, program words loaded into the behavioural program array by the testbench), see
code/tests/formal_programs/rtl_fv/ and its README for the equivalence assumptions.
Evidence class: RTL-simulated, verified against the reference model, for the enumerated or sampled encodings only.
"""
from __future__ import annotations

import argparse
import json
import os
import random
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
FP = HERE.parent / "formal_programs"
sys.path.insert(0, str(FP))

IDLE_SLOT = (3, 0, 0)          # guard never, src ZERO, dst NULL
PREAMBLE_NAMES = None


def load_tools(root: Path):
    for p in ("code/host2", "sim/reference", "code/md2"):
        sys.path.insert(0, str(root / p))
    global M, asm_text, host_writes, Chip
    from metronome2_tools._md import M  # noqa
    from metronome2_tools.asm import assemble_text as asm_text  # noqa
    from metronome2_tools.image import host_writes  # noqa
    from metronome2 import Chip  # noqa


def pack(moves, cond=0, jmode=0, jcond=0, imm=0, pause=1):
    w = pause | (jmode << 1) | (imm << 3) | (cond << 11) | (jcond << 59)
    for i in range(3):
        g, s, d = moves[i] if i < len(moves) else IDLE_SLOT
        b = 17 + 14 * i
        w |= g << b | s << (b + 2) | d << (b + 8)
    return w


def imm_move(dst, imm):
    return pack([(0, M.SRC_ID["IMM"], M.DST_ID[dst])], imm=imm)


def preamble():
    ws = []
    for dst, v in [("ACC.LD", 0x5A), ("R0", 0x11), ("R1", 0x22), ("R2", 0x33), ("R3", 0x44), ("CNT0.LO", 0x03),
                   ("CNT0.HI", 0x01), ("CNT1.LO", 0x07), ("SH0.CFG", 0x08), ("SH0.LD", 0xA6), ("SH1.CFG", 0x17),
                   ("SH1.LD", 0x6B), ("LF0.B0", 0x5D), ("LF0.B1", 0x21), ("LF0.B2", 0xE3), ("LF0.B3", 0x9C),
                   ("LF1.B0", 0x31), ("LF1.B1", 0xA7), ("P0.AL", 0x08), ("P0.AH", 0x00), ("L.SYM", 0x05)]:
        ws.append(imm_move(dst, v))
    for k in (1, 3, 5, 6, 10, 15):
        ws.append(imm_move("FLAGS.SET", k))
    return ws


def tail(addr):
    return pack([], jmode=1, imm=addr, pause=1)       # pause goto self


def dmem_image():
    return bytes((i * 37 + (i >> 3) * 11 + 5) & 0xFF for i in range(2048))


# ---- the compared state: one list drives both the testbench and the model -----------------------------------------
def fields():
    f = [("uo", 8, "uo_out", lambda c, o: o[0]), ("uio", 8, "uio_out", lambda c, o: o[1]),
         ("oe", 8, "uio_oe", lambda c, o: o[2]),
         ("acc", 8, "dut.u_acc.a", lambda c, o: c.acc.A), ("accz", 1, "dut.u_acc.z", lambda c, o: c.acc.Z),
         ("accc", 1, "dut.u_acc.c", lambda c, o: c.acc.C), ("accn", 1, "dut.u_acc.n", lambda c, o: c.acc.N),
         ("regs", 32, "dut.u_acc.r", lambda c, o: sum(v << (8 * i) for i, v in enumerate(c.acc.R))),
         ("fl", 16, "dut.fl", lambda c, o: c.flags.F)]
    for k in range(2):
        f += [(f"sh{k}d", 8, f"dut.g_sh[{k}].u.dr", lambda c, o, k=k: c.sh[k].D),
              (f"sh{k}c", 4, f"dut.g_sh[{k}].u.cnt", lambda c, o, k=k: c.sh[k].CNT)]
    for k in range(3):
        f.append((f"cn{k}", 16, f"dut.g_cn[{k}].u.v", lambda c, o, k=k: c.cnt[k].V))
    for k in range(2):
        f.append((f"lf{k}", 32, f"dut.g_lf[{k}].u.s", lambda c, o, k=k: c.lf[k].S))
    f.append(("ptr", 11, "dut.u_mem.ptr", lambda c, o: c.mem.ptr.PTR))
    f.append(("spos", 24, "dut.s_pos", lambda c, o: c.mem.streams[0].POS | (c.mem.streams[1].POS << 12)))
    for t in range(6):
        for rn, mn, w in (("pc", "PC", 8), ("en", "EN", 1), ("ready", "READY", 1), ("running", "RUNNING", 1),
                          ("armed", "ARMED", 1), ("late", "LATE", 1), ("ovr", "OVR", 1)):
            f.append((f"t{t}{rn}", w, f"dut.g_thr[{t}].u.{rn}", lambda c, o, t=t, mn=mn: getattr(c.threads[t], mn)))
    for l in range(3):
        for rn, mn, w in (("ph", "PH", 16), ("run", "RUN", 1), ("fired", "FIRED", 3), ("staged", "STAGED", 4),
                          ("committed", "COMMITTED", 4), ("tapmiss", "TAPMISS", 1)):
            f.append((f"l{l}{rn}", w, f"dut.g_ln[{l}].u.{rn}", lambda c, o, l=l, mn=mn: getattr(c.lines[l], mn)))
    f += [("inb", 8, "dut.inb", lambda c, o: c.host.INB), ("inv", 1, "dut.inv", lambda c, o: c.host.INV),
          ("outb", 8, "dut.outb", lambda c, o: c.host.OUTB), ("outv", 1, "dut.outv", lambda c, o: c.host.OUTV),
          ("conflict", 1, "dut.conflict", lambda c, o: c.ctrl.CONFLICT), ("memhaz", 1, "dut.memhaz", lambda c, o: c.ctrl.MEMHAZ),
          ("late_any", 6, "{5'd0,|{" + ",".join(f"dut.g_thr[{t}].u.late" for t in range(6)) + "}}",
           lambda c, o: int(any(t.LATE for t in c.threads))),
          ("starved", 2, "dut.s_starved[1:0]", lambda c, o: c.mem.streams[0].STARVED | (c.mem.streams[1].STARVED << 1))]
    return f


def tb_source(nb, ncyc):
    fl = fields()
    cat = ", ".join(p for _n, _w, p, _m in fl)
    width = sum(w for _n, w, _p, _m in fl)
    return f"""`timescale 1ns/1ps
// Generated by sweep.py: batch loop around tt_um_brentius_metronome (formal-preload structure), per-cycle state dump.
module tb_isa;
    parameter NB = {nb};
    parameter NCYC = {ncyc};
    reg clk = 0; reg rst_n = 0; reg [7:0] ui_in = 8'h00, uio_in = 8'h00;
    wire [7:0] uo_out, uio_out, uio_oe;
    tt_um_brentius_metronome dut(.ui_in(ui_in), .uo_out(uo_out), .uio_in(uio_in), .uio_out(uio_out), .uio_oe(uio_oe),
                                 .ena(1'b1), .clk(clk), .rst_n(rst_n));
    always #5 clk = ~clk;
    integer b, r, fd;
    reg run_seen;
    reg [{width-1}:0] sig;
    reg [8*16-1:0] fn;
    task dump; begin
        sig = {{{cat}}};
        $fdisplay(fd, "%0d %0d %h", b, r, sig);
    end endtask
    task drive(input integer rr); begin
        uio_in = (rr * 37 + (rr >> 3) * 11) & 8'hFF;
        ui_in  = ((rr * 91 + (rr >> 2) * 5) & 8'hF8) | 8'h02;
    end endtask
    initial begin
        fd = $fopen("rtl_trace.txt", "w");
        for (b = 0; b < NB; b = b + 1) begin
            rst_n = 0; ui_in = 8'h00; uio_in = 8'h00;
            $sformat(fn, "b%0d.hex", b);
            $readmemh(fn, dut.u_pmem0.mem);
            $readmemh("dmem.hex", dut.u_dmem.mem);
            repeat (4) @(posedge clk);
            #2 rst_n = 1;
            run_seen = 0; r = 0;
            while (r < NCYC) begin
                @(posedge clk); #1;
                if (!run_seen) begin
                    if (dut.run_g === 1'b1) begin run_seen = 1; r = 0; dump; drive(1); end
                end else begin
                    r = r + 1; dump; drive(r + 1);
                end
            end
        end
        $fclose(fd);
        $finish;
    end
endmodule
"""


def run_model(root, ws, words_by_batch, dmem, ncyc, out_path, coverage):
    fl = fields()
    with open(out_path, "w") as fo:
        for b, words in enumerate(words_by_batch):
            chip = Chip()
            for addr, data, note in ws:
                if note == "CTRL.RUN" or addr < 0x1000:
                    continue
                chip.backdoor_write(addr, data)
            for i, w in enumerate(words):
                chip.cores[0].prog[i] = w
            chip.mem.data[:] = dmem
            chip.backdoor_write(M.HOST_MAP["CTRL_BASE"], bytes([1]))
            o = (0, 0, 0)

            def row(r, o):
                v = 0
                sh = 0
                for _n, w, _p, mf in fl:
                    v = (v << w) | (int(mf(chip, o)) & ((1 << w) - 1))   # first field = most significant
                    sh += w
                fo.write(f"{b} {r} {v:0{(sh + 3) // 4}x}\n")
            # alignment: the RTL's first dumped cycle (run_g high) is one model step after the backdoor RUN write
            o = tuple(chip.step(0, 0, 1))
            row(0, o)
            seen = set()
            n0 = len(chip.trace)
            for r in range(1, ncyc + 1):
                rr = r
                uio = ((rr * 37 + (rr >> 3) * 11) & 0xFF)
                ui = (((rr * 91 + (rr >> 2) * 5) & 0xF8) | 0x02)
                o = tuple(chip.step(ui, uio, 1))
                row(r, o)
            for (_c, core, thr, pc) in chip.trace[n0:]:
                seen.add((core, pc))
            coverage.append(seen)


def exhaustive_batches(per, slots=(0, 1, 2)):
    """Yield (name, test_words, descriptors) for all slot x guard x src x dst, T.STOP excluded."""
    tstop = M.DST_ID["T.STOP"]
    combos = [(g, s, d) for g in range(4) for s in range(64) for d in range(64) if d != tstop]
    for slot in slots:
        for i in range(0, len(combos), per):
            chunk = combos[i:i + per]
            words = []
            for c in chunk:
                mv = [IDLE_SLOT] * 3
                mv[slot] = c
                words.append(pack(mv, imm=0x6D))
            yield f"slot{slot}_{i // per}", words, [(slot,) + c for c in chunk]


def cond_batches(per):
    acc_ld = M.DST_ID["ACC.LD"]
    combos = [(g, s, cnd) for g in range(4) for s in range(64) for cnd in range(64)]
    for i in range(0, len(combos), per):
        chunk = combos[i:i + per]
        yield f"cond_{i // per}", [pack([(g, s, acc_ld)], cond=c, imm=0x6D) for g, s, c in chunk], chunk


def random_batches(n_words, per, seed):
    rng = random.Random(seed)
    tstop = M.DST_ID["T.STOP"]
    for i in range(0, n_words, per):
        words = []
        for k in range(min(per, n_words - i)):
            mv = []
            for _ in range(3):
                g, s, d = rng.randrange(4), rng.randrange(64), rng.randrange(64)
                mv.append((g, s, 0 if d == tstop else d))
            jmode = rng.choice([0, 0, 0, 0, 1, 2, 3])
            words.append(pack(mv, cond=rng.randrange(64), jmode=jmode, jcond=rng.randrange(32),
                              imm=rng.randrange(256), pause=rng.choice([0, 1, 1, 1])))
        yield f"rand_{i // per}", words, None


def skeleton(threads):
    text = (HERE / "skeleton.mas").read_text()
    head = text.split(".thread 0")[0]
    tail_ = ".core 0\np0:     pause goto p0\n"
    mid = text.split(".end\n.out O0")[0] if False else ""
    blocks = "".join(f".thread {t}\n    core 0\n    line {t // 2}\n    trigger ALWAYS\n    pc {pc}\n.end\n"
                     for t, pc in threads)
    outs = ".out O0\n    line 0\n    lut b0 ^ (seg & 1)\n    oe always\n.end\n.out O9\n    line 1\n    lut b0\n.end\n"
    return head + blocks + outs + tail_


def build_group(out, root, threads, batches, ncyc_fn):
    """Writes the RTL inputs of one group and returns the host-write list and batch word lists."""
    import gen_fv
    prog = asm_text(skeleton(threads))
    ws = host_writes(prog)
    gen = out / "gen"
    gen_fv.emit_writes(gen, ws, M, hostin=False, skip_prog=True)
    return ws


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--group", default="all")
    ap.add_argument("--quick", action="store_true", help="a small subset (smoke check of the harness)")
    ap.add_argument("--random-words", type=int, default=30000)
    ap.add_argument("--seed", type=int, default=20261116)
    ap.add_argument("--cycles-per-word", type=int, default=4, help="ALWAYS-trigger dispatch is 4 cycles per burst")
    ap.add_argument("--slots", default="0,1,2")
    a = ap.parse_args()
    root, out = Path(a.root).resolve(), Path(a.out).resolve()
    load_tools(root)
    out.mkdir(parents=True, exist_ok=True)
    PRE = preamble()
    per = 200
    results = {}
    groups = []
    if a.group in ("exhaustive", "all"):
        groups.append(("exhaustive", [(0, 0)], list(exhaustive_batches(per, [int(x) for x in a.slots.split(",")]))))
    if a.group in ("cond", "all"):
        groups.append(("cond", [(0, 0)], list(cond_batches(per))))
    if a.group in ("random", "all"):
        groups.append(("random", [(0, 0)], list(random_batches(a.random_words, per, a.seed))))
    if a.group in ("tstop", "all"):
        tb = []
        tw = [(g, s) for g in range(4) for s in range(64)]
        for i in range(0, len(tw), 6):
            chunk = tw[i:i + 6]
            words = [pack([(g, s, M.DST_ID["T.STOP"])], imm=0x6D) for g, s in chunk]
            tb.append((f"tstop_{i // 6}", words, chunk))
        groups.append(("tstop", None, tb))
    if a.quick:
        groups = [(n, t, b[:3]) for n, t, b in groups]
    dm = dmem_image()
    t_total = time.time()
    for gname, threads, batches in groups:
        gdir = out / gname
        gdir.mkdir(exist_ok=True)
        if gname == "tstop":
            # thread t (t = 0..5) starts at word t; every word is [guard,src -> T.STOP] + a jump-to-self tail
            threads = [(t, 2 * t) for t in range(6)]
        ws = build_group(gdir, root, threads, batches, None)
        prog_words = []
        for name, words, _desc in batches:
            if gname == "tstop":
                img = []
                for w in words:
                    img += [w, tail(len(img) + 1)]
                img += [tail(len(img))] * (12 - len(img))
                prog_words.append(img)
            else:
                img = PRE + words + [tail(len(PRE) + len(words))]
                assert len(img) <= 256, len(img)
                prog_words.append(img)
        ncyc = max(len(w) for w in prog_words) * a.cycles_per_word + 40
        (gdir / "dmem.hex").write_text("\n".join(f"{int.from_bytes(dm[i:i + 4], 'little'):08x}"
                                                  for i in range(0, 2048, 4)) + "\n")
        for b, img in enumerate(prog_words):
            full = img + [0] * (256 - len(img))
            (gdir / f"b{b}.hex").write_text("\n".join(f"{w:016x}" for w in full) + "\n")
        (gdir / "tb_isa.v").write_text(tb_source(len(prog_words), ncyc))
        files = [root / "src" / f for f in ("project.v", "md2_core.v", "md2_thread.v", "md2_line.v", "md2_acc.v",
                                            "md2_shifter.v", "md2_counter.v", "md2_lfsr.v", "md2_mem.v",
                                            "md2_stream.v", "md2_pmem.v", "md2_dmem.v")]
        files += [FP / "rtl_fv/fv_cfg_bank.v", FP / "rtl_fv/fv_host.v"]
        env = dict(os.environ)
        cmd = ["iverilog", "-g2012", "-DSIM", "-DFV_PAYLOAD=8'h00", "-DFV_DELAY=0", "-I", str(root / "src"),
               "-I", str(gdir / "gen"), "-I", str(FP / "rtl_fv"), "-o", str(gdir / "isa.vvp"),
               str(gdir / "tb_isa.v")] + [str(f) for f in files]
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode:
            print(r.stderr[-3000:])
            return 2
        t0 = time.time()
        r = subprocess.run(["vvp", str(gdir / "isa.vvp")], cwd=gdir, capture_output=True, text=True)
        (gdir / "vvp.log").write_text(r.stdout + r.stderr)
        t_rtl = time.time() - t0
        t0 = time.time()
        coverage = []
        run_model(root, ws, prog_words, dm, ncyc, gdir / "model_trace.txt", coverage)
        t_mod = time.time() - t0
        rtl = (gdir / "rtl_trace.txt").read_text().splitlines()
        mod = (gdir / "model_trace.txt").read_text().splitlines()
        mism = [i for i, (x, y) in enumerate(zip(rtl, mod)) if x != y]
        # words executed at least once (model trace), tests only
        npre = len(PRE)
        executed = sum(len([pc for (core, pc) in cov if core == 0 and npre <= pc < npre + len(batches[i][1])])
                       for i, cov in enumerate(coverage)) if gname != "tstop" else sum(
            len([pc for (core, pc) in cov if pc % 2 == 0 and pc < 2 * len(batches[i][1])]) for i, cov in enumerate(coverage))
        nwords = sum(len(b[1]) for b in batches)
        res = {"batches": len(batches), "test_words": nwords, "executed_at_least_once_in_model": executed,
               "cycles_compared_per_batch": ncyc + 1, "rows_rtl": len(rtl), "rows_model": len(mod),
               "mismatching_rows": len(mism), "first_mismatch": None, "t_rtl_s": round(t_rtl, 1),
               "t_model_s": round(t_mod, 1)}
        if len(rtl) != len(mod) or mism:
            i = mism[0] if mism else min(len(rtl), len(mod))
            res["first_mismatch"] = {"row": i, "rtl": rtl[i] if i < len(rtl) else None,
                                     "model": mod[i] if i < len(mod) else None}
        results[gname] = res
        print(gname, json.dumps(res))
    results["_meta"] = {"root": str(root), "seed": a.seed, "elapsed_s": round(time.time() - t_total, 1),
                        "fields": [(n, w) for n, w, _p, _m in fields()]}
    (out / "result.json").write_text(json.dumps(results, indent=1))
    return 1 if any(isinstance(v, dict) and v.get("mismatching_rows") for k, v in results.items()
                    if k != "_meta") else 0


if __name__ == "__main__":
    sys.exit(main())
