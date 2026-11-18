"""Generate and run the compiled-program BMC proofs.

    python run_proofs.py --root ROOT --out DIR --program uart_tx --task safe [--mutant NAME] [--depth N] [--timeout S]

ROOT: source tree (src/, code/scorec, ...) - the frozen v3 baseline snapshot, or a v3 tree later.
DIR : fresh work directory (generated inputs, .sby, SymbiYosys output).  Tasks: safe | hazard | cover.
"""
import argparse, os, shutil, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gen_fv  # noqa: E402

DUT_FILES = ["project.v", "md2_core.v", "md2_thread.v", "md2_line.v", "md2_acc.v", "md2_shifter.v", "md2_counter.v",
             "md2_lfsr.v", "md2_mem.v", "md2_stream.v", "md2_pmem.v", "md2_dmem.v"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--program", default="uart_tx")
    ap.add_argument("--mutant", default="none")
    ap.add_argument("--task", default="safe")
    ap.add_argument("--depth", type=int, default=0)
    ap.add_argument("--timeout", type=int, default=900)
    ap.add_argument("--hazard", type=int, default=2)
    a = ap.parse_args()
    root, out = Path(a.root).resolve(), Path(a.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    gen = out / "gen"
    n, ncfg = gen_fv.emit(gen, root, a.program, a.mutant)
    stage = out / "stage"
    stage.mkdir(exist_ok=True)
    names = []
    for f in [root / "src" / f for f in DUT_FILES] + [root / "src" / "md2_defs.vh", root / "src" / "md2_map.vh",
              HERE / "rtl_fv/fv_cfg_bank.v", HERE / "rtl_fv/fv_host.v", HERE / f"fv_{a.program}.sv",
              gen / "fv_cfg_img.vh", gen / "fv_seq.vh"]:
        shutil.copy(f, stage / f.name)
        names.append(f.name)
    depth = a.depth or int(os.environ.get("FV_DEPTH", "0")) or DEFAULT_DEPTH[a.program]
    tpl = (HERE / f"fv_{a.program}.sby.in").read_text()
    srcs = [n for n in names if n.endswith(".v") or n.endswith(".sv")]
    sby = (tpl.replace("@DEPTH@", str(depth)).replace("@FILES@", " ".join(srcs[:-1]))
           .replace("@FVSV@", f"fv_{a.program}.sv").replace("-I @GEN@ -I @SRC@", "")
           .replace("@HAZARD@", str(a.hazard)))
    sby += "".join(n + chr(10) for n in names)
    (stage / "job.sby").write_text(sby)
    t0 = time.time()
    r = subprocess.run(["sby", "-f", "-d", str(out / "work"), "job.sby", a.task], cwd=stage, capture_output=True,
                       text=True, timeout=a.timeout)
    (out / "sby.log").write_text(r.stdout + r.stderr)
    print(r.stdout[-1500:], r.stderr[-500:])
    print(f"task={a.task} program={a.program} mutant={a.mutant} depth={depth} seq={n} cfg_bytes={ncfg} "
          f"rc={r.returncode} time={time.time()-t0:.0f}s")
    return r.returncode


DEFAULT_DEPTH = {"uart_tx": 200, "uart_rx": 150}
if __name__ == "__main__":
    sys.exit(main())
