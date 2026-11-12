# v2 skeleton place-and-route runs, 2026-11-12 (U10)

Raw outputs of the Tiny Tapeout flow (tt-support-tools `--harden --no-docker`, LibreLane 3.1.0.dev4, PDK
ihp-sg13cmos5l 89d42ee6, see each `versions.txt`) on RunPod pod `95t05xzcwd33an` (cpu5c, 16 vCPU), for the v2-only
skeleton `sim/numerics/v2_sizing/tt_v2_pnr/`. Copied from `/workspace/results/<tag>/` on network volume `tjy64mfk8b`.
Do not edit. Diagnosis and history: `BOTS/PLANS/HARDEN_LEDGER.md`, "v2 skeleton iterations"; decision D24.

| Tag | Source config | Result |
|---|---|---|
| `v2pnr_r1_20261112T0056` | template defaults + SRAM recipe | fail at LVS: 51 DRT shorts, slow setup -0.926 ns |
| `v2pnr_r3_20261112T0837` | + v1.0 repair block, latch write fix, `project.sdc` | fail: slow setup -1.154 ns; DRT 0, LVS clean |
| `v2pnr_r4_20261112T0921` | + `MAX_TRANSITION_CONSTRAINT` 1.0 | **pass**: slow setup +0.398 ns, hold +0.110, DRT 0, LVS clean, precheck 10/10 (`precheck/`), GL 1/1 (`gl/`) |

(r2 was killed by user request before it produced a result.) `runs.log` is the volume's run log at copy time.

**Not in Git** (`.gitignore`; on this laptop's disk and on the volume): each run's `run_text.tgz` (all step logs,
reports and metrics, about 11 MB each) and `harden.log` (flow console, about 3.5 MB each). Full physical views
(`final/` GDS, DEF, ODB, SPEF, SDF and `tt_submission/`) are only on the volume.
