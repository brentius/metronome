# Compiled-program bounded proof (V3 plan 7.4)

BMC (SymbiYosys, smtbmc, bitwuzla; yosys-slang front end) of the **full chip RTL** with a compiled Score program loaded.

    source code/tools/env.sh
    python code/tests/formal_programs/run_proofs.py --root SRC_ROOT --out SCRATCH/run --task safe     # the proof
    ... --task hazard      # same property without the d != 2 exclusion: fails, the HOSTIN-drop counterexample
    ... --task cover       # a complete frame is reachable (non-vacuity)
    ... --mutant stop_bit_low|start_bit_high|img_mod7|img_stop_low --task safe     # each must fail
    python code/tests/formal_programs/ce_summary.py SCRATCH/run/work                # payload and delay of a counterexample

`SRC_ROOT` is any tree with `src/`, `code/scorec`, `code/score`, `code/host2`, `sim/reference` (the frozen baseline or v3).
Program: `code/score/lib/uart_8n1.score`, role sender, `tx=O8`, 10 Mbaud (6 clk/bit), compiled by `scorec`.

Preload equivalence (assumption A6 of `wiki/EVIDENCE.md`): `rtl_fv/fv_cfg_bank.v` replaces `md2_cfg_bank` by the constant
the image writes (visible once the bank's reset chain releases); `rtl_fv/fv_host.v` replaces `md2_host` by a sequencer
that issues the image's program bytes (all of them, zeros included) and runtime writes (T0.PC, T0.EN, CTRL.RUN, L0.CTL) on
the same internal write bus, then one `CTRL.HOSTIN` write of a symbolic payload after 18 + d cycles, d symbolic in 0..11.
All other RTL is the unmodified `src/`. Input pins are free every cycle. Data RAM and unreached program words are
unconstrained. `tb_calib.v` replays concrete (payload, d) values in Icarus on the same build (calibration of the
latency bound and the beat-grid phase).
