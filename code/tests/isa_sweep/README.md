# Single-instruction sweep (V3 plan 7.9)

    python code/tests/isa_sweep/sweep.py --root SRC_ROOT --out SCRATCH/isa --group exhaustive --slots 0   # slots 0,1,2 in parallel
    ... --group cond | random --random-words 12000 | tstop          ... --quick   (3 batches, harness check)
    python code/tests/isa_sweep/diffrow.py SRC_ROOT SCRATCH/isa/exhaustive BATCH ROW N                   # decode a mismatch

See the module docstring for the enumerated sets and what they do not cover. RTL: Icarus on the formal-preload build
(`../formal_programs/rtl_fv`), program words loaded by the testbench into the behavioural program array, SRAM zeroed.
Model: `sim/reference/metronome2`. Compared: pins and ~60 architectural fields every cycle, aligned at the first cycle
with RUN_global high. About 5 minutes per slot run on one core.
