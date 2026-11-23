# Findings — pad-input CDC campaign (2026-11-19)

Scope: structural audit of `src/` at branch `metronome-v4.0`, HEAD `b7b4068` + uncommitted v4 working tree, plus
the ±1-cycle jitter simulation in this directory. Nothing here is a request to change RTL.

## No RTL, SPEC or reference-model defect found

The audit proves the intended structure: all 16 raw pad bits enter `s1` only, `s1 → s2` only, and raw `rst_n`
reaches only the two `ARST` pins of the reset synchroniser (`rst_m`, `rst_q`), with the configuration latch bank's
2112 asynchronous clears fed by the synchronised `rst_q`/`rst_s` rather than by the raw pin. The jitter runs decode
identically to their unperturbed controls. This matches SPEC v2 §1–2 ("async assert, synchronous release"): the
`rst_m`/`rst_q` cells are the only `$adff`, every downstream clear is synchronous (`SRST`) or a latch async clear
driven by `rst_s`.

The two items below are *not* defects. They are recorded because they are easy to get wrong when writing further
tests, and one of them changes how a jitter/CDC negative control has to be built.

## Observation 1 — the host link tolerates a full one-cycle first-stage slip, even at SCK = clk/2

**Class: RTL-simulated.** Not a defect, but it means "±1 cycle of jitter" can never be used as a *must-fail* control
on this design.

Reproduction (≈10 s with a warm OSS CAD Suite, 2 passes × 1 604 cycles):

```sh
CDC_SCENARIOS=spi_host_fast CDC_SEEDS=7 CDC_JITTER=1 CDC_JITTER_DEPTH=1 \
    python -m pytest code/tests/cdc -q -k test_cdc_jitter
```

Observed: every MOSI edge is one cycle late, `spi_host_fast` writes a sentinel at clk/16, overwrites the same
address at clk/2 and reads back — and both readbacks are still correct (`[5a5a, a53c]`,
`results/cdc_rtl_20261119/probes/spi_host_fast-depth1.json`). With `CDC_JITTER_DEPTH=2` the clk/2 overwrite is lost
(`[5a5a, 5a5a]`, `…-depth2.json`).

Why: the first two flops delay `SCK` and `MOSI` by the same amount, so a per-pin slip is common-mode until it
exceeds the receiver's internal margin. Consequence for this campaign: the negative control must use a disturbance
larger than one cycle (`test_negative_control` uses two), and the "±1 cycle" claim in the README is a *tolerance*
claim, not a demonstrated limit.

## Observation 2 — SRAM contents survive a reset, so a write→readback control can pass after a failed write

**Class: RTL-simulated.** Harness hazard, not a design bug (SPEC v2: configuration is cleared, memories are not).

Reproduction: any scenario that (a) runs a clean pass, (b) writes a value over SPI in the perturbed pass, and
(c) reads the same address back. If the perturbed write fails, the readback returns the value the *clean* pass left
in that SRAM word and the pass looks successful. This was observed while building the negative control: a
"write 0xa53c at clk/2, read back" scenario decoded `a53c` even with MOSI frozen for four cycles
(`CDC_JITTER_DEPTH=4`, MOSI pin never following its stimulus).

Fix used here: `spi_host_fast` writes a *sentinel* at the safe rate first, reads it back, then overwrites and reads
again, so the two readbacks must show two different values and retention cannot mask a lost write. Other tests that
verify a write by readback after a reset should do the same.
