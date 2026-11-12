# Latch-bank sizing branch through the Tiny Tapeout GitHub Action, 2026-11-12

Commit `72f7b9e` on branch `sizing/latch-bank-20261112` (minimal top wrapping `cfg_latch_bank`, 2,048 bits, written
over host SPI). Workflow run 43127164757 (`gds`): the **Build GDS step was cancelled at GitHub's 6 h job limit**
(00:25:34 to 06:25:30 UTC); gl_test, precheck and viewer were skipped, so there is no flow result. The `test` (RTL)
run 43127164720 and `docs` run 43127165072 passed. Job logs need authentication (HTTP 403 without a token) and were
not retrieved; these JSON files are the public run and job metadata, fetched 2026-11-12.

Likely cause (not confirmed from the log): the post-CTS resizer's time borrowing through transparent latches. In the
v2 skeleton r1 that step alone took 4,634 s on a 16-vCPU pod; after the D24 write-path change it took 25 s. The
latch structure itself has since passed the full flow, precheck and GL inside the skeleton (`../v2pnr_skeleton_20261112/`).
The branch was built before D24 and was not rerun.
