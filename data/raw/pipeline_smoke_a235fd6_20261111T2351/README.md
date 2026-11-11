# Official Tiny Tapeout pipeline smoke: required gates passed

Validated source: **a235fd6ef655bbf02066f68cecf56bca5b81545b**, branch `ci/pipeline-smoke-20261111`. This is the existing small combinational template example, configured for 8x4 tiles, 60 MHz and top `tt_um_brentius_metronome`. It is a CI-pipeline smoke test, not Metronome v1/v2 hardware validation.

| Required gate | Result | Evidence |
|---|---|---|
| RTL test | Passed | [run 43112777630](https://github.com/brentius/metronome/actions/runs/43112777630), `rtl_run.json`, `rtl_workflow_logs.zip` |
| GDS build | Passed, 2026-11-11 23:29:29 UTC | [job 130832880652](https://github.com/brentius/metronome/actions/runs/43112777677/job/130832880652), `jobs.json`, `tt_submission.zip` |
| Tiny Tapeout precheck | Passed, 23:50:05 UTC; 10 checks, including full SG13CMOS5L DRC | [job 130858463007](https://github.com/brentius/metronome/actions/runs/43112777677/job/130858463007), `precheck_reports.zip` |
| Gate-level simulation | Passed, 23:30:13 UTC; 1/1 test | [job 130858462836](https://github.com/brentius/metronome/actions/runs/43112777677/job/130858462836), `gatelevel_test_results.zip` |

The physical workflow's **overall conclusion is failure** solely because the optional viewer could not deploy to GitHub Pages (HTTP 404; Pages not enabled). All four required pipeline gates passed. Viewer publication settings were not changed. Docs run 43112777634 also passed.

## Provenance and preserved outputs

- `jobs.json`, `artifacts.json`, `rtl_run.json`, `physical_workflow_run.json`: observed GitHub job/run/artifact metadata. These distinguish required-job success from optional viewer failure.
- `tt_submission.zip` (artifact 13899004703): original generated layout/netlist and source/config snapshot, including commit ID and PDK provenance. Downloading this artifact is not a tapeout submission.
- `gatelevel_test_results.zip` (artifact 13901185590): original GL XML results and waveform.
- `precheck_reports.zip` (artifact 13900499236): original precheck results and DRC reports.
- `physical_workflow_logs.zip`, `rtl_workflow_logs.zip`: complete original job logs, including the optional viewer error.
- `submission_commit_id.json`, `pdk.json`, `gatelevel_results.xml`, `precheck_results.xml/md`: byte-for-byte copies of selected archive members for review.
- `manifest.json`: file sizes and SHA-256 hashes; ZIP CRC and artifact-digest checks passed.
- Derived validation summary: `data/processed/pipeline_smoke_a235fd6_20261111T2351.json`.

The generated submission records Tiny Tapeout support tools `9d13ff3e`, LibreLane `3.1.0.dev4`, PDK `ihp-sg13cmos5l` from IHP-Open-PDK `89d42ee6d2fd9b50b86a1aada6fee6673c3e6008`, and the exact smoke commit/workflow URL. Automatic follow-up is disabled after required-gate success. Root README stays empty and user-owned; no v1 timing work or v2 design work was resumed.
