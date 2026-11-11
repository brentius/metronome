# First official template physical run: failed slow setup

Source `c83a7f4f0b3443ab065fc4619414ffa5bbd36f21`, [run 43099316692](https://github.com/brentius/metronome/actions/runs/43099316692), GDS job `130785460765`, artifact `13894909439` (`GDS_logs`). Started 2026-11-11 21:00:24 UTC; job ended 22:13:32 UTC with failure. Dependent precheck and GL jobs were skipped. RTL test and docs workflows passed separately.

The flow completed routing, generated final views, and Netgen reported “Circuits match uniquely.” Its deferred-error summary identifies setup violations at `nom_slow_1p08V_125C` as the failing gate. These are fresh post-route extracted STA results at a 16.667 ns clock, not inherited v1 metrics:

- Slow setup worst slack −0.422881 ns, TNS −4.755686 ns, 25 violating endpoints.
- Typical setup +5.875966 ns (about +5.876); fast +9.5401 ns.
- Hold is positive in all reported corners; worst overall about +0.0956 ns.
- Slow corner also has cap/slew violations. No new TT precheck pass or complete physical signoff is claimed.

The first slow setup path starts at `u_pmem1.u_sram`, whose clock-to-Q is 5.543210 ns on that path, and crosses same-cycle instruction decode. The post-GRT repair log shows the actual `-setup_margin 3.0` invocation and pre-route WNS about +2.825 ns. The native reports explain why a positive estimated global-route result did not establish final closure.

## Preserved inputs and outputs

- `GDS_logs.zip`: full original artifact, 295548328 bytes, SHA-256 `d76f891bcec345d43e66d95808410396118eaea427d341ff7521215d2a52a1bc`. Kept locally and ignored by Git; the GitHub artifact is the second copy.
- `archive_members.txt`: original ZIP member list.
- `github_job.log`: original downloaded job log, including tool/action versions and the actual error.
- `selected/`: original selected configs, repair/routing logs, final netlist, native timing reports and LVS reports. Large per-corner STA logs/reports are retained locally and in the artifact, but ignored by Git. The root STA summary and smaller reports are versioned. No original raw output was edited.
- Derived metric provenance/diagnosis: `data/processed/template_ci_c83a7f4_failure_20261111T2221.json`.

## Bounded next experiment

Change only `GRT_RESIZER_SETUP_SLACK_MARGIN` from 3.0 ns to 4.0 ns. Leave placement margin, RTL, ISA, pin map, memories, 16.667 ns clock and all final checks intact. A read-only Luna-medium review supported this as a useful physical-only experiment, while explicitly noting that it does not guarantee closure. The next official flow must establish the result, including hold, routing, area, precheck and gate-level behavior. V2 architecture changes remain with Fable.
