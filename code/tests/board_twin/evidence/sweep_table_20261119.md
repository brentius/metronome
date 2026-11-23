clock period 16000 ps (62.5 MHz); 38 points; 28 pin-change nudges away from clock edges

| SCK | period (chip cycles) | phase | jitter | sample lead | ID | read RAM | read reg | write RAM | write reg | model mismatches | verdict |
|---|---|---|---|---|---|---|---|---|---|---|---|
| clk/32 | 32 | 0.05 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/32 | 32 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/32 | 32 | 0.95 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/24 | 24 | 0.05 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/24 | 24 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/24 | 24 | 0.95 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/20 | 20 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/16 | 16 | 0.05 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/16 | 16 | 0.37 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/16 | 16 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/16 | 16 | 0.95 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/16 | 16 | 0.50 | 0.45 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/15.5 | 15.5 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/15 | 15 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/15 | 15 | 0.95 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/12 | 12 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/10 | 10 | 0.95 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/8 | 8 | 0.05 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/8 | 8 | 0.50 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/8 | 8 | 0.95 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/6 | 6 | 0.50 | 0.00 | 0.25 | ok | **fail** | ok | ok | ok | 0 | FAIL |
| clk/6 | 6 | 0.95 | 0.00 | 0.25 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/5 | 5 | 0.05 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/5 | 5 | 0.50 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/4 | 4 | 0.05 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/4 | 4 | 0.37 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/4 | 4 | 0.62 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/4 | 4 | 0.95 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/4 | 4 | 0.50 | 0.30 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/3.5 | 3.5 | 0.50 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/3 | 3 | 0.50 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/3 | 3 | 0.95 | 0.00 | 0.25 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |
| clk/2 | 2 | 0.05 | 0.00 | 0.25 | **fail** | **fail** | **fail** | ok | ok | 0 | FAIL |
| clk/2 | 2 | 0.50 | 0.00 | 0.25 | **fail** | **fail** | **fail** | ok | ok | 0 | FAIL |
| clk/2 | 2 | 0.95 | 0.00 | 0.25 | **fail** | **fail** | **fail** | ok | ok | 0 | FAIL |
| clk/8 | 8 | 0.50 | 0.00 | 0.05 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/6 | 6 | 0.50 | 0.00 | 0.05 | ok | ok | ok | ok | ok | 0 | PASS |
| clk/4 | 4 | 0.50 | 0.00 | 0.05 | **fail** | **fail** | ok | ok | ok | 0 | FAIL |

- full link (ID read + RAM read + register read + writes) at every tested phase: clk/8, clk/10, clk/12, clk/15, clk/15.5, clk/16, clk/20, clk/24, clk/32
- reads at every tested phase: clk/8, clk/10, clk/12, clk/15, clk/15.5, clk/16, clk/20, clk/24, clk/32
- writes at every tested phase: clk/2, clk/3, clk/3.5, clk/4, clk/5, clk/6, clk/8, clk/10, clk/12, clk/15, clk/15.5, clk/16, clk/20, clk/24, clk/32
- model mismatches over all points: 0
