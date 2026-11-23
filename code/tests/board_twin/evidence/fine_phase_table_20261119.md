clock period 16000 ps (62.5 MHz); 20 points; 2 pin-change nudges away from clock edges

| SCK | phase 0.02 | phase 0.12 | phase 0.22 | phase 0.32 | phase 0.42 | phase 0.52 | phase 0.62 | phase 0.72 | phase 0.82 | phase 0.92 |
|---|---|---|---|---|---|---|---|---|---|---|
| clk/5 ID read | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** | ok | ok | ok | ok |
| clk/5 RAM read | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** |
| clk/5 register read | ok | ok | ok | ok | ok | ok | ok | ok | ok | ok |
| clk/5 RAM write | ok | ok | ok | ok | ok | ok | ok | ok | ok | ok |
| clk/5 register write | ok | ok | ok | ok | ok | ok | ok | ok | ok | ok |
| clk/6 ID read | ok | ok | ok | ok | ok | ok | ok | ok | ok | ok |
| clk/6 RAM read | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** | **fail** | ok | ok | ok |
| clk/6 register read | ok | ok | ok | ok | ok | ok | ok | ok | ok | ok |
| clk/6 RAM write | ok | ok | ok | ok | ok | ok | ok | ok | ok | ok |
| clk/6 register write | ok | ok | ok | ok | ok | ok | ok | ok | ok | ok |

- full link (ID read + RAM read + register read + writes) at every tested phase: none
- reads at every tested phase: none
- writes at every tested phase: clk/5, clk/6
- model mismatches over all points: 0
