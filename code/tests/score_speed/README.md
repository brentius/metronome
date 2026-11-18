# Score reference-model rate sweep

Run from the repository root:

```powershell
python code/tests/score_speed/bench.py --repo . --out data/raw/score_speed_<run-id>
```

For a frozen source snapshot, pass its extracted root to `--repo`. The runner imports the compiler, reference model,
Score examples and peer benches only from that tree. Every scenario compiles an actual Score program, configures the
model image directly, drives a small deterministic payload, checks decoded protocol events or received bytes, and
requires zero LATE, OVR, TAPMISS, STARVED, CONFLICT and MEMHAZ flags. UART/SPI/Ethernet use the Score codec oracle;
I2C additionally uses its independent bus decoder. Ethernet is exercised at its fixed 10 Mb/s line rate. Mixed-width
mailbox cases include LSB, MSB and reversed LSB field order. Baseline corruption is retained as a runtime failure.
The runner stores exact Score text, assembly, image, host writes, source hashes and a copy of its own source.
Original edge-sampled SPI and an explicit later-sampling variant are separate cases; the compiler does not move
the original sample. Check both received RAM and decoded wires: a wire-only check missed the old9/10MHz RX fault.

This measures functional rates in the pure Python cycle model at a fixed 60 MHz clock. Image setup bypasses host SPI,
so it says nothing about host throughput. A compiler E-TIME rejection, a runtime failure, and a pass are separate
outcomes. The highest tested pass is only a tested point, not a validated protocol maximum. This is not RTL, gate,
STA, silicon, or hardware evidence.
