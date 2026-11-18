# Compiled Score pin verification

`run_score.py` compiles actual Score programs, loads the ordered image through the host SPI link at clk/16,
and compares sampled RTL outputs with the cycle reference model. UART/SPI/Ethernet decoders and an independent
I2C decoder/peer check protocol data. Receiver RAM and error status are read through SPI and checked separately.
The cases cover mixed-width mailbox fields, UART TX/RX and bad stop, full-duplex SPI controller, Ethernet
TX/RX/FCS rejection, and I2C controller/target including stretching and address NACK.
The two additional SPI points are the original edge-sampled Score at60/7MHz and an explicit later-sampling Score
at10MHz. I2C target checks include raw OE hold after SCL falls and absence of driven-high open-drain outputs.

```powershell
python code/tests/score_rtl/run_model.py --out data/raw/score_model_NEW
python code/tests/score_rtl/run_score.py --out data/raw/score_rtl_NEW
python code/tests/score_rtl/run_score.py --out data/raw/score_frozen_NEW --rtl-src PATH_TO_FROZEN_SRC
```

Select cases with repeated `--case NAME`. Gate runs add `--netlist PATH --cells PDK_VERILOG_DIRECTORY`;
SDF runs also add `--sdf PATH`. Each output directory must be new. The runner preserves source hashes,
compiled assembly/images, XML/logs, actual driven inputs, sampled outputs and semantic/readback results.
A failing, missing or skipped test is a failure. Inputs that change during a run invalidate its aggregate result.
Use an immutable source snapshot for parallel work. `run_model.py` is a quick fixture preflight, not RTL evidence.

The nominal chip clock is60MHz (simulated period16667ps). SRAM arrays are initialized internally to zero for
reproducibility; program/configuration/data needed by each scenario is then loaded through SPI. These tests
do not establish startup from unknown/stale SRAM or all buffer-exhaustion behavior. Peer feedback uses the
previous cycle's reference outputs, which must agree with sampled RTL outputs on every checked cycle.
Pins are sampled8ns after each rising edge. The SDF adapter omits SRAM/interconnect annotation and Icarus
does not enforce timing checks; this is functional delay simulation, not complete timing signoff or hardware.

Mailbox wire speed and host throughput are distinct: the mixed-width SPI scenario runs at100kbit/s with
explicit arrival spacing. The speed sweep uses an ideal producer for its high-rate mailbox points. Reading an
empty mailbox returns its latched byte; there is no FIFO or automatic frame stall. Applications must supply
each field before its scheduled read. Images assume a reset/stopped chip; activation is RUN before lineCTL,
and does not make several lines start atomically. The qualified r4b netlist cannot verify subsequent RTL edits.
