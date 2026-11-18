# Metronome v2 protocol pin campaign

This campaign checks that a program loaded through the host SPI pins can generate bounded protocol wire traces using the v2 line engine, instruction memory and GPIO lookup tables. Each test runs the same case on the RTL or a routed netlist, compares every output pin each cycle against `sim/reference/metronome2`, then finds and decodes the expected wire-cell sequence from the observed GPIO trace. The independent decoder is in `protocol_decode.py`; it does not use the assembler, waveform builder or chip model. A corrupted-pin negative control must be rejected in each run.

These are precomposed waveform demonstrations, not dedicated protocol peripherals or full endpoint implementations. Program images are unrolled from host-provided constants. The test proves that the chip can replay the corresponding pin states through its programmable line and output machinery. It does not prove that a chip can discover a protocol, parse arbitrary traffic, arbitrate, recover clocks, or compute every protocol response in hardware.

## Coverage

The chip runs at a nominal 60 MHz. The runner uses a 16,667 ps clock period with alternating 8,333/8,334 ps half-cycles, and samples pins 8,000 ps after the rising edge. The cycle periods below are the programmed waveform cell durations.

| Case | Pins and bounded vector | Scope and limits |
|---|---|---|
| `uart` | O0, 1 Mbit/s, two 8N1 bytes `A6 39` | TX framing and data; no receive endpoint |
| `spi_mode0` … `spi_mode3` | O0 SCK, O1 MOSI, O2 active-low CS; bytes `96 2D` | CPOL/CPHA, setup/sample/return edges and CS framing; MISO is not driven by a target |
| `i2c_100k` | O0 SCL, O1 SDA; START, address `0x50` write, ACK, byte `A5`, ACK, STOP | Precomposed combined bus trace; ACK lows are waveform cells, not a dynamic target response. Open-drain release/drive and pull-ups are represented |
| `i2c_400k` | Same trace at 400 kHz, 50-cycle cells | SCL low is 100 cycles (1.667 µs), high is 50 cycles (0.833 µs), and bus-free time after STOP is 100 cycles (1.667 µs), calculated at 60 MHz |
| `usb_ls` | O0 D−, O1 D+; DATA0 packet `5A`, sync/PID, CRC16, stuffing and SE0 EOP | Low-speed NRZI/J-K pair replay at 1.5 Mbit/s; no attach, reset, handshake, enumeration or retry behavior |
| `ethernet_10baset` | O0/O1 differential TX; `55` preamble ×7, `D5` SFD, body `12 A6` | Manchester at 10 Mbit/s (six 60 MHz cycles per bit, three per half-bit); no Ethernet FCS or complete MAC frame |
| `jtag` | O0 TCK, O1 TMS, O2 TDI | TAP reset, idle, DR select/capture, 32 zero bits, update and idle; no target/TDO response |
| `swd` | O0 SWCLK, O1 SWDIO; O3 mirrors SWDIO drive enable | Host request fields APnDP=1, RnW=0, A2=1, A3=0, parity/stop/park, then four released turnaround clocks; no target ACK/data phase |
| `ps2` | O0 clock, O1 data; byte `5A` | One 11-bit frame, odd parity, open-drain levels, 16.7 kHz clock. Data changes on rising edges before the following falling-edge sample |
| `can` | O0 recessive/dominant bus abstraction; 500 kbit/s | Classical 11-bit ID `123`, DLC 1, data `A5`, CRC-15, stuffing, unacknowledged ACK slot and EOF; no analog transceiver, arbitration or retransmission |
| `custom_hdlc` | O0; flag, payload `7E 7D A5`, CRC-16/CCITT and zero stuffing | Invented bounded protocol; CRC is non-reflected, init `FFFF`, poly `1021`, transmitted MSB-first |
| `custom_diffman` | O0/O1 differential pair; preamble/sync/payload `55 D5 3C` | Invented differential-Manchester convention defined by the waveform builder and decoder; not a standard |

UART, SPI, I2C, low-speed USB, 10 Mbit Ethernet, JTAG, SWD, PS/2 and CAN are the competition's named target families. The two custom vectors provide examples of reprogramming for new framing and line codes.

Each case also reads the runtime status blocks through the host SPI link after the capture window. The bench expects no TAPMISS, LATE, OVR, STARVED, core conflict or memory hazard flags. Raw stimulus, sampled pins, resolved wire traces, per-case XML/logs and hashes are kept under the requested output directory. The runner refuses to reuse an existing output path so separate RTL, gate and SDF attempts remain intact.

## Run

Use Python 3.12, cocotb 2.1 and Icarus Verilog 14-devel from the local OSS CAD Suite. In PowerShell:

```powershell
. .\code\tools\env.ps1
python code\tests\protocol_campaign\run_campaign.py --repo . --out data\raw\protocol_campaign_rtl_20261115T2000Z
```

Run one or more selected cases during iteration:

```powershell
python code\tests\protocol_campaign\run_campaign.py --repo . --out data\raw\protocol_campaign_smoke_20261115T2000Z --case uart --case spi_mode0
```

For a hardened netlist, supply the routed netlist and the IHP standard-cell Verilog directory. For SDF, run one corner per fresh output directory:

```powershell
python code\tests\protocol_campaign\run_campaign.py --repo . --netlist <r4b-netlist.nl.v> --cells <sg13cmos5l_stdcell-model-dir> --out <new-gate-output-dir>
python code\tests\protocol_campaign\run_campaign.py --repo . --netlist <r4b-netlist.nl.v> --cells <sg13cmos5l_stdcell-model-dir> --sdf <corner.sdf> --out <new-sdf-output-dir>
```

SDF simulation is supplemental functional evidence. The Icarus converter omits SRAM macro SDF and cell-to-cell INTERCONNECT delays, and Icarus does not enforce SDF timing checks. Sampling outputs 8 ns after an edge does not establish timing closure; use the routed STA reports for that.

## References

- [Jane Street competition brief and FAQ](https://blog.janestreet.com/protocol-emulator-asic-competition/) — target protocol families, GPIO and clock constraints, submission verification expectations.
- [NXP UM10204, I2C-bus specification and user manual](https://community.nxp.com/pwmxy87654/attachments/pwmxy87654/other/18306/1/UM10204_I2CSpec.pdf?inline=true) — START/STOP, ACK, standard/fast-mode timing.
- [USB-IF USB 2.0 specification](https://www.usb.org/usb2) — low/full-speed packet and physical-layer reference.
- [IEEE 1149.1 Working Group](https://grouper.ieee.org/groups/1149/1/) — TAP and boundary-scan architecture.
- [Arm, low pin-count debug interfaces](https://developer.arm.com/-/media/Arm%20Developer%20Community/PDF/Low_Pin-Count_Debug_Interfaces_for_Multi-device_Systems.pdf) — SWD context; the production specification is the Arm Debug Interface Architecture Specification (ADIv5).
- [IBM Personal System/2 Hardware Interface Technical Reference](https://bitsavers.org/pdf/ibm/pc/ps2/Personal_System_2_Hardware_Interface_Technical_Reference_May88.pdf) — keyboard and auxiliary-device interface context.
- [Bosch, Classical CAN bit stuffing and CRC discussion](https://www.bosch-semiconductors.com/media/ip_modules/pdf_2/papers/icc_2015_mutter_1.pdf) — CRC-15 and stuff-bit context.
