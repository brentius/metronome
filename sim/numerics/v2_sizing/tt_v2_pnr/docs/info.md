<!---

This file is used to generate your project datasheet. Please fill in the information below and delete any unused
sections.

You can also include images in this folder and reference them in the markdown. Each image must be less than
512 kb in size, and the combined size of all images must be less than 1 MB.
-->

## How it works

This is the Metronome v2 place-and-route sizing build, not the v2 design. It puts the v2 sizing blocks into one
Tiny Tapeout top so that the official flow can place, route and time them together at 60 MHz on 8x4 tiles:

- two pipelined cores (`md2_core`), each with a 256x64 IHP program SRAM (`md2_pmem`, instances `u_pmem0.u_sram`
  and `u_pmem1.u_sram`), and six thread state slices (`md2_core_thread`);
- thread and stream configuration in a 56-byte bank of IHP latches with one clock gate per byte (`cfg_latch_bank`,
  cells `sg13cmos5l_dlhrq_1` and `sg13cmos5l_lgcp_1`);
- one stream (`md2_stream`) on the 512x32 IHP data SRAM (`md2_dmem`, instance `u_dmem.u_sram`); the RAM port
  goes to the stream first and then to the host;
- the v2 SPI host link (`md2_host`);
- a stand-in for the commons (`md2_commons_stub`). All 58 destinations write registers or cheap functional
  stand-ins, every source reads through each core's full source multiplexer, and the guards come from registers,
  synchronised pins and the real stream's status.

The host map, the commons and the thread start rules below are sizing choices. SPEC v2 will fix the real ones.

### Pins

| Pin | Use |
|---|---|
| ui[0], ui[1], ui[2] | Host SPI SCK, CS_N, MOSI (SPI mode 0, MSB first, SCK at most clk/16) |
| ui[7:3] | Input pins P12..P8 (2-flop synchronised) |
| uio_in[7:0] | Input pins P7..P0 (2-flop synchronised); line k uses P(2k) as PINA and P(2k+1) as PINB |
| uo[0], uo[1] | Host MISO; IRQ (= HOST.OUTV, a byte waits in the outgoing mailbox) |
| uo[5:2] | Line 0 symbol (4 bits) |
| uo[6], uo[7] | Parity of the line 1 symbol; parity of the line 2 and line 3 symbols |
| uio_out[7:0], uio_oe[7:0] | Register R0; register R1 |

### Host protocol

A frame is CS_N low, a command byte, a 16-bit address (high byte first), then data bytes. The address increments
after each data byte. Command 0x02 writes and 0x03 reads; any other command ignores the rest of the frame.
Reads work only for the data RAM and the control block. Other addresses read 0.

### Host map (sizing)

| Address | Access | Contents |
|---|---|---|
| 0x0000 + core x 0x800 + 8 x word + byte | W | Program SRAM of `core` (0 or 1), byte `byte` (0 = bits 7:0) of 64-bit word `word` (0..255). Writes take the SRAM port from the core, so write programs while RUN = 0 and the cores are idle |
| 0x1000..0x17FF | R/W | Data RAM bytes (byte address = address - 0x1000, little-endian within each 32-bit word) |
| 0x2000 + 8 x t + n | W | Thread t (0..5) configuration, latch byte n: 0 = {bit 3 EN, bits 2:1 LINE, bit 0 CORE}; 1 = TRIG (5 bits); 2 = W0C (6); 3 = W1C (6); 4 = W0H; 5 = W1H; 6 = start PC; 7 reserved |
| 0x2030..0x2037 | W | Stream S0 configuration: 0x30 = {bit 1 MSB first, bit 0 MODE (1 = receive)}; 0x31/0x32 = START[7:0]/[10:8]; 0x33/0x34 = LEN[7:0]/[11:8]; 0x35/0x36 = MARK[7:0]/[11:8]; 0x37 reserved |
| 0x2400 | R/W | Bit 0 RUN. On RUN 0 -> 1 every thread loads EN and its PC from configuration bytes 0 and 6 |
| 0x2401 | W | Doorbell: bit t triggers thread t once |
| 0x2402 | R | ID, 0xA2 |
| 0x2403 | R/W | Read: {S0.STARVED, S0.END, RUNNING[5:0]}. Write (any value): clear S0.STARVED |
| 0x2404 | R/W | Write: HOST.IN mailbox byte (sets HOST.INV). Read: HOST.OUT byte (clears HOST.OUTV) |
| 0x2405 | R | {HOST.OUTV, HOST.INV, thread EN[5:0]} |
| 0x2406, 0x2407 | R | S0 position POS[7:0]; {0, BITIDX[2:0], POS[11:8]} |
| 0x2408, 0x2409 | R | Thread OVR[5:0]; thread READY[5:0] |

Configuration latches reach the logic two clock cycles after the write strobe. Writes in the first two cycles
after reset is released are ignored.

### Triggers and stand-ins

A thread triggers on its doorbell, or on its TRIG setting: ALWAYS, FLAGn.RISE for flags 0..7, PINA.RISE, PINA.FALL
and PINA.EDGE on its line's pin A, or HOST.INV rising. Beat-generator triggers are not built. The line symbols
are written directly, with no commit on the beat. HOST.OUT also clears HOST.INV: the core does not export source
codes, so the rule that reading HOST.IN clears it cannot be built here. The LFSR polynomial is fixed at 0xEDB88320.
Stream S1 is a small rotator, and the pointer P0 is a register that does not access the RAM.

## How to test

`test/test.py` loads a short program into core 0 over SPI, places 0xA5 in the data RAM, configures thread 0
(core 0, line 0, EN) and stream S0 (transmit, START 0, LEN 1), sets RUN and rings the doorbell. R0 on uio_out must
go 0x00 -> 0x11 -> 0x33. The move of 0xEE on a taken jump's wrong path must never appear. R1 on uio_oe must be
0x22. Each further doorbell moves one stream bit to uo[2], giving 1, 0, 1, 0, 0, 1, 0, 1. Run it with `make` in
`test/` (RTL) or `make GATES=yes` (gate level). Without make, run `python test/run_local.py`.

## External hardware

An SPI controller (the demo board's RP2350) on ui[0..2] and uo[0..1].
