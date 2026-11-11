<!---

This file is used to generate your project datasheet. Please fill in the information below and delete any unused
sections.

You can also include images in this folder and reference them in the markdown. Each image must be less than
512 kb in size, and the combined size of all images must be less than 1 MB.
-->

## How it works

Metronome is a protocol emulator that you program instead of rewire. Programs run on the protocol's own bit clock rather than the chip clock. Hardware beat generators produce or recover that bit clock. Short, loop-free bursts of move instructions run between beats, and pin reads and writes happen on beat taps, never on instruction count. A burst that misses its deadline raises a sticky flag instead of corrupting the waveform.

*Status: v2.0 is in progress. The design in `src/` is the v1.0 Metronome RTL, ported into the official Tiny Tapeout template as the baseline for v2.0.*

## How to test

A host microcontroller (the demo board's RP2350) loads the program and configuration over the SPI target port (HOST_SCK, HOST_CS_N, HOST_MOSI, HOST_MISO), then sets RUN. HOST_IRQ signals data for the host. Protocol pins are P0..P12 (inputs) and O0..O13 (outputs); uio pins are bidirectional, with output enable under program control.

## External hardware

None required for 3.3 V protocols. Transceivers or pull-ups on a Pmod as the protocol needs (for example pull-ups for I2C, a 10BASE-T transformer and driver for Ethernet).
