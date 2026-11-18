<!---

This file is used to generate your project datasheet. Please fill in the information below and delete any unused
sections.

You can also include images in this folder and reference them in the markdown. Each image must be less than
512 kb in size, and the combined size of all images must be less than 1 MB.
-->

## How it works

Metronome v4 is a programmable protocol emulator. Four timing lines generate or follow protocol clocks and schedule pin samples and output changes at programmable points within a bit period. Two execution cores run short bursts of move instructions in response to those events. Each core has room for 256 program words. Sticky status flags report missed deadlines and other execution errors.

The same hardware can load programs for UART, SPI, I2C and other wire formats. One resident demonstration captures an unfamiliar UART waveform, learns its rate and framing, then transmits the validated prefix. The host loads the demonstration once over SPI.

## How to test

Supply a 60 MHz clock and pulse `rst_n` low before loading an image. Use SPI mode 0, MSB first, at up to 3.75 MHz. The host drives SCK on `ui[0]`, CS_N on `ui[1]` and MOSI on `ui[2]`, and reads MISO on `uo[0]`. Apply the image's ordered writes, including the write that enables execution. After a power cycle or project reselection, reset and reload the image.

For the resident UART demonstration, run `python -m transcribe demo-image resident-uart.json` from `code/host2`. Load the image, send a 3.3 V UART signal to P5 (`uio[5]`), and capture the replay on O8 (`uo[2]`). The repository's `code/host2/transcribe/README.md` gives the stimulus, SPI transactions and expected readback.

The centralized v4 design passed Tiny Tapeout precheck and extracted setup and hold at a 16.667 ns period across the three nominal corners. The resident demonstration ran in RTL and routed gate-level simulation.

## External hardware

Use 3.3 V logic and a common ground for the UART demonstration. Add external components as the protocol requires, such as pull-ups for I2C or a suitable transceiver for a different physical layer.
