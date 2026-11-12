"""Helpers: assemble an example, load its image into the v2 model, step it, observe pins."""
from pathlib import Path

from metronome2 import Chip, m, spi
from metronome2_tools.asm import assemble_file, assemble_text
from metronome2_tools.image import build_image, host_writes, image_writes

EXAMPLES = Path(__file__).resolve().parents[1] / "examples"
IDLE = 0x02          # ui_in: CS_N high


def example(name):
    return assemble_file(EXAMPLES / f"{name}.mas")


def load(chip, prog):
    """Apply the ordered host writes of `prog` instantly (backdoor); returns the write list."""
    writes = host_writes(prog)
    for addr, data, _note in writes:
        chip.backdoor_write(addr, data)
    return writes


def spi_load(chip, prog, half_period=8):
    """Apply the image over the SPI link at clk/16 (the cycle-accurate host path).  Returns the cycle count and the
    list of cycles in which a configuration write strobe was active (D24 evidence)."""
    from metronome2 import regs
    cfg_cycles = []
    n = 0
    for addr, data, _ in host_writes(prog):
        for i in range(0, len(data), 64):
            frames = spi.write_frames(addr + i, data[i:i + 64], half_period)
            for f in frames:
                chip.step(f)
                if chip.host.WR is not None and regs.is_config(chip.host.ADDR):
                    cfg_cycles.append(n)
                n += 1
    return n, cfg_cycles


def pin_trace(chip, cycles, pin_fn, ui=IDLE, uio_fn=None):
    """Step `cycles` cycles; pin_fn(uo, uio_out, uio_oe) -> sample.  uio_fn(cycle) -> uio_in."""
    out = []
    for c in range(cycles):
        uo, uio_out, uio_oe = chip.step(ui, uio_fn(c) if uio_fn else 0)
        out.append(pin_fn(uo, uio_out, uio_oe))
    return out


def runs(trace):
    """[(level, start_index, length)] of constant runs."""
    out, s = [], 0
    for i in range(1, len(trace) + 1):
        if i == len(trace) or trace[i] != trace[s]:
            out.append((trace[s], s, i - s))
            s = i
    return out


def lut(fn, bits=5):
    """Truth table as an int: bit idx = fn(idx)."""
    return sum((fn(i) & 1) << i for i in range(1 << bits))
