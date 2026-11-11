"""Machine description: the single source of truth for the Metronome v1 machine.

Everything that must agree between the RTL, the assembler, the reference model and the documentation lives here:
instruction field layout, source ports, destination ports, guard conditions, trigger sources, unit counts, pin map
and the host address map. `python code/md/gen.py` regenerates the derived files (Verilog header, JSON, doc tables).
Semantics are specified in wiki/SPEC.md; this file only names and numbers things.

Change policy: any edit here is an interface change (AGENTS.md). Regenerate, rerun all tests, record it in
BOTS/PLANS/DECISIONS.md.
"""
from __future__ import annotations

from dataclasses import dataclass, field

VERSION = 1

# ----------------------------------------------------------------------------------------------------------------
# Sizes (parameters; the sizing run may change them)
# ----------------------------------------------------------------------------------------------------------------
N_CORES = 2          # each core has its own 256 x 64 program SRAM
N_ENGINES = 6        # threads of control
N_BEATGENS = 4       # beat generators
N_SHIFTERS = 4
N_COUNTERS = 4
N_LFSRS = 2
N_ACC_REGS = 4       # scratch registers beside the accumulator
N_PTRS = 2           # data-RAM pointers
N_FLAGS = 16
PROG_WORDS = 256     # per core
DATA_BYTES = 2048    # data RAM (512 x 32 SRAM with bit mask, or behavioural model)
BG_WIDTH = 16        # beat generator phase width
DATA_WIDTH = 8       # move bus width
LFSR_WIDTH = 32
COUNTER_WIDTH = 16

# ----------------------------------------------------------------------------------------------------------------
# Pins
# ----------------------------------------------------------------------------------------------------------------
# Input-capable protocol pins P0..P12 (synchronised): uio_in[0..7] then ui_in[3..7].
IN_PINS = [f"uio[{i}]" for i in range(8)] + [f"ui[{i}]" for i in range(3, 8)]
N_IN_PINS = len(IN_PINS)          # 13; select codes 13..15 read constant 0
# Output-capable protocol pins O0..O13: uio_out[0..7] (with output enable), then uo_out[2..7].
OUT_PINS = [f"uio[{i}]" for i in range(8)] + [f"uo[{i}]" for i in range(2, 8)]
N_OUT_PINS = len(OUT_PINS)        # 14
N_OE_PINS = 8                     # O0..O7 have an output-enable table
# Host link (SPI target, mode 0): ui[0]=SCK, ui[1]=CS_N, ui[2]=MOSI, uo[0]=MISO, uo[1]=IRQ.
HOST_PINS = {"SCK": "ui[0]", "CS_N": "ui[1]", "MOSI": "ui[2]", "MISO": "uo[0]", "IRQ": "uo[1]"}

# ----------------------------------------------------------------------------------------------------------------
# Instruction word (64 bits, LSB first)
# ----------------------------------------------------------------------------------------------------------------
@dataclass(frozen=True)
class Field:
    name: str
    lsb: int
    width: int

    @property
    def msb(self) -> int:
        return self.lsb + self.width - 1


INSN_BITS = 64
N_MOVES = 3
FIELDS = [Field("pause", 0, 1), Field("jmode", 1, 2), Field("imm", 3, 8), Field("cond", 11, 6)]
for _m in range(N_MOVES):
    _b = 17 + 14 * _m
    FIELDS += [Field(f"m{_m}_guard", _b, 2), Field(f"m{_m}_src", _b + 2, 6), Field(f"m{_m}_dst", _b + 8, 6)]
FIELDS.append(Field("reserved", 59, 5))
FIELD = {f.name: f for f in FIELDS}

JMODES = {"next": 0, "always": 1, "if": 2, "ifnot": 3}       # jump to imm: never / always / if cond / if !cond
GUARDS = {"always": 0, "if": 1, "ifnot": 2, "never": 3}      # per-move guard relative to the instruction's cond

# ----------------------------------------------------------------------------------------------------------------
# Ports. Each entry: (name, description). Index = position in the list. "k" families are expanded below.
# ----------------------------------------------------------------------------------------------------------------
@dataclass
class Port:
    name: str
    desc: str
    unit: str
    idx: int = -1           # unit instance, -1 for singletons


def _fam(prefix: str, n: int, suffix: str, desc: str, unit: str) -> list[Port]:
    return [Port(f"{prefix}{k}.{suffix}", desc.replace("{k}", str(k)), unit, k) for k in range(n)]


SRC: list[Port] = [
    Port("ZERO", "constant 0", "const"),
    Port("IMM", "the instruction's 8-bit imm field", "const"),
    Port("E.IN", "executing engine's 2-bit input symbol (bits 1:0)", "engine"),
    Port("E.CAP", "executing engine's captured bits {B1,A2,A1,A0} (bits 3:0)", "engine"),
    Port("FLAGS.LO", "flags 7..0", "flags"),
    Port("FLAGS.HI", "flags 15..8", "flags"),
    Port("PINS.LO", "synchronised input pins P7..P0", "pins"),
    Port("PINS.HI", "synchronised input pins P12..P8 (bits 4:0)", "pins"),
    Port("ACC", "accumulator", "acc"),
    *[Port(f"R{k}", f"scratch register {k}", "acc", k) for k in range(N_ACC_REGS)],
    *_fam("SH", N_SHIFTERS, "D", "shifter {k} data", "shifter"),
    *_fam("SH", N_SHIFTERS, "O", "shifter {k} out bit (bit 0 of the bus)", "shifter"),
    *_fam("CNT", N_COUNTERS, "LO", "counter {k} bits 7..0", "counter"),
    *_fam("CNT", N_COUNTERS, "HI", "counter {k} bits 15..8", "counter"),
    *[p for k in range(N_LFSRS) for p in
      [Port(f"LF{k}.B{b}", f"LFSR {k} state bits {8*b+7}..{8*b}", "lfsr", k) for b in range(4)]],
    *_fam("P", N_PTRS, "D", "pointer {k} prefetched data byte mem[ptr]", "mem"),
    Port("HOST.IN", "byte from the host mailbox (reading clears HOST.INV)", "host"),
]

DST: list[Port] = [
    Port("NULL", "discard", "const"),
    Port("E.SYM", "stage the executing engine's output symbol (bits 1:0)", "engine"),
    Port("E.STOP", "disable the executing engine after this burst (data ignored)", "engine"),
    Port("FLAGS.SET", "set flag number bus[3:0]", "flags"),
    Port("FLAGS.CLR", "clear flag number bus[3:0]", "flags"),
    Port("ACC.LD", "ACC := bus", "acc"),
    Port("ACC.ADD", "ACC := ACC + bus (C = carry out)", "acc"),
    Port("ACC.SUB", "ACC := ACC - bus (C = no borrow)", "acc"),
    Port("ACC.AND", "ACC := ACC & bus", "acc"),
    Port("ACC.OR", "ACC := ACC | bus", "acc"),
    Port("ACC.XOR", "ACC := ACC ^ bus", "acc"),
    Port("ACC.CMP", "flags from ACC - bus, ACC unchanged", "acc"),
    *[Port(f"R{k}", f"scratch register {k} := bus", "acc", k) for k in range(N_ACC_REGS)],
    *_fam("SH", N_SHIFTERS, "LD", "shifter {k}: data := bus, count := length", "shifter"),
    *_fam("SH", N_SHIFTERS, "SH", "shifter {k}: shift once, shifting in bus[0]; count -= 1", "shifter"),
    *_fam("SH", N_SHIFTERS, "CFG", "shifter {k}: bus[3:0] = length 1..8 (0 means 8), bus[4] = MSB first", "shifter"),
    *_fam("CNT", N_COUNTERS, "LO", "counter {k}: bits 7..0 := bus", "counter"),
    *_fam("CNT", N_COUNTERS, "HI", "counter {k}: bits 15..8 := bus", "counter"),
    *_fam("CNT", N_COUNTERS, "DEC", "counter {k}: decrement, saturating at 0 (data ignored)", "counter"),
    *_fam("LF", N_LFSRS, "ST", "LFSR {k}: one step with input bit bus[0]", "lfsr"),
    *[p for k in range(N_LFSRS) for p in
      [Port(f"LF{k}.B{b}", f"LFSR {k} state bits {8*b+7}..{8*b} := bus", "lfsr", k) for b in range(4)]],
    *_fam("P", N_PTRS, "AL", "pointer {k} address bits 7..0 := bus", "mem"),
    *_fam("P", N_PTRS, "AH", "pointer {k} address bits 10..8 := bus[2:0] (and starts a prefetch)", "mem"),
    *_fam("P", N_PTRS, "W", "pointer {k}: mem[ptr] := bus, ptr += 1", "mem"),
    *_fam("P", N_PTRS, "R", "pointer {k}: ptr += 1 and prefetch the next byte (data ignored)", "mem"),
    *_fam("BG", N_BEATGENS, "CTL", "beat generator {k}: bus[0] RUN, bus[1] ARM, bus[2] REN", "beatgen"),
    Port("HOST.OUT", "byte to the host mailbox (sets HOST.OUTV, raises IRQ)", "host"),
]

GUARD_CONDS: list[Port] = [
    Port("TRUE", "always true", "const"),
    *[Port(f"F{k}", f"flag {k}", "flags", k) for k in range(N_FLAGS)],
    *_fam("SH", N_SHIFTERS, "DONE", "shifter {k} count is 0", "shifter"),
    *_fam("SH", N_SHIFTERS, "OUT", "shifter {k} out bit", "shifter"),
    *_fam("CNT", N_COUNTERS, "Z", "counter {k} is 0", "counter"),
    Port("ACC.Z", "accumulator result zero", "acc"),
    Port("ACC.C", "accumulator carry / no borrow", "acc"),
    Port("ACC.N", "accumulator result bit 7", "acc"),
    Port("E.IN0", "executing engine input symbol bit 0", "engine"),
    Port("E.IN1", "executing engine input symbol bit 1", "engine"),
    Port("E.SYNC", "an edge was accepted by the engine's beat generator during the previous beat", "engine"),
    Port("E.PINA", "live synchronised level of the engine's pin A", "engine"),
    Port("E.PINB", "live synchronised level of the engine's pin B", "engine"),
    *_fam("LF", N_LFSRS, "OUT", "LFSR {k} state bit 0", "lfsr"),
    Port("HOST.INV", "host mailbox holds an unread byte", "host"),
    Port("HOST.OUTE", "outgoing host mailbox is empty", "host"),
    *_fam("P", N_PTRS, "RDY", "pointer {k} prefetched data is valid", "mem"),
    *[Port(f"PIN{k}", f"synchronised level of input pin P{k} ({IN_PINS[k]})", "pins", k) for k in range(N_IN_PINS)],
    *_fam("BG", N_BEATGENS, "RUN", "beat generator {k} is running", "beatgen"),
]

# Trigger sources (engine config TRIG, 5 bits)
TRIGGERS: list[str] = ["NONE"]
for _g in range(N_BEATGENS):
    TRIGGERS += [f"BG{_g}.BEAT", f"BG{_g}.TAP0", f"BG{_g}.TAP1", f"BG{_g}.TAP2"]
TRIGGERS += [f"FLAG{_k}.RISE" for _k in range(8)]
TRIGGERS += ["PINA.RISE", "PINA.FALL", "PINA.EDGE", "HOST.INV", "ALWAYS"]
assert len(TRIGGERS) <= 32

for _lst, _w, _what in [(SRC, 6, "sources"), (DST, 6, "destinations"), (GUARD_CONDS, 6, "guards")]:
    assert len(_lst) <= (1 << _w), f"too many {_what}: {len(_lst)}"

SRC_ID = {p.name: i for i, p in enumerate(SRC)}
DST_ID = {p.name: i for i, p in enumerate(DST)}
GUARD_ID = {p.name: i for i, p in enumerate(GUARD_CONDS)}
TRIG_ID = {n: i for i, n in enumerate(TRIGGERS)}

# ----------------------------------------------------------------------------------------------------------------
# Host address map (16-bit byte addresses over the SPI link). Configuration registers are little-endian bytes.
# ----------------------------------------------------------------------------------------------------------------
HOST_MAP = {
    "PROG_BASE": 0x0000,      # core c program: PROG_BASE + c*0x800 + word*8 + byte; word written when byte 7 lands
    "DATA_BASE": 0x1000,      # data RAM bytes 0x1000..0x17FF
    "BG_BASE": 0x2000,        # beat generator g: 0x2000 + g*0x20
    "ENG_BASE": 0x2100,       # engine e: 0x2100 + e*0x20
    "OUT_BASE": 0x2200,       # output cell o: 0x2200 + o*0x08
    "UNIT_BASE": 0x2300,      # unit configuration (shifter cfg, LFSR poly)
    "CTRL_BASE": 0x2400,      # global control and status
}

BG_REGS = {  # offset: (name, bytes)
    0x00: ("INC", 2), 0x02: ("MOD", 2), 0x04: ("T0", 2), 0x06: ("T1", 2), 0x08: ("T2", 2),
    0x0A: ("PRE", 2), 0x0C: ("WLO", 2), 0x0E: ("WHI", 2), 0x10: ("PHASE", 2),
    0x12: ("CTL", 1),        # bit0 RUN, bit1 ARM, bit2 REN, bit3 WEN
    0x13: ("EDGE", 1),       # bits3:0 pin select, bits5:4 polarity: 0 none, 1 rise, 2 fall, 3 both
}
ENG_REGS = {
    0x00: ("PC", 1), 0x01: ("CFG", 1),     # CFG bit0 EN, bit1 core, bits3:2 beat generator
    0x02: ("TRIG", 1), 0x03: ("PINS", 1),  # PINS bits3:0 pin A, bits7:4 pin B
    0x04: ("LUT0", 2), 0x06: ("LUT1", 2),  # input symbol tables, index {B1,A2,A1,A0}
    0x08: ("W0C", 1), 0x09: ("W0H", 1), 0x0A: ("W1C", 1), 0x0B: ("W1H", 1),
    0x0C: ("SYM", 1),                      # read: bits1:0 staged, bits3:2 committed
    0x0D: ("STAT", 1),                     # read: bit0 ready, bit1 running, bit2 armed; sticky bit4 LATE, bit5 OVERRUN
}
OUT_REGS = {0x00: ("ENG", 1), 0x02: ("LUT", 2), 0x04: ("OE", 2)}   # LUT index {seg[1:0], sym[1:0]}
UNIT_REGS = {0x00 + 8 * k: (f"LF{k}.POLY", 4) for k in range(N_LFSRS)}
# Host-readable registers per block (D14, area): every other configuration register is write-only and reads 0.
# CTRL registers are all readable (as documented per register); program memory always reads 0.
HOST_READABLE = {
    "BG": ("PHASE", "CTL"),
    "ENG": ("PC", "SYM", "STAT"),
    "OUT": (),
    "UNIT": (),
}
CTRL_REGS = {
    0x00: ("RUN", 1),        # bit0 global run (engines dispatch only when set)
    0x01: ("STICKY", 1),     # bit0 CONFLICT, bit1 MEMHAZ; write 1 to clear
    0x02: ("IRQEN", 1),      # bit0 HOST.OUTV, bit1 any sticky error
    0x03: ("DOORBELL", 1),   # write: bit e triggers engine e (trigger source HOST.INV is separate)
    0x04: ("HOSTIN", 1),     # write: byte into the host->chip mailbox
    0x05: ("HOSTOUT", 1),    # read: byte from chip->host mailbox (no side effect)
    0x06: ("HOSTSTAT", 1),   # read: bit0 HOST.INV, bit1 HOST.OUTV; write 1 to bit1 clears HOST.OUTV
    0x07: ("ID", 1),         # read: 0xA0 | VERSION
}
