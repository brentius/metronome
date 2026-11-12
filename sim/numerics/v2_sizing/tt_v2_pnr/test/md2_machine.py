"""Machine description for Metronome v2: the single source of truth for v2 names and numbers.

v2 replaces v1's engines with lines (beat generator + pins + symbols) and threads (PC, trigger, watchers bound to a
line), adds two streams and a pipelined core, and moves write-only configuration into latches (BOTS/PLANS/V2_DESIGN.md
section 4). This file fixes the instruction fields, source ports, destination ports, guards, the jump-condition subset,
trigger sources, write groups and the configuration-bit inventory. Semantics are specified by SPEC v2 (to be written,
build step 2); until then V2_DESIGN.md section 4 is the reference.

It lives beside v1's code/md/ until the v2 RTL replaces v1 in src/ (D22). `python code/md2/gen.py` regenerates
code/md2/machine.json, code/md2/md2_defs.vh and wiki/ISA_TABLES_V2.md; `--check` fails on stale outputs.

Change policy: any edit here is an interface change (AGENTS.md). Regenerate, rerun tests, record it in DECISIONS.md.
"""
from __future__ import annotations

from dataclasses import dataclass

VERSION = 2

# ----------------------------------------------------------------------------------------------------------------
# Sizes (V2_DESIGN 4.4; the sizing run may change them)
# ----------------------------------------------------------------------------------------------------------------
N_CORES = 2          # each core has its own 256 x 64 program SRAM
N_LINES = 4          # beat generator + sampled pins + input/output symbol
N_THREADS = 6        # PC, trigger, two watchers; bound to one line and one core
N_STREAMS = 2
N_SHIFTERS = 2
N_COUNTERS = 3
N_LFSRS = 2
N_ACC_REGS = 4
N_PTRS = 1           # raw data-RAM pointer, for tables
N_FLAGS = 16
PROG_WORDS = 256     # per core
DATA_BYTES = 2048    # 512 x 32 SRAM (2 KB decided, V2_DESIGN 4.4)
BG_WIDTH = 16
DATA_WIDTH = 8
LFSR_WIDTH = 32
COUNTER_WIDTH = 16
OSYM_BITS = 4        # output symbol
ISYM_BITS = 2        # input symbol
N_SAMPLES = 4        # captured samples per beat {B1, A2, A1, A0}
LUT_IN_BITS = N_SAMPLES + 1      # input tables: samples + remembered bit
PIN_LUT_IN_BITS = 3 + 2          # pin tables: three selected symbol bits + 2-bit SEG
STREAM_ADDR_BITS = 11            # byte address in the 2 KB RAM
STREAM_LEN_BITS = 12             # byte count, 0..2048

# ----------------------------------------------------------------------------------------------------------------
# Pins (unchanged from v1, D8)
# ----------------------------------------------------------------------------------------------------------------
IN_PINS = [f"uio[{i}]" for i in range(8)] + [f"ui[{i}]" for i in range(3, 8)]
N_IN_PINS = len(IN_PINS)          # 13; select codes 13..15 read constant 0
OUT_PINS = [f"uio[{i}]" for i in range(8)] + [f"uo[{i}]" for i in range(2, 8)]
N_OUT_PINS = len(OUT_PINS)        # 14
N_OE_PINS = 8
HOST_PINS = {"SCK": "ui[0]", "CS_N": "ui[1]", "MOSI": "ui[2]", "MISO": "uo[0]", "IRQ": "uo[1]"}

# ----------------------------------------------------------------------------------------------------------------
# Instruction word (64 bits, LSB first). v1 layout plus the 5-bit jump condition in the former reserved bits.
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
FIELDS.append(Field("jcond", 59, 5))
FIELD = {f.name: f for f in FIELDS}

JMODES = {"next": 0, "always": 1, "if": 2, "ifnot": 3}   # jump to imm: never / always / if jcond / if !jcond
GUARDS = {"always": 0, "if": 1, "ifnot": 2, "never": 3}  # per-move guard relative to the instruction's cond


# ----------------------------------------------------------------------------------------------------------------
# Ports. Index = position in the list. "L." and "T." name the executing thread's line and the thread itself.
# ----------------------------------------------------------------------------------------------------------------
@dataclass
class Port:
    name: str
    desc: str
    unit: str
    idx: int = -1           # unit instance, -1 for singletons or thread-relative ports


def _fam(prefix: str, n: int, suffix: str, desc: str, unit: str) -> list[Port]:
    return [Port(f"{prefix}{k}.{suffix}", desc.replace("{k}", str(k)), unit, k) for k in range(n)]


SRC: list[Port] = [
    Port("ZERO", "constant 0", "const"),
    Port("IMM", "the instruction's 8-bit imm field", "const"),
    Port("L.IN", "line's 2-bit input symbol (bits 1:0), from the snapshot and the remembered bit", "line"),
    Port("L.CAP", "line's snapshot {REM, B1, A2, A1, A0} (bits 4:0)", "line"),
    Port("FLAGS.LO", "flags 7..0", "flags"),
    Port("FLAGS.HI", "flags 15..8", "flags"),
    Port("PINS.LO", "synchronised input pins P7..P0", "pins"),
    Port("PINS.HI", "synchronised input pins P12..P8 (bits 4:0)", "pins"),
    Port("ACC", "accumulator", "acc"),
    *[Port(f"R{k}", f"scratch register {k}", "acc", k) for k in range(N_ACC_REGS)],
    *_fam("SH", N_SHIFTERS, "D", "shifter {k} data", "shifter"),
    *_fam("SH", N_SHIFTERS, "O", "shifter {k} out bit (bit 0)", "shifter"),
    *_fam("CNT", N_COUNTERS, "LO", "counter {k} bits 7..0", "counter"),
    *_fam("CNT", N_COUNTERS, "HI", "counter {k} bits 15..8", "counter"),
    *[p for k in range(N_LFSRS) for p in
      [Port(f"LF{k}.B{b}", f"LFSR {k} state bits {8*b+7}..{8*b}", "lfsr", k) for b in range(4)]],
    *_fam("LF", N_LFSRS, "O", "LFSR {k} out bit, state bit 0 (bit 0)", "lfsr"),
    *_fam("P", N_PTRS, "D", "pointer {k} prefetched data byte mem[ptr]", "mem"),
    *_fam("S", N_STREAMS, "BIT", "stream {k} current transmit bit (bit 0)", "stream"),
    *_fam("S", N_STREAMS, "BYTE", "stream {k} last completed receive byte, or current transmit byte", "stream"),
    Port("HOST.IN", "byte from the host mailbox (reading clears HOST.INV)", "host"),
]

DST: list[Port] = [
    Port("NULL", "discard", "const"),
    Port("L.SYM", "stage the line's whole 4-bit output symbol := bus[3:0]", "line"),
    Port("L.DBIT", "stage only the data bit: symbol bit 0 := bus[0]", "line"),
    Port("L.XOR", "staged symbol ^= bus[3:0]", "line"),
    Port("T.STOP", "disable the executing thread after this burst (data ignored)", "thread"),
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
    *_fam("S", N_STREAMS, "ADV", "stream {k} transmit: advance to the next bit (data ignored)", "stream"),
    *_fam("S", N_STREAMS, "RX", "stream {k} receive: append bit bus[0]", "stream"),
    *_fam("S", N_STREAMS, "CTL", "stream {k}: bus[0] rewind to start, bus[1] flush a partial receive byte", "stream"),
    *_fam("L", N_LINES, "CTL", "line {k} beat generator: bus[0] RUN, bus[1] ARM, bus[2] REN", "line"),
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
    Port("L.IN0", "line input symbol bit 0", "line"),
    Port("L.IN1", "line input symbol bit 1", "line"),
    Port("L.SYNC", "an edge was accepted by the line's beat generator during the previous beat", "line"),
    Port("L.PINA", "live synchronised level of the line's pin A", "line"),
    Port("L.PINB", "live synchronised level of the line's pin B", "line"),
    *_fam("LF", N_LFSRS, "OUT", "LFSR {k} state bit 0", "lfsr"),
    Port("HOST.INV", "host mailbox holds an unread byte", "host"),
    Port("HOST.OUTE", "outgoing host mailbox is empty", "host"),
    *_fam("P", N_PTRS, "RDY", "pointer {k} prefetched data is valid", "mem"),
    *_fam("S", N_STREAMS, "END", "stream {k} length exhausted", "stream"),
    *_fam("S", N_STREAMS, "MARK", "stream {k} position equals its mark", "stream"),
    *_fam("S", N_STREAMS, "BYTE", "stream {k} is at a byte boundary", "stream"),
    *_fam("S", N_STREAMS, "BIT", "stream {k} current transmit bit", "stream"),
    *[Port(f"PIN{k}", f"synchronised level of input pin P{k} ({IN_PINS[k]})", "pins", k) for k in range(N_IN_PINS)],
    *_fam("L", N_LINES, "RUN", "line {k} beat generator is running", "line"),
]

# Jump conditions: the 5-bit jcond field indexes this subset of GUARD_CONDS (V2_DESIGN 4.5). Chosen for loop and
# field control: flags 0..7, shifter and counter ends, accumulator flags, line input and sync, host mailbox,
# pointer ready and every stream status. Per-pin levels, flags 8..15, shifter out bits and line RUN are move guards
# only; a program that must jump on one copies it to a flag or uses it as the move condition.
JUMP_GUARDS: list[str] = [
    "TRUE", *[f"F{k}" for k in range(8)],
    *[f"SH{k}.DONE" for k in range(N_SHIFTERS)], *[f"CNT{k}.Z" for k in range(N_COUNTERS)],
    "ACC.Z", "ACC.C", "ACC.N", "L.IN0", "L.IN1", "L.SYNC", "L.PINA",
    "HOST.INV", "HOST.OUTE", *[f"P{k}.RDY" for k in range(N_PTRS)],
    *[f"S{k}.{s}" for k in range(N_STREAMS) for s in ("END", "MARK", "BYTE", "BIT")],
]

# Trigger sources (thread config TRIG, 5 bits). Line events are absolute; PINA events use the thread's line.
TRIGGERS: list[str] = ["NONE"]
for _g in range(N_LINES):
    TRIGGERS += [f"L{_g}.BEAT", f"L{_g}.TAP0", f"L{_g}.TAP1", f"L{_g}.TAP2"]
TRIGGERS += [f"FLAG{_k}.RISE" for _k in range(8)]
TRIGGERS += ["PINA.RISE", "PINA.FALL", "PINA.EDGE", "HOST.INV", "ALWAYS"]

# Write groups (SPEC v1 6, D4; one group per line for the three symbol ports, V2_DESIGN 4.2). Two or more enabled
# moves to one group in a cycle set CONFLICT. "L.SYM" and "T.STOP" resolve to the executing thread's line or thread.
WRITE_GROUPS: dict[str, list[str]] = {
    "L.SYM": ["L.SYM", "L.DBIT", "L.XOR"],
    "T.STOP": ["T.STOP"],
    "FLAGS": ["FLAGS.SET", "FLAGS.CLR"],
    "ACC": ["ACC.LD", "ACC.ADD", "ACC.SUB", "ACC.AND", "ACC.OR", "ACC.XOR", "ACC.CMP"],
    **{f"R{k}": [f"R{k}"] for k in range(N_ACC_REGS)},
    **{f"SH{k}": [f"SH{k}.LD", f"SH{k}.SH"] for k in range(N_SHIFTERS)},
    **{f"SH{k}.CFG": [f"SH{k}.CFG"] for k in range(N_SHIFTERS)},
    **{f"CNT{k}": [f"CNT{k}.LO", f"CNT{k}.HI", f"CNT{k}.DEC"] for k in range(N_COUNTERS)},
    **{f"LF{k}": [f"LF{k}.ST"] + [f"LF{k}.B{b}" for b in range(4)] for k in range(N_LFSRS)},
    **{f"P{k}": [f"P{k}.AL", f"P{k}.AH", f"P{k}.W", f"P{k}.R"] for k in range(N_PTRS)},
    **{f"S{k}": [f"S{k}.ADV", f"S{k}.RX", f"S{k}.CTL"] for k in range(N_STREAMS)},
    **{f"L{k}.CTL": [f"L{k}.CTL"] for k in range(N_LINES)},
    "HOST.OUT": ["HOST.OUT"],
}

# ----------------------------------------------------------------------------------------------------------------
# Host-written configuration held in latches (V2_DESIGN 4.7): field -> bits, per block instance. The host map
# (addresses) is fixed by SPEC v2; this inventory sizes the latch block. State that programs or hardware change
# (PC, READY, thread EN, shifter CFG, PHASE, RUN/ARM/REN, stream position) stays in flops and is not listed.
# ----------------------------------------------------------------------------------------------------------------
LINE_CFG = {   # beat generator, edge sources, snapshot, pins, input tables
    "INC": 16, "MOD": 16, "T0": 16, "T1": 16, "T2": 16, "PRE": 16, "WLO": 16, "WHI": 16,
    "WEN": 1, "EDGE": 6,            # boundary edge: pin select 4, polarity 2
    "T0EDGE": 6, "T0SRC": 1,        # follower mode: tap 0 from a second edge select (V2_DESIGN 4.1)
    "SNAP": 2,                      # snapshot tap
    "PINA": 4, "PINB": 4,
    "LUT0": 1 << LUT_IN_BITS, "LUT1": 1 << LUT_IN_BITS,
}
THREAD_CFG = {"CORE": 1, "LINE": 2, "TRIG": 5, "W0C": 6, "W1C": 6, "W0H": 8, "W1H": 8}
OUT_CFG = {"LINE": 2, "BOUND": 1, "SEL": 3 * 2, "LUT": 1 << PIN_LUT_IN_BITS}
OE_CFG = {"OE": 1 << PIN_LUT_IN_BITS}          # pins O0..O7 only
LFSR_CFG = {"POLY": LFSR_WIDTH}
STREAM_CFG = {"MODE": 1, "MSB": 1, "START": STREAM_ADDR_BITS, "LEN": STREAM_LEN_BITS, "MARK": STREAM_LEN_BITS}

CONFIG_BLOCKS = {   # block -> (fields, instances)
    "line": (LINE_CFG, N_LINES),
    "thread": (THREAD_CFG, N_THREADS),
    "out": (OUT_CFG, N_OUT_PINS),
    "oe": (OE_CFG, N_OE_PINS),
    "lfsr": (LFSR_CFG, N_LFSRS),
    "stream": (STREAM_CFG, N_STREAMS),
}
CONFIG_BITS = {b: sum(f.values()) * n for b, (f, n) in CONFIG_BLOCKS.items()}
CONFIG_BITS_TOTAL = sum(CONFIG_BITS.values())

for _lst, _w, _what in [(SRC, 6, "sources"), (DST, 6, "destinations"), (GUARD_CONDS, 6, "guards"),
                        (JUMP_GUARDS, 5, "jump guards"), (TRIGGERS, 5, "triggers")]:
    assert len(_lst) <= (1 << _w), f"too many {_what}: {len(_lst)}"

SRC_ID = {p.name: i for i, p in enumerate(SRC)}
DST_ID = {p.name: i for i, p in enumerate(DST)}
GUARD_ID = {p.name: i for i, p in enumerate(GUARD_CONDS)}
JGUARD_ID = {n: i for i, n in enumerate(JUMP_GUARDS)}
TRIG_ID = {n: i for i, n in enumerate(TRIGGERS)}
