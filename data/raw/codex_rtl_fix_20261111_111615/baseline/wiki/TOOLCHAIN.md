# Toolchain (assembler, checks, images)

Code: `code/host/metronome_tools/`. Tests: `python -m pytest code/host -q`. All names and numbers come from `code/md/machine.py`; the tools hard-code no encodings. `wiki/SPEC.md` is normative.

Commands (run from `code/host`):

- `python -m metronome_tools.asm prog.mas -o prog.json [-l] [-v] [--no-check]` assembles, runs the checks, and writes the image. Check errors exit with code 2 and write no image.
- `python -m metronome_tools.check prog.mas` prints the full check report.
- `python -m metronome_tools.disasm prog.json` prints re-assemblable source.

## 1. Source syntax

- Comments start with `;`. (`//` is not a comment, because `//` is floor division in expressions.)
- Everything is case-insensitive for port, trigger and condition names. Labels and `.equ` names are case-sensitive.
- `label:` can stand alone or precede an instruction. Labels belong to the current `.core`.
- `.core N` selects the core. `.org A` sets that core's location counter. `.equ NAME expr` defines a constant. Expressions allow `+ - * // / % << >> & | ^ ~`, comparisons, `a if c else b`, `min max abs round maj rev`, labels and `.equ` names.

### Instructions

One line is one instruction (one 64-bit word):

```
[when COND]  [guard] src -> dst {, [guard] src -> dst}  [goto L [if|ifnot [COND]]]  [pause]
```

- `src` is a port name or `#expr`. `#expr` is an immediate (-128..255). `#0` becomes `ZERO` and uses no imm field.
- `dst` is a port name. The port tables are in `wiki/ISA_TABLES.md`.
- Up to 3 moves, separated by commas. Guards are relative to the instruction condition: `? move` runs if COND, `! move` runs if not COND, and `never move` is disabled.
- `when COND` sets the instruction condition. A `?`/`!` guard or `goto ... if/ifnot` needs one. `goto L if COND` is shorthand for `when COND ... goto L if`. `when` must be on the same line, before the moves.
- `goto L` jumps always. `goto L if` jumps when COND is true and `goto L ifnot` when it is false. Otherwise control continues at the next address.
- `pause` ends the burst. The next trigger resumes at the jump target or at the next address. `pause goto L` is the usual loop-back.
- `nop` is an empty instruction.

The imm field is shared by the jump target and every non-zero immediate. If the values differ, the assembler errors and says to split the instruction. Moves to the same write group (SPEC 6: `ACC.*`, `SHk.LD/SH`, `CNTk.*`, `LFk.*`, `Pk.*`, `FLAGS.*`, one `Rk`, ...) in one instruction are an error unless their guards are `?` and `!`. Two `E.SYM` moves guarded `?` and `!` are fine.

### Configuration directives

These become host writes. Block directives end with `.end`. Each line in a block is `key value...`.

```
.clock 60e6                       ; default 60 MHz; used by 'rate'
.beatgen N                        ; 0..3
    rate|baud HZ | period CYCLES | inc E / mod E
    taps T0 T1 T2                 ; phases; '-' disables (written as MOD). INC and MOD can be used in expressions
    preset E   phase E   window LO HI   edge PIN none|rise|fall|both
    ctl run arm ren wen           ; initial CTL ('window' sets wen)
.end
.engine N                         ; 0..5
    core C  beatgen G  trigger NAME   ; NAME from machine.TRIGGERS; beatgen defaults to the trigger's generator
    pins A=P8 B=uio[2]  | pina X | pinb X
    in0 EXPR / in1 EXPR           ; truth table over a0 a1 a2 b1 (e.g. maj(a0,a1,a2)); lut0/lut1 give raw values
    watch0 COND -> LABEL          ; watch1 likewise
    start LABEL  | pc E           ; initial PC
    enable | disable
.end
.out O8                           ; or uo[2], uio[3], or a number
    engine N | none
    lut EXPR      oe EXPR|always|never      ; over sym (0..3) and seg (0..3)
    seg0: v0 v1 v2 v3             ; readable LUT rows per segment, columns are symbols
    oeseg0: ...   lutraw E   oeraw E
.end
.lfsr N poly=P [width=W] [init=I] [reflected]   ; MSB-first definition; poly and init are bit-reversed (SPEC 6.1)
.lfsr N raw=REG [init=I]                        ; register form, used as written
.data ADDR byte|"text" ...        ; initial data RAM
.irqen outv error                 ; IRQ enable bits
.run on|off                       ; default on: CTRL.RUN is written last
.budget engine N cycles|insns V   ; see section 2
```

`.lfsr` defines `LFn_POLY`, `LFn_INIT` and `LFn_INIT_B0..B3`, so a program loads the CRC init with `#LF0_INIT_B0 -> LF0.B0`, and so on. `.beatgen` defines `BGn_INC`, `BGn_MOD` and `BGn_PERIOD`. Input pins are `P0..P12`, `uio[i]`/`ui[i]`, or `none`. Output pins are `O0..O13` or `uio[i]`/`uo[i]`. An unset tap is written as MOD (disabled). An unset engine or output cell is not written and keeps its reset value.

## 2. Static checks (`check.py`)

The model is SPEC 5. A trigger in cycle t gives the first instruction in t+2. A burst of n instructions on an idle core ends in cycle t+n+1, so the trigger-to-last-instruction time is n+1 cycles.

1. **Burst rule.** Pause nodes are removed from the control-flow graph, and any remaining cycle is an error that names the loop (for example `s(0x00) -> t(0x01) -> s(0x00)`). This covers every assembled instruction, reachable or not. An instruction that continues into unprogrammed memory is also an error.
2. **Burst lengths.** For each engine the entries are its start PC, its watcher handlers, and every resume point after a reachable `pause`. For each entry the checker reports the longest path (instructions) and the position of the last `E.SYM` write. Conditions are not correlated, so infeasible paths count. The result is conservative.
3. **Response time.** `resp = own worst burst + 1 + W`. W is the sum of the longest bursts of every other enabled engine on the same core, each counted once. This is conservative: it assumes each other engine fires once before ours runs, and it does not model starvation by a faster-triggering lower-numbered engine.
4. **Budgets.**
   - For `BGg.BEAT` and `BGg.TAPk` triggers the commit window is derived from INC, MOD and Tk. The last `E.SYM` write must land no later than the commit beat, otherwise the symbol would be LATE.
   - Also for `BGg.BEAT` and `BGg.TAPk` triggers, response + 1 must not exceed the minimum trigger spacing `floor(MOD/INC)`, otherwise OVR could occur. Edge re-alignment is not modelled, and the checker warns when it is configured.
   - `.budget engine N cycles V` bounds the full response. `.budget engine N insns V` bounds the burst length.
5. **Advisory warnings.** A missing `start`, a trigger on an unconfigured beat generator, and a write group written by several engines.

Every error names the engine, the burst entry and the path.

## 3. Program image and host link (`image.py`)

The JSON image holds `program` (informational copy of the words), `writes` (the complete ordered host write list with notes) and `labels`. Write order:

1. Program memory, little-endian 8-byte words (assumption: SPEC 9 does not state the byte order of the staging word).
2. Data RAM.
3. LFSR POLY.
4. Output cells.
5. Beat generator registers except CTL.
6. Engine registers, with CFG last.
7. Beat generator CTL.
8. IRQEN.
9. CTRL.RUN, last.

`spi_streams(writes, coalesce, max_frame)` builds mode-0 frames `0x02 | addr_hi | addr_lo | data...`. Address-contiguous writes are merged. `spi_read_frame(addr, n)` builds `0x03 | addr | n dummy bytes`, and `spi_read_result(miso, n)` takes MISO bytes 3..3+n-1 (our reading of SPEC 9). `decode_spi` and `apply_writes` are inverses for tests. Keep SCK at or below clk/16.

## 4. Disassembler

`disasm.py` prints source that re-assembles to the same words. Jump targets become labels `L<hex>`. A test checks this on 500 random instructions.

## 5. Spec resolutions (SPEC 9a) and how they affect the tools

- INC must be below MOD (9a.6). The assembler rejects `inc >= mod`, and `rate` at or above the clock.
- Unused source, destination, guard and trigger codes read 0, act as NULL, evaluate false, and never fire (9a.1). The tools only emit named ports. `decode` maps out-of-range fields to ZERO/NULL/TRUE, a disassembly-only simplification of the false-guard rule.
- Host reads have no side effects, and HOSTSTAT bit 1 is write-1-to-clear for OUTV. The tools write neither: the images never read or write HOSTSTAT, and the `uart_tx`/`uart_rx` host protocol only reads HOSTSTAT/HOSTOUT.
- Taps at or above MOD are disabled (9a.10), which is how unset taps are written.
- Program loading while RUN is 0 (9a.8) matches the write order: RUN is written last. Re-downloading to a running chip is the caller's responsibility.

## 6. Running the tests

`python -m pytest code/host -q` (448 tests at the time of writing). `conftest.py` puts `code/host` and `code/md` on `sys.path`.

## 7. Limitations and notes for other roles

- The tools do not simulate. Example behaviour is checked only by `tests/funcsim.py`, which is not the reference model.
- Not done: SPI-controller and I2C examples, and a check for pointer hazards (`P0.D` read before RDY).
- SPEC and machine.py observations:
  - `ENG_REGS` comments name `STAT` bit 5 "OVERRUN" where SPEC says OVR.
  - SPEC 9 gives no program-word byte order.
  - A reset out cell is bound to engine 0, not unbound.
  - Engine `E.SYM` staging persists when a burst writes nothing, and the examples rely on this.
