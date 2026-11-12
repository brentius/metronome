# Toolchain v2 (assembler, static timing check, images)

Code: `code/host2/metronome2_tools/`. Tests: `python -m pytest code/host2 -q` (67 pass; run it separately from `code/host`, whose test files share names). Examples: `code/host2/examples/`.
All names and numbers come from `code/md2/machine.py` (loaded as `md2_machine`, the module the v2 model uses); the tools hard-code no encoding. The only layout knowledge outside it is the bit packing of single-byte config registers (`EDGE`, `T0EDGE`, `HOLD`, thread `CFG`, stream `MODE`, out `BIND`/`SEL`), taken from the register descriptions in `machine.py`; `tests/test_asm.py` checks it against the model's decode. Normative spec: [SPEC_V2.md](SPEC_V2.md) part B.

Commands (from `code/host2`):

- `python -m metronome2_tools.asm prog.mas -o prog.json [-l] [-v] [--no-check]` assembles, runs the check, writes the image. A check error exits 2 and writes no image.
- `python -m metronome2_tools.check prog.mas` prints the full report. `python -m metronome2_tools.disasm prog.json` prints re-assemblable source.

## 1. Source syntax

v1 syntax (TOOLCHAIN.md section 1) with v2 ports. Comments start with `;`. Names are case-insensitive; labels and `.equ` names are case-sensitive. `.core N`, `.org A`, `.equ NAME expr`, labels as in v1.

```
[when COND] [guard] src -> dst {, [guard] src -> dst} [goto L [if|ifnot [JCOND]]] [pause]
```

- `COND` (any guard, 6-bit) only guards moves: `? move` runs if COND, `! move` if not.
- The **jump condition** is separate (SPEC v2 5, 7). `goto L if JCOND` / `goto L ifnot JCOND` takes one of the 32 `JUMP_GUARDS`. Bare `goto L if` reuses the `when` condition, which must then be a jump guard. Per-pin levels, flags 8..15, shifter out bits and line RUN are move guards only; the assembler rejects them after `goto` and says what is accepted. One instruction may therefore guard moves on `PIN7` and jump on `CNT1.Z`.
- The 8-bit `imm` field is shared by the jump target and every non-zero immediate. Same-group moves in one instruction are an error unless guarded `?` and `!` (groups from `machine.WRITE_GROUPS`; the three symbol ports are one group).
- `nop`, `pause`, `pause goto L` as in v1. A taken jump on a non-pausing instruction costs an idle cycle; `pause goto` does not (SPEC v2 5).

## 2. Configuration directives

Block directives end with `.end`; each line is `key value...`. Unset blocks are not written and keep their reset value (0).

```
.line N                                  ; 0..3
    rate|baud HZ | period CYC | inc E / mod E     ; INC < MOD, both <= 65535 (INC, MOD usable in later expressions)
    taps T0 T1 T2                        ; '-' disables (written as MOD)
    preset E  phase E  window LO HI      ; window sets WEN
    edge PIN none|rise|fall|both         ; re-alignment edge (default rise)
    follow                               ; FOLLOW = 1 (SPEC 3.3)
    t0edge PIN rise|fall|both            ; tap 0 sourced from this edge (T0SRC = 1)
    snap tap0|tap1|tap2|beat
    pins A=P3 B=uio[2] | pina X | pinb X
    in0 EXPR / in1 EXPR                  ; truth tables over a0 a1 a2 b1 rem (index {REM,B1,A2,A1,A0}); lut0/lut1 raw
    hold PIN low|high tapK               ; HEN = 1, HPIN, HLVL, HTAP (SPEC 3.2a)
    ctl run arm ren                      ; initial CTL (written last)
    minperiod N / minhalf N              ; declared assumptions about a followed clock, used by the check only
.end
.thread N                                ; 0..5
    core C  line L  trigger NAME         ; line defaults to the line of an Lg.* trigger, else 0
    watch0 COND -> LABEL                 ; watch1 likewise (any guard; TRUE is rejected)
    start LABEL | pc E    enable | disable
.end
.out O8                                  ; O0..O13, uio[i], uo[i]
    line N | none                        ; none: BOUND = 0, the pin shows LUT[0]
    sel B0 B1 B2                         ; symbol bit numbers (0..3) read as table inputs (default 0 1 2)
    lut EXPR   oe EXPR|always|never      ; over b0 b1 b2 seg (index {SEG[1:0], b2, b1, b0}); lutraw/oeraw; segN: v0..v7
.end
.stream N                                ; 0..1
    mode tx|rx   order msb|lsb   start A   len N   mark N
.end
.lfsr N poly=P [width=W] [init=I] [reflected] | raw=REG [init=I]    ; as v1; defines LFn_POLY, LFn_INIT, LFn_INIT_B0..B3
.data ADDR byte|"text" ...   .irqen outv error   .run on|off   .clock 60e6
.budget thread N cycles|insns V
```

`.line` defines `Ln_INC`, `Ln_MOD`, `Ln_PERIOD`.

## 3. Image and host link (`image.py`)

`host_writes(prog)` is the ordered `(address, bytes, note)` list; `build_image` wraps it in JSON (`machine_version` 2, `writes`, informational `program`, `labels`). Order: program memory (RUN_global is 0), data RAM, LFSR POLY, stream config, output pins, line config (without CTL and PHASE), thread config (watchers, then CFG), thread PC and EN, stream rewind (MODE/START apply at a rewind), line PHASE, line CTL (starts the lines), IRQEN, `CTRL.RUN` last. Program words are written as little-endian bytes of word w of core c at `c*0x800 + 8w` (SPEC v2 9; the byte order of the staging word is still not stated there, as in v1).

**D24.** The image is a list of byte writes carried by SPI frames. At the SPEC limit of SCK = clk/16, a byte takes at least 128 cycles, so no two host writes (and no two configuration writes) are in consecutive cycles; the image uses no other path. `min_write_gap_cycles(divider)` gives the spacing, and `tests/test_examples.py` loads a whole image over the cycle-accurate model link and checks every cycle (minimum gap measured: 128). Hold the link idle for a few cycles after reset: a configuration write in the two cycles after `rst_q` rises is ignored.

`spi_streams`, `spi_write_frame`, `spi_read_frame` are as v1.

## 4. Static check (`check.py`, SPEC v2 10.4)

All counts in cycles. Burst length = instructions executed + 1 for each taken jump on a non-pausing instruction; a burst entry is a thread's start, its watcher handlers and every resume point after a reachable `pause`. Conditions are not correlated, so infeasible paths count (conservative). A trigger in cycle t executes burst-cycle i in `t + i + 2`; with others on the core, `Sigma = sum (L_p + 1)` over the other enabled threads bound to the same core, `L_p` their longest burst, each counted once (SPEC v2 5).

Errors:

1. **Burst rule.** Every control-flow cycle must pass through a pause; an instruction that continues into unprogrammed memory is an error.
2. **Commit deadline.** For a thread triggered by `Lg.BEAT` / `Lg.TAPk` on its own line: last symbol write at burst-cycle s needs `s + 2 + Sigma <= gap(trigger, next boundary)` (else the write is LATE).
3. **Snapshot.** Last input read (sources `L.IN`, `L.CAP`; guards `L.IN0`, `L.IN1` as move or jump condition) at burst-cycle r needs `r + 2 + Sigma < gap(trigger, next snapshot)`, snapshot event from `SNAP`. Strict, following the text "before the next snapshot cycle".
4. **Overrun.** `n + 2 + Sigma + 1 <= gap(trigger, trigger)`, else the next trigger sets OVR (the same rule as v1's spacing check).
5. **INC < MOD**, 1 <= INC, MOD <= 65535, on every configured line.
6. **Window and taps.** A line that re-aligns (edge polarity set, `FOLLOW = 0`, REN used: initial `ctl ren`, or a move to `Lk.CTL` with an immediate that has bit 2 set or a source the tools cannot evaluate) and has `WEN = 1` needs `WLO <= WHI`, and every enabled phase tap used for capture, snapshot or a trigger needs `T < WLO and T <= PRE`, or `T > WHI + INC and T > PRE`. A tap is "used" if it is the snapshot tap, a thread triggers on it, or the line has a pin select below 13 and a non-zero input table.
7. **Hold.** `HPIN >= 13` with `HLVL = 1` (would hold forever). Warning: level 0 on such a pin, or a hold tap that is disabled or edge-sourced.
8. `.budget thread N cycles|insns V`.

`gap(e, s)` (`timing.py`) is a lower bound on cycles from an event to the next occurrence of another. Free-running generated line: exact, simulated from the SPEC 3.4 tap and fired-bit rules over one phase period from each possible start phase (`PRE`, `phase`, 0); a hold only lengthens, so it stays valid. Re-aligning line: the minimum of that and the time after an accepted edge loads `PRE` (approximate: ignores the window). Follower line: from the declared `minperiod` and `minhalf` (assumptions the author states; without them the deadline checks are skipped with a warning). Edge-sourced tap 0 on a free-running line, and triggers by a different line than the thread's own, are reported as not statically checkable.

Warnings: non-ascending taps, a tap skipped in free running (TAPMISS), `FOLLOW` without an edge, a follower with triggered threads and no `minperiod`, a re-aligning line with `WEN = 0`, a write group shared by threads, triggers that are not line events on threads that write symbols.

## 5. Evidence and limits

- Model, not silicon: `tests/test_examples.py` runs UART TX (115200 baud, O8), Ethernet-rate Manchester TX (10 Mbit/s, 6 cycles per cell, O0) and an SPI mode-1 target on a follower line (three clock rates, MOSI into a receive stream, MISO from a transmit stream) on `sim/reference/metronome2` and checks pin traces; the model and the tools share an author and a spec. The check's response arithmetic is compared with the model's execution trace for two threads on one core (bound met exactly).
- Not checked: pointer hazards (`P0.D` before `RDY`), stream starvation, cross-line trigger deadlines, `Lk.CTL` immediates computed at run time (assumed to set REN), data-dependent loops that terminate through a pause only.
- Spec observations (see the delivery report): the first boundary of a follower line with an edge-sourced tap 0 used to set TAPMISS (fixed by D28: the starting beat is exempt); "before the next snapshot cycle" is read strictly; "REN used" and "used for capture" are not defined statically; mode-0 SPI targets could not present the first bit before the first edge (fixed by D28: a line start commits the staged symbol).
