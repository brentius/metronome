"""Autobaud, plan A (v4, BOTS/PLANS/V4_PLAN.md Phase 0): the chip measures *and* retunes itself; the host does nothing.

Needs the v4 machine additions (SPEC v2 13, cycle model only so far): `CW.*` move destinations that write host-map
configuration from a program. With them, plan B's host step (compute the divider, rewrite line 0) becomes firmware.

**Normal form.** The receiver is compiled so that only two configuration fields depend on the rate:

* `INC = 8`, `PRE = 3 * INC = 24` (the start latency of a started line, rx.py) are rate independent;
* unused taps are 0xFFFF (never reached), not `MOD`;
* `MOD = S` and the sample tap `T = S >> 1`, where S is the length of 8 bit times in chip cycles. Then a beat is
  `MOD / INC = S / 8` cycles, one bit, and the sample sits at 50 %.

The nominal image carries `S` for the nominal rate, so it also works unretuned. The firmware rewrites four bytes.

**Measurement.** Edge capture into S0 (SPEC v2 12.4) is started by the init thread (a CW write of `EMASK` and `ECTL`),
into the receive stream's own buffer. A LIN header gives records: 0 break fall, 1 break end, 2 sync start fall,
3..10 the eight sync bit edges (0x55: every bit boundary is an edge), so records 3..10 hold one bit time each and
their sum is the start fall to the bit-7 fall: 8 bit times, fall to fall (rise/fall asymmetry cancels). `MARK = 44`
(11 records) tells the polling thread that record 10 is in.

**Arithmetic on the 8-bit machine.** A record is `{DC[18:0], PIN[12:0]}`; bytes 1..3 with byte 1 masked to bits 7:5
are `DC << 5` as a 24-bit number. Eight of them are summed with 8-bit adds and carry chains (`Z = 32 S`). LFSR 1
with polynomial 0 is a 32-bit right shifter (`step` = `S >> 1`): five steps give S, one more `S >> 1`, one more
`S >> 2`.

**Validation.** The break (record 1) must be at least 12 bit times (`B >= 1.5 S`, compared as `B >> 1 >= S/2 + S/4`
in 16 bits; LIN requires 13, a data byte has at most 9 low bits), and S must fit 16 bits (>= about 7.3 kbaud).
Otherwise the capture restarts and the thread waits for the next header.

**Apply.** CW writes `MOD` and the tap (4 bytes, one write every 2 cycles), turns capture off (`ECTL = 0`), rewinds
S0 (now the receive stream again), arms line 0 and stops itself. It must finish within the 2 bit times between the
bit-7 fall and the first data start bit (calculated; measured on the model in the tests).

The burst rule (every control-flow cycle passes a pause, SPEC v2 10) holds: the thread is triggered `ALWAYS` and
every wait pauses, so it polls and is re-dispatched every few cycles.

Resources: core 1, thread 2 (`ALWAYS`), CNT1, CNT2, R0..R3, ACC, P0, LF1, CW. Refused (E-UNSUPPORTED) when
the receiver needs LF1 (constant signature) or a sample point other than 50 %.
"""
from __future__ import annotations

from fractions import Fraction

from .plan import CompileError

FCLK = 60_000_000
INC = 8
MARK = 44                      # 11 records of 4 bytes
SHIFT = 5                      # bytes 1..3 of a record are DC << 5
DBG = 0x2460
EMASK_ADDR, ECTL_ADDR = DBG + 0x08, DBG + 0x02
LINE0 = 0x2000


def normal_form(x, period: Fraction):
    """(inc, mod, taps text, preset) of line 0 for plan A at the nominal beat period (chip cycles per bit)."""
    mod = round(8 * period)
    if mod > 0xFFFF:
        raise CompileError("E-FIT-TAP", f"autobaud plan A: 8 bit times ({mod} cycles) do not fit MOD (16 bits); "
                                        "nominal rate below about 7.3 kbaud")
    ts = ["65535"] * 3
    sample = [t for t in x.taps if t.frac is not None]
    if len(sample) != 1 or sample[0].frac != Fraction(1, 2) or len(x.taps) != 1:
        raise CompileError("E-UNSUPPORTED", "autobaud plan A: only a single sample tap at 50 % is retuned on chip")
    tap = sample[0]
    ts[tap.idx] = str(mod >> 1)
    x.opts["autobaud"]["tap_idx"] = tap.idx
    return INC, mod, " ".join(ts), 3 * INC


def add_onchip(x, rx_pin: int, rx_base: int):
    if x.opts.get("has_const"):
        raise CompileError("E-UNSUPPORTED", "autobaud plan A needs LFSR 1, which this receiver uses")
    tap_addr = LINE0 + 0x04 + 2 * x.opts["autobaud"]["tap_idx"]
    x.b.block(".line 2", ["inc 1", "mod 2", "taps - - -", f"pins A=P{rx_pin}"])
    mask = 1 << rx_pin
    # init (core 0, one move per instruction): EMASK, then ECTL = CEN; CW.D needs one other instruction in between
    x.init_moves += [f"#{EMASK_ADDR & 0xFF} -> CW.AL", f"#{EMASK_ADDR >> 8} -> CW.AH",
                     (f"#{mask & 0xFF} -> CW.D" if mask & 0xFF else "ZERO -> CW.D"), "ZERO -> NULL",
                     (f"#{mask >> 8} -> CW.D" if mask >> 8 else "ZERO -> CW.D"),
                     f"#{ECTL_ADDR & 0xFF} -> CW.AL", "#1 -> CW.D"]
    r1 = rx_base + 4 * 1 + 1          # record 1 (break end), byte 1
    r3 = rx_base + 4 * 3 + 1          # record 3 (first sync bit), byte 1
    k = x.b.cores[1]
    i = k.i
    k.label("ab")
    i([], goto="ab_go", jmode="if", jcond="S0.MARK", note="autobaud A: 11 edge records captured? (else wait)")
    i([], goto="ab", pause=True)
    k.label("ab_go")
    i(["ZERO -> R0", "ZERO -> R1", "ZERO -> R2"], note="Z = sum of DC << 5 over records 3..10 (24 bits)")
    i([f"#{r3 & 0xFF} -> P0.AL"])
    i([f"#{r3 >> 8} -> P0.AH"], note="prefetch record 3, byte 1")
    i(["#8 -> CNT1.LO"])
    i(["ZERO -> CNT1.HI"])
    k.label("ab_b1")
    i([], goto="ab_b1", jmode="ifnot", jcond="P0.RDY", pause=True)
    i(["P0.D -> ACC.LD", "ZERO -> P0.R"], note="byte 1: DC[2:0] in bits 7:5")
    i(["#224 -> ACC.AND"])
    i(["R0 -> ACC.ADD"])
    i(["ACC -> R0", "R1 -> ACC.LD"], goto="ab_b2", jmode="ifnot", jcond="ACC.C")
    i(["#1 -> ACC.ADD"], note="carry into Z byte 1")
    i(["ACC -> R1", "R2 -> ACC.LD"], goto="ab_b2", jmode="ifnot", jcond="ACC.C")
    i(["#1 -> ACC.ADD"])
    i(["ACC -> R2"])
    k.label("ab_b2")
    i([], goto="ab_b2", jmode="ifnot", jcond="P0.RDY", pause=True)
    i(["P0.D -> ACC.LD", "ZERO -> P0.R"], note="byte 2: DC[10:3]")
    i(["R1 -> ACC.ADD"])
    i(["ACC -> R1", "R2 -> ACC.LD"], goto="ab_b3", jmode="ifnot", jcond="ACC.C")
    i(["#1 -> ACC.ADD"])
    i(["ACC -> R2"])
    k.label("ab_b3")
    i([], goto="ab_b3", jmode="ifnot", jcond="P0.RDY", pause=True)
    i(["P0.D -> ACC.LD", "ZERO -> P0.R"], note="byte 3: DC[18:11]")
    i(["R2 -> ACC.ADD"])
    i(["ACC -> R2", "ZERO -> CNT1.DEC"])
    k.label("ab_sk")
    i([], goto="ab_sk", jmode="ifnot", jcond="P0.RDY", pause=True)
    i(["ZERO -> P0.R"], goto="ab_b1", jmode="ifnot", jcond="CNT1.Z", note="skip byte 0 of the next record")
    # S = Z >> 5 through LFSR 1 (polynomial 0: a step is a right shift)
    i(["R0 -> LF1.B0"], note="LFSR 1 as a right shifter: S = Z >> 5")
    i(["R1 -> LF1.B1"])
    i(["R2 -> LF1.B2"])
    i(["ZERO -> LF1.B3"])
    for _ in range(SHIFT):
        i(["ZERO -> LF1.ST"])
    i(["LF1.B2 -> ACC.LD"], note="S must fit 16 bits")
    i(["LF1.B0 -> R0", "LF1.B1 -> R1", "ZERO -> LF1.ST"], goto="ab_bad", jmode="ifnot", jcond="ACC.Z",
      note="R1:R0 = S = MOD")
    i(["LF1.B0 -> R2", "LF1.B1 -> R3", "ZERO -> LF1.ST"], note="R3:R2 = S >> 1 = the 50 % tap")
    # Y = S/2 + S/4 (< 49152) into CNT2 as storage
    i(["LF1.B0 -> ACC.LD"], note="Y = S/2 + S/4, the break threshold / 2")
    i(["R2 -> ACC.ADD"])
    i(["ACC -> CNT2.LO", "LF1.B1 -> ACC.LD"], goto="ab_y", jmode="ifnot", jcond="ACC.C")
    i(["#1 -> ACC.ADD"])
    k.label("ab_y")
    i(["R3 -> ACC.ADD"])
    i(["ACC -> CNT2.HI"])
    # B = break length (record 1) >> 1, into LFSR 1
    i([f"#{r1 & 0xFF} -> P0.AL"], note="B = record 1 (break) DC >> 1")
    i([f"#{r1 >> 8} -> P0.AH"])
    k.label("ab_r1")
    i([], goto="ab_r1", jmode="ifnot", jcond="P0.RDY", pause=True)
    i(["P0.D -> ACC.LD", "ZERO -> P0.R"])
    i(["#224 -> ACC.AND"])
    i(["ACC -> LF1.B0"])
    k.label("ab_r2")
    i([], goto="ab_r2", jmode="ifnot", jcond="P0.RDY", pause=True)
    i(["P0.D -> LF1.B1", "ZERO -> P0.R"])
    k.label("ab_r3")
    i([], goto="ab_r3", jmode="ifnot", jcond="P0.RDY", pause=True)
    i(["P0.D -> LF1.B2"])
    i(["ZERO -> LF1.B3"])
    for _ in range(SHIFT + 1):
        i(["ZERO -> LF1.ST"])
    # B >= Y ?  (B up to 18 bits, Y 16 bits): compare high to low
    i(["LF1.B2 -> ACC.LD"], note="break >= 12 bit times?")
    i(["LF1.B1 -> ACC.LD"], goto="ab_ok", jmode="ifnot", jcond="ACC.Z")
    i(["CNT2.HI -> ACC.CMP"])
    i([], goto="ab_bad", jmode="ifnot", jcond="ACC.C")
    i(["LF1.B0 -> ACC.LD"], goto="ab_ok", jmode="ifnot", jcond="ACC.Z")
    i(["CNT2.LO -> ACC.CMP"])
    i([], goto="ab_bad", jmode="ifnot", jcond="ACC.C")
    # apply: MOD, the sample tap, capture off, rewind S0, arm line 0, stop
    k.label("ab_ok")
    i([f"#{(LINE0 + 2) & 0xFF} -> CW.AL"], note="retune line 0 (written while RUN = ARM = 0)")
    i([f"#{(LINE0 + 2) >> 8} -> CW.AH"])
    i(["R0 -> CW.D"], note="MOD")
    i([])
    i(["R1 -> CW.D"])
    i([f"#{tap_addr & 0xFF} -> CW.AL"])
    i(["R2 -> CW.D"], note="sample tap")
    i([])
    i(["R3 -> CW.D"])
    i([f"#{ECTL_ADDR & 0xFF} -> CW.AL"])
    i([f"#{ECTL_ADDR >> 8} -> CW.AH"])
    i(["ZERO -> CW.D"], note="ECTL = 0: capture off, S0 is the receive stream again")
    i([])
    i(["#1 -> S0.CTL"], note="rewind S0 (after capture is off)")
    i(["#2 -> L0.CTL", "ZERO -> T.STOP"], pause=True, note="arm the receiver (config visible by now); done")
    k.label("ab_bad")
    i([f"#{ECTL_ADDR & 0xFF} -> CW.AL"], note="not a LIN header: restart the capture, wait for the next one")
    i([f"#{ECTL_ADDR >> 8} -> CW.AH"])
    i(["#1 -> CW.D"])
    i([])
    i(["#1 -> S0.CTL"])
    i([], goto="ab", pause=True)
    x.host["autobaud"] = {"plan": "A", "records": 11, "inc": INC, "fields_retuned": ["MOD", "sample tap"],
                          "host_involvement": "none after load", "capture_base": rx_base}
    x.notes.append("autobaud plan A: the chip measures the LIN sync field and retunes line 0 itself (v4 CW writes)")
    return [(2, 1, 2, "ALWAYS", "ab")]
