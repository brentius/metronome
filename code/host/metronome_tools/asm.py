"""Metronome assembler.  python -m metronome_tools.asm prog.mas -o prog.json   (syntax: wiki/TOOLCHAIN.md)"""
from __future__ import annotations

import argparse
import difflib
import re
import sys
from fractions import Fraction
from pathlib import Path

from ._md import M, Insn, Move
from .expr import ExprError, evaluate, evaluate_int
from .model import AsmError, AsmInsn, BeatGen, Engine, Lfsr, OutCell, Program

IDENT = r"[A-Za-z_][A-Za-z_0-9]*"
POLARITY = {"none": 0, "rise": 1, "fall": 2, "both": 3}
CTL_BITS = {"run": 1, "arm": 2, "ren": 4, "wen": 8}
BG_KEYS = ["rate", "baud", "period", "inc", "mod", "taps", "preset", "phase", "window", "edge", "ctl"]
ENG_KEYS = ["core", "beatgen", "trigger", "pins", "pina", "pinb", "in0", "in1", "lut0", "lut1", "watch0", "watch1",
            "start", "pc", "enable", "disable"]


# --------------------------------------------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------------------------------------------

def strip_comment(line: str) -> str:
    out, q = [], False
    i = 0
    while i < len(line):
        c = line[i]
        if c == '"':
            q = not q
        elif not q and c == ";":
            break
        out.append(c)
        i += 1
    return "".join(out).strip()


def split_top(s: str, sep: str = ",") -> list[str]:
    parts, depth, cur = [], 0, []
    for c in s:
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        if c == sep and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(c)
    parts.append("".join(cur))
    return [p.strip() for p in parts if p.strip()]


def suggest(name: str, choices) -> str:
    near = difflib.get_close_matches(name, list(choices), n=3, cutoff=0.6)
    return f" (did you mean {', '.join(near)}?)" if near else ""


def write_group(dst: str) -> str | None:
    """The write group of a destination port (SPEC 6): enabled moves to one group in one cycle conflict."""
    if dst == "NULL":
        return None
    if dst.startswith("ACC."):
        return "ACC"
    m = re.fullmatch(r"(SH\d)\.(LD|SH)", dst)
    if m:
        return m.group(1) + ".LD/SH"
    m = re.fullmatch(r"(CNT\d|LF\d|P\d)\.\w+", dst)
    if m:
        return m.group(1)
    if dst.startswith("FLAGS."):
        return "FLAGS"
    return dst


def _norm_pin(t: str) -> str:
    t = t.strip().lower().replace(" ", "")
    for a, b in (("uio_in", "uio"), ("uio_out", "uio"), ("ui_in", "ui"), ("uo_out", "uo")):
        t = t.replace(a, b)
    return t


def parse_in_pin(tok: str, env: dict) -> int:
    t = tok.strip()
    if t.lower() in ("none", "off", "-"):
        return 15
    m = re.fullmatch(r"[Pp](\d+)", t)
    n = int(m.group(1)) if m else None
    if n is None and _norm_pin(t) in M.IN_PINS:
        n = M.IN_PINS.index(_norm_pin(t))
    if n is None:
        n = evaluate_int(t, env)
    if not 0 <= n < M.N_IN_PINS:
        raise AsmError(f"input pin {tok!r} out of range 0..{M.N_IN_PINS - 1} (use 'none' for the constant-0 select)")
    return n


def parse_out_pin(tok: str, env: dict) -> int:
    t = tok.strip()
    m = re.fullmatch(r"[Oo](\d+)", t)
    n = int(m.group(1)) if m else None
    if n is None and _norm_pin(t) in M.OUT_PINS:
        n = M.OUT_PINS.index(_norm_pin(t))
    if n is None:
        n = evaluate_int(t, env)
    if not 0 <= n < M.N_OUT_PINS:
        raise AsmError(f"output pin {tok!r} out of range 0..{M.N_OUT_PINS - 1}")
    return n


def rev_bits(v: int, w: int) -> int:
    return int(format(v & ((1 << w) - 1), f"0{w}b")[::-1], 2)


def _wrap(ex: Exception, line: int, file: str) -> AsmError:
    if isinstance(ex, AsmError):
        return AsmError(ex.msg, ex.line or line, ex.file or file)
    return AsmError(str(ex), line, file)


# --------------------------------------------------------------------------------------------------------------
# instruction parsing
# --------------------------------------------------------------------------------------------------------------
_GOTO = re.compile(r"\bgoto\s+(\S+)(?:\s+(ifnot|if)\b(?:\s+([A-Za-z0-9_.]+))?)?")
_WHEN = re.compile(r"^\s*when\s+([A-Za-z0-9_.]+)\s*")
_PAUSE = re.compile(r"(?<![\w.])pause(?![\w.])")


def parse_insn(text: str, env: dict, labels: dict, core: int, line: int) -> Insn:
    s = text.strip()
    cond = "TRUE"
    m = _WHEN.match(s)
    if m:
        cond = m.group(1).upper()
        s = s[m.end():]
    pause = bool(_PAUSE.search(s))
    s = _PAUSE.sub(" ", s)
    if re.fullmatch(r"\s*nop\s*", s):
        s = ""
    goto = _GOTO.search(s)
    target = jkind = None
    if goto:
        tname, jkind, jcond = goto.group(1), goto.group(2), goto.group(3)
        s = s[:goto.start()] + s[goto.end():]
        if tname in labels:
            tcore, target = labels[tname]
            if tcore != core:
                raise AsmError(f"goto {tname}: label is in core {tcore} but this instruction is in core {core}", line)
        else:
            try:
                target = evaluate_int(tname, env)
            except ExprError:
                raise AsmError(f"unknown label {tname!r}{suggest(tname, labels)}", line) from None
        if not 0 <= target < M.PROG_WORDS:
            raise AsmError(f"goto target {target} outside 0..{M.PROG_WORDS - 1}", line)
        if jcond:
            if cond != "TRUE" and cond != jcond.upper():
                raise AsmError(f"conflicting conditions: when {cond} and goto ... {jkind} {jcond.upper()}", line)
            cond = jcond.upper()
    if cond not in M.GUARD_ID:
        raise AsmError(f"unknown condition {cond!r}{suggest(cond, M.GUARD_ID)}", line)

    moves, imms, needs_cond = [], [], False
    for part in split_top(s):
        guard = "always"
        mg = re.match(r"^(\?|!|never\b)\s*", part)
        if mg:
            guard = {"?": "if", "!": "ifnot", "never": "never"}[mg.group(1)]
            part = part[mg.end():]
        if "->" not in part:
            raise AsmError(f"expected 'src -> dst', got {part!r}", line)
        src_t, dst_t = (x.strip() for x in part.split("->", 1))
        dst = dst_t.upper()
        if dst not in M.DST_ID:
            raise AsmError(f"unknown destination port {dst_t!r}{suggest(dst, M.DST_ID)}", line)
        if src_t.startswith("#"):
            try:
                v = evaluate_int(src_t[1:], env)
            except ExprError as e:
                raise AsmError(str(e), line) from None
            if not -128 <= v <= 255:
                raise AsmError(f"immediate {v} does not fit the 8-bit imm field", line)
            v &= 0xFF
            if v == 0:
                src = "ZERO"          # a zero needs no imm field
            else:
                src = "IMM"
                imms.append(v)
        else:
            src = src_t.upper()
            if src not in M.SRC_ID:
                raise AsmError(f"unknown source port {src_t!r}{suggest(src, M.SRC_ID)}", line)
        if guard in ("if", "ifnot"):
            needs_cond = True
        moves.append(Move(src, dst, guard))
    if len(moves) > M.N_MOVES:
        raise AsmError(f"{len(moves)} moves in one instruction; at most {M.N_MOVES}", line)

    if jkind:
        needs_cond = True
    if needs_cond and cond == "TRUE":
        raise AsmError("a conditional move guard or 'goto ... if/ifnot' needs a condition: add 'when COND' "
                       "(or 'goto L if COND')", line)
    vals = sorted(set(imms) | ({target} if target is not None else set()))
    if len(vals) > 1:
        what = []
        if imms:
            what.append("immediates " + ", ".join(f"#{v}" for v in sorted(set(imms))))
        if target is not None:
            what.append(f"jump target {target}")
        raise AsmError("the 8-bit imm field is shared by the jump target and immediates: this instruction needs "
                       f"{' and '.join(what)}; split it into two instructions", line)
    jmode = "next" if target is None else {None: "always", "if": "if", "ifnot": "ifnot"}[jkind]
    insn = Insn(tuple(moves), cond, jmode, vals[0] if vals else 0, pause)
    for i, a in enumerate(moves):                      # write-group conflicts inside one instruction (SPEC 6)
        for b in moves[i + 1:]:
            ga, gb = write_group(a.dst), write_group(b.dst)
            if ga is None or ga != gb or "never" in (a.guard, b.guard):
                continue
            if {a.guard, b.guard} == {"if", "ifnot"}:
                continue
            raise AsmError(f"moves to {a.dst} and {b.dst} write the same group ({ga}) in one cycle and are not "
                           f"exclusive (use '?' / '!' guards); the hardware would set CONFLICT", line)
    return insn


# --------------------------------------------------------------------------------------------------------------
# the assembler proper
# --------------------------------------------------------------------------------------------------------------
class Assembler:
    def __init__(self, text: str, name: str = "<src>"):
        self.name = name
        self.prog = Program(source_name=name)
        self.env: dict = {}
        self.items: list = []        # ordered configuration items
        self.raw_insns: list = []    # (core, addr, text, line)
        self.equs: list = []
        self._parse(text)

    def _err(self, msg, line):
        return AsmError(msg, line, self.name)

    # -- pass 1: split into labels, instructions, directives ----------------------------------------------
    def _parse(self, text: str) -> None:
        core, pc = 0, [0] * M.N_CORES
        used = {c: set() for c in range(M.N_CORES)}
        block = None
        pending: list = []
        label_re = re.compile(rf"^({IDENT})\s*:(?!\w)\s*(.*)$")
        for no, raw in enumerate(text.splitlines(), 1):
            line = strip_comment(raw)
            if not line:
                continue
            try:
                if block is not None:
                    if line.lower() == ".end":
                        self.items.append(block)
                        block = None
                    else:
                        block["lines"].append((no, line))
                    continue
                m = label_re.match(line) if not line.startswith(".") else None
                while m:
                    lbl = m.group(1)
                    if lbl in self.prog.labels or any(lbl == p for p in pending):
                        raise AsmError(f"duplicate label {lbl!r}")
                    pending.append(lbl)
                    line = m.group(2).strip()
                    m = label_re.match(line)
                if not line:
                    continue
                if line.startswith("."):
                    kw, _, rest = line.partition(" ")
                    kw, rest = kw.lower(), rest.strip()
                    if kw == ".core":
                        core = evaluate_int(rest, {})
                        if not 0 <= core < M.N_CORES:
                            raise AsmError(f".core must be 0..{M.N_CORES - 1}")
                    elif kw == ".org":
                        pc[core] = evaluate_int(rest, {})
                        if not 0 <= pc[core] < M.PROG_WORDS:
                            raise AsmError(f".org outside 0..{M.PROG_WORDS - 1}")
                    elif kw == ".equ":
                        mm = re.match(rf"^({IDENT})\s*,?\s*(.+)$", rest)
                        if not mm:
                            raise AsmError(".equ NAME value")
                        self.equs.append((mm.group(1), mm.group(2), no))
                    elif kw in (".beatgen", ".engine", ".out"):
                        block = {"kind": kw[1:], "arg": rest, "lines": [], "line": no}
                    elif kw in (".lfsr", ".data", ".irqen", ".run", ".clock", ".budget"):
                        self.items.append({"kind": kw[1:], "arg": rest, "lines": [], "line": no})
                    else:
                        raise AsmError(f"unknown directive {kw}")
                    continue
                if pc[core] >= M.PROG_WORDS:
                    raise AsmError(f"core {core} program memory is full ({M.PROG_WORDS} words)")
                if pc[core] in used[core]:
                    raise AsmError(f"address 0x{pc[core]:02X} of core {core} is already occupied (.org overlap)")
                for lbl in pending:
                    self.prog.labels[lbl] = (core, pc[core])
                pending = []
                used[core].add(pc[core])
                self.raw_insns.append((core, pc[core], line, no))
                pc[core] += 1
            except (AsmError, ExprError) as e:
                raise _wrap(e, no, self.name) from None
        if block is not None:
            raise self._err(f".{block['kind']} block is missing .end", block["line"])
        for lbl in pending:                  # labels at the very end of a section
            self.prog.labels[lbl] = (core, pc[core])

    # -- pass 2: resolve values, process configuration, encode --------------------------------------------
    def assemble(self) -> Program:
        p, env = self.prog, self.env
        for name, (_, a) in p.labels.items():
            env[name] = a
        for name, expr, no in self.equs:
            try:
                v = evaluate(expr, env)
            except ExprError as e:
                raise self._err(str(e), no) from None
            env[name] = int(v) if isinstance(v, float) and v == int(v) and abs(v) < 2**53 else v
        p.symbols = env
        for it in self.items:
            try:
                getattr(self, "_do_" + it["kind"])(it)
            except (AsmError, ExprError) as e:
                raise _wrap(e, it["line"], self.name) from None
        for core, addr, text, no in self.raw_insns:
            try:
                insn = parse_insn(text, env, p.labels, core, no)
            except (AsmError, ExprError) as e:
                raise _wrap(e, no, self.name) from None
            p.code[core][addr] = AsmInsn(core, addr, insn, no, text)
        self._resolve_engines()
        return p

    def _label(self, name: str, core: int, line: int) -> int:
        if name not in self.prog.labels:
            raise self._err(f"unknown label {name!r}{suggest(name, self.prog.labels)}", line)
        c, a = self.prog.labels[name]
        if c != core:
            raise self._err(f"label {name!r} is in core {c} but the engine runs on core {core}", line)
        return a

    def _resolve_engines(self) -> None:
        for e in self.prog.engines.values():
            if e.start is not None:
                e.start_addr = self._label(e.start, e.core, e.line)
            elif e.pc is not None:
                e.start_addr = e.pc
            for k in (0, 1):
                if e.watch[k]:
                    e.watch_addr[k] = self._label(e.watch[k][1], e.core, e.line)

    # -- directives ----------------------------------------------------------------------------------------
    @staticmethod
    def _lines(it):
        for no, line in it["lines"]:
            key, _, rest = line.partition(" ")
            yield no, key.lower(), rest.strip()

    def _do_clock(self, it):
        self.prog.clock_hz = float(evaluate(it["arg"], self.env))

    def _do_run(self, it):
        a = it["arg"].lower() or "on"
        if a not in ("on", "off"):
            raise AsmError(".run on|off")
        self.prog.run = a == "on"

    def _do_irqen(self, it):
        bits = 0
        for w in it["arg"].replace(",", " ").split():
            if w.lower() in ("outv", "mailbox"):
                bits |= 1
            elif w.lower() in ("error", "errors", "sticky"):
                bits |= 2
            else:
                bits |= evaluate_int(w, self.env)
        self.prog.irqen = bits

    def _do_budget(self, it):
        m = re.fullmatch(r"engine\s+(\S+)\s+(cycles|insns)\s+(.+)", it["arg"], re.I)
        if not m:
            raise AsmError(".budget engine N cycles|insns VALUE")
        self.prog.budgets.append((evaluate_int(m.group(1), self.env), m.group(2).lower(),
                                  evaluate_int(m.group(3), self.env), it["line"]))

    def _do_data(self, it):
        toks = re.findall(r'"[^"]*"|[^\s,]+', it["arg"])
        if len(toks) < 2:
            raise AsmError('.data ADDR byte|"string" ...')
        addr = evaluate_int(toks[0].rstrip(":"), self.env)
        buf = bytearray()
        for t in toks[1:]:
            if t.startswith('"'):
                buf += t[1:-1].encode("ascii")
            else:
                v = evaluate_int(t, self.env)
                if not -128 <= v <= 255:
                    raise AsmError(f"data byte {v} out of range")
                buf.append(v & 0xFF)
        if addr < 0 or addr + len(buf) > M.DATA_BYTES:
            raise AsmError(f"data at {addr}+{len(buf)} exceeds the {M.DATA_BYTES}-byte data RAM")
        self.prog.data.append((addr, bytes(buf)))

    def _do_lfsr(self, it):
        toks = it["arg"].split()
        n = evaluate_int(toks[0], self.env)
        if not 0 <= n < M.N_LFSRS:
            raise AsmError(f"LFSR index must be 0..{M.N_LFSRS - 1}")
        kv = {}
        for t in toks[1:]:
            k, _, v = t.partition("=")
            kv[k.lower()] = v
        width = evaluate_int(kv.get("width", "32"), self.env)
        if not 1 <= width <= M.LFSR_WIDTH:
            raise AsmError(f"width must be 1..{M.LFSR_WIDTH}")
        if "raw" in kv:                       # register form: already LSB-first, used as written
            poly = evaluate_int(kv["raw"], self.env)
            init = evaluate_int(kv.get("init", "0"), self.env)
        elif "poly" in kv:
            poly = evaluate_int(kv["poly"], self.env)
            init = evaluate_int(kv.get("init", "0"), self.env)
            if "reflected" not in kv:         # MSB-first definition: bit-reverse within the width (SPEC 6.1)
                poly, init = rev_bits(poly, width), rev_bits(init, width)
        else:
            raise AsmError(".lfsr N poly=P [width=W] [init=I] [reflected]   |   .lfsr N raw=REG [init=I]")
        mask = (1 << M.LFSR_WIDTH) - 1
        poly, init = poly & mask, init & mask
        self.prog.lfsrs[n] = Lfsr(n, poly, width, init)
        self.env[f"LF{n}_POLY"] = poly
        self.env[f"LF{n}_INIT"] = init
        self.env[f"LF{n}_WIDTH"] = width
        for b in range(4):
            self.env[f"LF{n}_INIT_B{b}"] = (init >> (8 * b)) & 0xFF

    def _do_beatgen(self, it):
        n = evaluate_int(it["arg"], self.env)
        if not 0 <= n < M.N_BEATGENS:
            raise AsmError(f"beat generator must be 0..{M.N_BEATGENS - 1}")
        bg = BeatGen(n, line=it["line"])
        for no, key, rest in self._lines(it):
            try:
                env = dict(self.env, INC=bg.inc, MOD=bg.mod)
                self._bg_line(bg, key, rest, env)
            except (AsmError, ExprError) as e:
                raise _wrap(e, no, self.name) from None
        if not (bg.inc and bg.mod):
            raise AsmError(f"beatgen {n}: needs 'rate'/'baud', 'period' or 'inc' + 'mod'")
        if not 1 <= bg.inc < bg.mod <= 0xFFFF:
            raise AsmError(f"beatgen {n}: need 1 <= inc < mod <= 65535 (SPEC 9a.6) (inc={bg.inc}, mod={bg.mod})")
        for k, t in enumerate(bg.taps):
            if t is not None and not 0 <= t < bg.mod:
                raise AsmError(f"beatgen {n}: tap {k} = {t} must be below mod {bg.mod} (use '-' to disable)")
        live = [t for t in bg.taps if t is not None]
        if live != sorted(live) or bg.taps != [t for t in bg.taps if t is not None] + \
                [None] * bg.taps.count(None):
            raise AsmError(f"beatgen {n}: taps must satisfy T0 <= T1 <= T2 with disabled taps last (SPEC 3)")
        self.prog.bgs[n] = bg
        self.env[f"BG{n}_INC"] = bg.inc
        self.env[f"BG{n}_MOD"] = bg.mod
        self.env[f"BG{n}_PERIOD"] = bg.mod / bg.inc

    def _bg_line(self, bg: BeatGen, key: str, rest: str, env: dict) -> None:
        if key in ("rate", "baud"):
            rate = evaluate(rest, env)
            exact = (Fraction(rate) / Fraction(self.prog.clock_hz)).limit_denominator(10**12)
            frac = exact
            if frac.numerator > 0xFFFF or frac.denominator > 0xFFFF:
                frac = exact.limit_denominator(0xFFFF)
                ppm = abs(float(frac / exact) - 1) * 1e6
                self.prog.warnings.append(
                    f"beatgen {bg.n}: rate {rate} Hz at {self.prog.clock_hz / 1e6:g} MHz is not exact; using "
                    f"inc/mod = {frac.numerator}/{frac.denominator} ({ppm:.0f} ppm error, calculated)")
            if frac <= 0 or frac >= 1:
                raise AsmError(f"rate {rate} Hz is not within 0..clock ({self.prog.clock_hz:g} Hz)")
            bg.inc, bg.mod = frac.numerator, frac.denominator
        elif key == "period":
            bg.inc, bg.mod = 1, evaluate_int(rest, env)
        elif key == "inc":
            bg.inc = evaluate_int(rest, env)
        elif key == "mod":
            bg.mod = evaluate_int(rest, env)
        elif key == "taps":
            items = rest.replace(",", " ").split()
            if len(items) > 3:
                raise AsmError("at most three taps")
            bg.taps = [None, None, None]
            for k, t in enumerate(items):
                bg.taps[k] = None if t in ("-", "off") else evaluate_int(t, env)
        elif key == "preset":
            bg.pre = evaluate_int(rest, env)
        elif key == "phase":
            bg.phase = evaluate_int(rest, env)
        elif key == "window":
            lo, hi = rest.replace(",", " ").split()
            bg.wlo, bg.whi = evaluate_int(lo, env), evaluate_int(hi, env)
            bg.ctl |= CTL_BITS["wen"]
        elif key == "edge":
            toks = rest.split()
            bg.edge_pin = parse_in_pin(toks[0], env)
            pol = toks[1].lower() if len(toks) > 1 else "rise"
            bg.edge_pol = POLARITY[pol] if pol in POLARITY else evaluate_int(pol, env)
        elif key == "ctl":
            for w in rest.replace(",", " ").split():
                bg.ctl |= CTL_BITS[w.lower()] if w.lower() in CTL_BITS else evaluate_int(w, env)
        else:
            raise AsmError(f"unknown beatgen setting {key!r}{suggest(key, BG_KEYS)}")

    def _lut_from_expr(self, rest: str, names: list[str], widths: list[int]) -> int:
        lut = 0
        for idx in range(16):
            env = dict(self.env)
            sh = 0
            for nm, w in zip(names, widths):
                env[nm] = (idx >> sh) & ((1 << w) - 1)
                sh += w
            if evaluate_int(rest, env) & 1:
                lut |= 1 << idx
        return lut

    def _do_engine(self, it):
        n = evaluate_int(it["arg"], self.env)
        if not 0 <= n < M.N_ENGINES:
            raise AsmError(f"engine must be 0..{M.N_ENGINES - 1}")
        e = Engine(n, line=it["line"])
        for no, key, rest in self._lines(it):
            try:
                self._engine_line(e, key, rest)
            except (AsmError, ExprError) as ex:
                raise _wrap(ex, no, self.name) from None
        if e.trigger.startswith("BG") and e.bg is not None and int(e.trigger[2]) != e.bg:
            self.prog.warnings.append(
                f"engine {n}: trigger {e.trigger} but beatgen {e.bg}; the output commits on BG{e.bg}'s beats")
        self.prog.engines[n] = e

    def _engine_line(self, e: Engine, key: str, rest: str) -> None:
        env = self.env
        if key == "core":
            e.core = evaluate_int(rest, env)
            if not 0 <= e.core < M.N_CORES:
                raise AsmError(f"core must be 0..{M.N_CORES - 1}")
        elif key == "beatgen":
            e.bg = evaluate_int(rest, env)
            if not 0 <= e.bg < M.N_BEATGENS:
                raise AsmError(f"beatgen must be 0..{M.N_BEATGENS - 1}")
        elif key == "trigger":
            t = rest.upper()
            if t not in M.TRIG_ID:
                raise AsmError(f"unknown trigger {rest!r}{suggest(t, M.TRIG_ID)}; see wiki/ISA_TABLES.md")
            e.trigger = t
        elif key == "pins":
            for item in rest.replace(",", " ").split():
                k, _, v = item.partition("=")
                self._engine_line(e, "pin" + k.lower(), v)
        elif key == "pina":
            e.pina = parse_in_pin(rest, env)
        elif key == "pinb":
            e.pinb = parse_in_pin(rest, env)
        elif key == "in0":
            e.lut0 = self._lut_from_expr(rest, ["a0", "a1", "a2", "b1"], [1, 1, 1, 1])
        elif key == "in1":
            e.lut1 = self._lut_from_expr(rest, ["a0", "a1", "a2", "b1"], [1, 1, 1, 1])
        elif key == "lut0":
            e.lut0 = evaluate_int(rest, env) & 0xFFFF
        elif key == "lut1":
            e.lut1 = evaluate_int(rest, env) & 0xFFFF
        elif key in ("watch0", "watch1"):
            m = re.fullmatch(r"([A-Za-z0-9_.]+)\s*->\s*(\S+)", rest)
            if not m:
                raise AsmError(f"{key} COND -> handler_label")
            cond = m.group(1).upper()
            if cond not in M.GUARD_ID:
                raise AsmError(f"unknown condition {cond!r}{suggest(cond, M.GUARD_ID)}")
            if cond == "TRUE":
                raise AsmError("a watcher on TRUE would hijack every burst (guard 0 disables a watcher)")
            e.watch[int(key[-1])] = (cond, m.group(2))
        elif key == "start":
            e.start = rest
        elif key == "pc":
            e.pc = evaluate_int(rest, env)
        elif key in ("enable", "disable"):
            e.enable = key == "enable"
        else:
            raise AsmError(f"unknown engine setting {key!r}{suggest(key, ENG_KEYS)}")

    def _do_out(self, it):
        n = parse_out_pin(it["arg"], self.env)
        o = OutCell(n, line=it["line"])
        rows = {"lut": {}, "oe": {}}
        for no, key, rest in self._lines(it):
            try:
                if key == "engine":
                    if rest.lower() in ("none", "unbound"):
                        o.eng = 7
                    else:
                        o.eng = evaluate_int(rest, self.env)
                        if not 0 <= o.eng < M.N_ENGINES:
                            raise AsmError("engine out of range")
                elif key in ("lut", "oe"):
                    if key == "oe" and rest.lower() in ("always", "on"):
                        val = 0xFFFF
                    elif key == "oe" and rest.lower() in ("never", "off"):
                        val = 0
                    else:
                        val = self._lut_from_expr(rest, ["sym", "seg"], [2, 2])
                    setattr(o, key, val)
                elif key in ("lutraw", "oeraw"):
                    setattr(o, key[:-3], evaluate_int(rest, self.env) & 0xFFFF)
                elif key.startswith(("seg", "oeseg")):
                    m = re.fullmatch(r"(oe)?seg\s*(\d)\s*:\s*(.*)", (key + " " + rest).strip(), re.I)
                    if not m:
                        raise AsmError("segN: v0 v1 v2 v3   (levels for symbol 0..3)")
                    seg = int(m.group(2))
                    vals = [evaluate_int(x, self.env) for x in m.group(3).replace(",", " ").split()]
                    if seg > 3 or len(vals) != 4:
                        raise AsmError("segN: needs seg 0..3 and four values (symbols 0..3)")
                    rows["oe" if m.group(1) else "lut"][seg] = vals
                else:
                    raise AsmError(f"unknown out setting {key!r}")
            except (AsmError, ExprError) as ex:
                raise _wrap(ex, no, self.name) from None
        for attr, table in rows.items():
            if table:
                v = 0
                for seg, vals in table.items():
                    for sym, b in enumerate(vals):
                        if b & 1:
                            v |= 1 << (seg * 4 + sym)
                setattr(o, attr, v)
        if o.oe and n >= M.N_OE_PINS:
            self.prog.warnings.append(f"out O{n}: pin has no output-enable table; 'oe' ignored")
            o.oe = 0
        self.prog.outs[n] = o


def assemble_text(text: str, name: str = "<src>") -> Program:
    return Assembler(text, name).assemble()


def assemble_file(path: str | Path) -> Program:
    path = Path(path)
    return assemble_text(path.read_text(encoding="utf-8"), str(path))


def listing(prog: Program) -> str:
    out = []
    for core in range(M.N_CORES):
        if not prog.code[core]:
            continue
        out.append(f"core {core}:")
        inv: dict = {}
        for name, (c, a) in prog.labels.items():
            if c == core:
                inv.setdefault(a, []).append(name)
        for a, ai in sorted(prog.code[core].items()):
            lbl = ",".join(inv.get(a, []))
            out.append(f"  {a:02X}  {ai.word:016X}  {lbl + ':' if lbl else '':<12} {ai.text}")
    return "\n".join(out)


def main(argv=None) -> int:
    from . import check as chk
    from . import image as img
    ap = argparse.ArgumentParser(prog="metronome_tools.asm", description="Metronome assembler")
    ap.add_argument("source")
    ap.add_argument("-o", "--output", help="program image JSON to write")
    ap.add_argument("-l", "--listing", action="store_true", help="print an address/word/source listing")
    ap.add_argument("--no-check", action="store_true", help="skip the static checks (burst rule, timing budgets)")
    ap.add_argument("-v", "--verbose", action="store_true", help="print the full check report")
    a = ap.parse_args(argv)
    try:
        prog = assemble_file(a.source)
    except AsmError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    for w in prog.warnings:
        print(f"warning: {w}", file=sys.stderr)
    if a.listing:
        print(listing(prog))
    if not a.no_check:
        rep = chk.check(prog)
        print(rep.format(verbose=a.verbose), file=sys.stderr)
        if rep.errors:
            print(f"{len(rep.errors)} check error(s); image not written", file=sys.stderr)
            return 2
    if a.output:
        img.write_image(img.build_image(prog), a.output)
        print(f"wrote {a.output}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
