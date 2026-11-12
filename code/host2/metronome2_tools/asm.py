"""Metronome v2 assembler.  python -m metronome2_tools.asm prog.mas -o prog.json   (syntax: wiki/TOOLCHAIN_V2.md)"""
from __future__ import annotations

import argparse
import difflib
import re
import sys
from fractions import Fraction
from pathlib import Path

from ._md import M
from .encode import Insn, Move
from .expr import ExprError, evaluate, evaluate_int
from .model import (AsmError, AsmInsn, LineCfg, Lfsr, OutCfg, Program, StreamCfg, ThreadCfg)

IDENT = r"[A-Za-z_][A-Za-z_0-9]*"
POLARITY = {"none": 0, "rise": 1, "fall": 2, "both": 3}
CTL_BITS = {"run": 1, "arm": 2, "ren": 4}
LINE_KEYS = ["rate", "baud", "period", "inc", "mod", "taps", "preset", "phase", "window", "edge", "follow", "t0edge",
             "snap", "pins", "pina", "pinb", "in0", "in1", "lut0", "lut1", "hold", "ctl", "minperiod", "minhalf"]
THREAD_KEYS = ["core", "line", "trigger", "watch0", "watch1", "start", "pc", "enable", "disable"]
OUT_KEYS = ["line", "sel", "lut", "oe", "lutraw", "oeraw", "segN:"]
STREAM_KEYS = ["mode", "order", "start", "len", "mark"]
NONE_PIN = 15            # a pin select of 13..15 reads constant 0 (SPEC v2 2); the tools write 15


def strip_comment(line: str) -> str:
    out, q = [], False
    for c in line:
        if c == '"':
            q = not q
        elif not q and c == ";":
            break
        out.append(c)
    return "".join(out).strip()


def split_top(s: str, sep: str = ",") -> list:
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
    """The write group of a destination port (SPEC v2 6, from machine.WRITE_GROUPS)."""
    if dst == "NULL":
        return None
    for g, members in M.WRITE_GROUPS.items():
        if dst in members:
            return g
    return dst


def _norm_pin(t: str) -> str:
    t = t.strip().lower().replace(" ", "")
    for a, b in (("uio_in", "uio"), ("uio_out", "uio"), ("ui_in", "ui"), ("uo_out", "uo")):
        t = t.replace(a, b)
    return t


def parse_in_pin(tok: str, env: dict) -> int:
    t = tok.strip()
    if t.lower() in ("none", "off", "-"):
        return NONE_PIN
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


# ------------------------------------------------------------------------------------------------------------
# instruction parsing
# ------------------------------------------------------------------------------------------------------------
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
    if cond not in M.GUARD_ID:
        raise AsmError(f"unknown condition {cond!r}{suggest(cond, M.GUARD_ID)}", line)
    pause = bool(_PAUSE.search(s))
    s = _PAUSE.sub(" ", s)
    goto = _GOTO.search(s)
    target = jkind = None
    jcond = "TRUE"
    if goto:
        tname, jkind, jc = goto.group(1), goto.group(2), goto.group(3)
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
        if jkind:
            jcond = (jc or cond).upper()
            if jcond == "TRUE" and not jc:
                raise AsmError("'goto L if' / 'goto L ifnot' needs a jump condition: write 'goto L if COND' "
                               "or add 'when COND'", line)
            if jcond not in M.JGUARD_ID:
                raise AsmError(f"{jcond!r} is not a jump condition (SPEC v2 7); jumps accept: "
                               f"{', '.join(M.JUMP_GUARDS)}. Copy other conditions to a flag first, or use them "
                               f"as the move condition", line)

    if re.fullmatch(r"\s*nop\s*", s):
        s = ""
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
                src = "ZERO"
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
    if needs_cond and cond == "TRUE":
        raise AsmError("a '?' or '!' move guard needs a condition: add 'when COND'", line)
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
    insn = Insn(tuple(moves), cond, jmode, jcond, vals[0] if vals else 0, pause)
    for i, a in enumerate(moves):
        for b in moves[i + 1:]:
            ga, gb = write_group(a.dst), write_group(b.dst)
            if ga is None or ga != gb or "never" in (a.guard, b.guard):
                continue
            if {a.guard, b.guard} == {"if", "ifnot"}:
                continue
            raise AsmError(f"moves to {a.dst} and {b.dst} write the same group ({ga}) in one cycle and are not "
                           f"exclusive (use '?' / '!' guards); the hardware would set CONFLICT", line)
    return insn


# ------------------------------------------------------------------------------------------------------------
# the assembler proper
# ------------------------------------------------------------------------------------------------------------
class Assembler:
    def __init__(self, text: str, name: str = "<src>"):
        self.name = name
        self.prog = Program(source_name=name)
        self.env: dict = {}
        self.items: list = []
        self.raw_insns: list = []
        self.equs: list = []
        self._parse(text)

    def _err(self, msg, line):
        return AsmError(msg, line, self.name)

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
                    if lbl in self.prog.labels or lbl in pending:
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
                    elif kw in (".line", ".thread", ".out", ".stream"):
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
        for lbl in pending:
            self.prog.labels[lbl] = (core, pc[core])

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
        self._resolve_threads()
        return p

    def _label(self, name: str, core: int, line: int) -> int:
        if name not in self.prog.labels:
            raise self._err(f"unknown label {name!r}{suggest(name, self.prog.labels)}", line)
        c, a = self.prog.labels[name]
        if c != core:
            raise self._err(f"label {name!r} is in core {c} but the thread runs on core {core}", line)
        return a

    def _resolve_threads(self) -> None:
        for t in self.prog.threads.values():
            if t.start is not None:
                t.start_addr = self._label(t.start, t.core, t.line)
            elif t.pc is not None:
                t.start_addr = t.pc
            for k in (0, 1):
                if t.watch[k]:
                    t.watch_addr[k] = self._label(t.watch[k][1], t.core, t.line)

    @staticmethod
    def _lines(it):
        for no, line in it["lines"]:
            key, _, rest = line.partition(" ")
            yield no, key.lower(), rest.strip()

    # -- global directives -----------------------------------------------------------------------------------
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
        m = re.fullmatch(r"thread\s+(\S+)\s+(cycles|insns)\s+(.+)", it["arg"], re.I)
        if not m:
            raise AsmError(".budget thread N cycles|insns VALUE")
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
        width = evaluate_int(kv.get("width", str(M.LFSR_WIDTH)), self.env)
        if not 1 <= width <= M.LFSR_WIDTH:
            raise AsmError(f"width must be 1..{M.LFSR_WIDTH}")
        if "raw" in kv:
            poly = evaluate_int(kv["raw"], self.env)
            init = evaluate_int(kv.get("init", "0"), self.env)
        elif "poly" in kv:
            poly = evaluate_int(kv["poly"], self.env)
            init = evaluate_int(kv.get("init", "0"), self.env)
            if "reflected" not in kv:
                poly, init = rev_bits(poly, width), rev_bits(init, width)
        else:
            raise AsmError(".lfsr N poly=P [width=W] [init=I] [reflected]   |   .lfsr N raw=REG [init=I]")
        mask = (1 << M.LFSR_WIDTH) - 1
        poly, init = poly & mask, init & mask
        self.prog.lfsrs[n] = Lfsr(n, poly, width, init)
        self.env[f"LF{n}_POLY"] = poly
        self.env[f"LF{n}_INIT"] = init
        for b in range(4):
            self.env[f"LF{n}_INIT_B{b}"] = (init >> (8 * b)) & 0xFF

    # -- .line ----------------------------------------------------------------------------------------------
    def _do_line(self, it):
        n = evaluate_int(it["arg"], self.env)
        if not 0 <= n < M.N_LINES:
            raise AsmError(f"line must be 0..{M.N_LINES - 1}")
        ln = LineCfg(n, line=it["line"])
        for no, key, rest in self._lines(it):
            try:
                self._line_key(ln, key, rest, dict(self.env, INC=ln.inc, MOD=ln.mod))
            except (AsmError, ExprError) as e:
                raise _wrap(e, no, self.name) from None
        if not (ln.inc and ln.mod):
            raise AsmError(f"line {n}: needs 'rate'/'baud', 'period' or 'inc' + 'mod'")
        for nm, v in (("inc", ln.inc), ("mod", ln.mod), ("preset", ln.pre), ("wlo", ln.wlo), ("whi", ln.whi)):
            if not 0 <= v <= 0xFFFF:
                raise AsmError(f"line {n}: {nm} = {v} does not fit 16 bits")
        for k, t in enumerate(ln.taps):
            if t is not None and not 0 <= t <= 0xFFFF:
                raise AsmError(f"line {n}: tap {k} = {t} does not fit 16 bits")
        if ln.phase is not None and not 0 <= ln.phase <= 0xFFFF:
            raise AsmError(f"line {n}: phase does not fit 16 bits")
        self.prog.lines[n] = ln
        self.env[f"L{n}_INC"] = ln.inc
        self.env[f"L{n}_MOD"] = ln.mod
        self.env[f"L{n}_PERIOD"] = ln.mod / ln.inc

    def _line_key(self, ln: LineCfg, key: str, rest: str, env: dict) -> None:
        if key in ("rate", "baud"):
            rate = evaluate(rest, env)
            exact = (Fraction(rate) / Fraction(self.prog.clock_hz)).limit_denominator(10**12)
            frac = exact
            if frac.numerator > 0xFFFF or frac.denominator > 0xFFFF:
                frac = exact.limit_denominator(0xFFFF)
                ppm = abs(float(frac / exact) - 1) * 1e6
                self.prog.warnings.append(
                    f"line {ln.n}: rate {rate} Hz at {self.prog.clock_hz / 1e6:g} MHz is not exact; using "
                    f"inc/mod = {frac.numerator}/{frac.denominator} ({ppm:.0f} ppm error, calculated)")
            if frac <= 0 or frac >= 1:
                raise AsmError(f"rate {rate} Hz is not within 0..clock ({self.prog.clock_hz:g} Hz)")
            ln.inc, ln.mod = frac.numerator, frac.denominator
        elif key == "period":
            ln.inc, ln.mod = 1, evaluate_int(rest, env)
        elif key == "inc":
            ln.inc = evaluate_int(rest, env)
        elif key == "mod":
            ln.mod = evaluate_int(rest, env)
        elif key == "taps":
            items = rest.replace(",", " ").split()
            if len(items) > 3:
                raise AsmError("at most three taps")
            ln.taps = [None, None, None]
            for k, t in enumerate(items):
                ln.taps[k] = None if t in ("-", "off") else evaluate_int(t, env)
        elif key == "preset":
            ln.pre = evaluate_int(rest, env)
        elif key == "phase":
            ln.phase = evaluate_int(rest, env)
        elif key == "window":
            lo, hi = rest.replace(",", " ").split()
            ln.wlo, ln.whi = evaluate_int(lo, env), evaluate_int(hi, env)
            ln.wen = 1
        elif key == "edge":
            toks = rest.split()
            ln.edge_pin = parse_in_pin(toks[0], env)
            pol = toks[1].lower() if len(toks) > 1 else "rise"
            ln.edge_pol = 0 if toks[0].lower() in ("none", "off", "-") else \
                (POLARITY[pol] if pol in POLARITY else evaluate_int(pol, env))
        elif key == "follow":
            ln.follow = 1
        elif key == "t0edge":
            toks = rest.split()
            ln.t0_pin = parse_in_pin(toks[0], env)
            pol = toks[1].lower() if len(toks) > 1 else "rise"
            ln.t0_pol = POLARITY[pol] if pol in POLARITY else evaluate_int(pol, env)
            ln.t0src = 1
        elif key == "snap":
            t = rest.lower().replace(" ", "")
            if t in ("beat", "boundary"):
                ln.snap = 3
            elif re.fullmatch(r"tap[0-2]", t):
                ln.snap = int(t[3:])
            else:
                ln.snap = evaluate_int(t, env)
            if not 0 <= ln.snap <= 3:
                raise AsmError("snap: tap0|tap1|tap2|beat")
        elif key == "pins":
            for item in rest.replace(",", " ").split():
                k, _, v = item.partition("=")
                self._line_key(ln, "pin" + k.lower(), v, env)
        elif key == "pina":
            ln.pina = parse_in_pin(rest, env)
        elif key == "pinb":
            ln.pinb = parse_in_pin(rest, env)
        elif key in ("in0", "in1"):
            setattr(ln, "lut" + key[-1], self._lut(rest, ["a0", "a1", "a2", "b1", "rem"], M.LUT_IN_BITS))
        elif key in ("lut0", "lut1"):
            setattr(ln, key, evaluate_int(rest, env) & 0xFFFFFFFF)
        elif key == "hold":
            toks = rest.replace("=", " ").replace(",", " ").split()
            toks = [t for t in toks if t.lower() not in ("pin", "level", "on")]
            if len(toks) < 3:
                raise AsmError("hold PIN LEVEL tapK   (e.g. 'hold P3 high tap1'; LEVEL 0|1|low|high)")
            ln.hpin = parse_in_pin(toks[0], env)
            lv = toks[1].lower()
            ln.hlvl = {"high": 1, "h": 1, "low": 0, "l": 0}[lv] if lv in ("high", "h", "low", "l") \
                else evaluate_int(lv, env)
            if ln.hlvl not in (0, 1):
                raise AsmError("hold level must be 0, 1, low or high")
            ln.htap = evaluate_int("".join(toks[2:]).lower().replace("tap", ""), env)
            if not 0 <= ln.htap <= 2:
                raise AsmError("hold tap must be 0..2")
            ln.hen = 1
        elif key == "ctl":
            for w in rest.replace(",", " ").split():
                ln.ctl |= CTL_BITS[w.lower()] if w.lower() in CTL_BITS else evaluate_int(w, env)
        elif key == "minperiod":
            ln.minperiod = evaluate_int(rest, env)
        elif key == "minhalf":
            ln.minhalf = evaluate_int(rest, env)
        else:
            raise AsmError(f"unknown line setting {key!r}{suggest(key, LINE_KEYS)}")

    def _lut(self, rest: str, names: list, bits: int, widths: list | None = None) -> int:
        widths = widths or [1] * len(names)
        lut = 0
        for idx in range(1 << bits):
            env = dict(self.env)
            sh = 0
            for nm, w in zip(names, widths):
                env[nm] = (idx >> sh) & ((1 << w) - 1)
                sh += w
            if evaluate_int(rest, env) & 1:
                lut |= 1 << idx
        return lut

    # -- .thread --------------------------------------------------------------------------------------------
    def _do_thread(self, it):
        n = evaluate_int(it["arg"], self.env)
        if not 0 <= n < M.N_THREADS:
            raise AsmError(f"thread must be 0..{M.N_THREADS - 1}")
        t = ThreadCfg(n, line=it["line"])
        for no, key, rest in self._lines(it):
            try:
                self._thread_key(t, key, rest)
            except (AsmError, ExprError) as ex:
                raise _wrap(ex, no, self.name) from None
        if t.line_ is not None and t.trigger_line is not None and t.line_ != t.trigger_line:
            self.prog.warnings.append(
                f"thread {n}: trigger {t.trigger} but bound to line {t.line_}; symbols commit on line "
                f"{t.line_}'s boundaries and the commit deadline cannot be checked")
        self.prog.threads[n] = t

    def _thread_key(self, t: ThreadCfg, key: str, rest: str) -> None:
        env = self.env
        if key == "core":
            t.core = evaluate_int(rest, env)
            if not 0 <= t.core < M.N_CORES:
                raise AsmError(f"core must be 0..{M.N_CORES - 1}")
        elif key == "line":
            t.line_ = evaluate_int(rest, env)
            if not 0 <= t.line_ < M.N_LINES:
                raise AsmError(f"line must be 0..{M.N_LINES - 1}")
        elif key == "trigger":
            tr = rest.upper()
            if tr not in M.TRIG_ID:
                raise AsmError(f"unknown trigger {rest!r}{suggest(tr, M.TRIG_ID)}; see wiki/ISA_TABLES_V2.md")
            t.trigger = tr
        elif key in ("watch0", "watch1"):
            m = re.fullmatch(r"([A-Za-z0-9_.]+)\s*->\s*(\S+)", rest)
            if not m:
                raise AsmError(f"{key} COND -> handler_label")
            cond = m.group(1).upper()
            if cond not in M.GUARD_ID:
                raise AsmError(f"unknown condition {cond!r}{suggest(cond, M.GUARD_ID)}")
            if cond == "TRUE":
                raise AsmError("a watcher on TRUE would hijack every burst (guard 0 disables a watcher)")
            t.watch[int(key[-1])] = (cond, m.group(2))
        elif key == "start":
            t.start = rest
        elif key == "pc":
            t.pc = evaluate_int(rest, env)
        elif key in ("enable", "disable"):
            t.enable = key == "enable"
        else:
            raise AsmError(f"unknown thread setting {key!r}{suggest(key, THREAD_KEYS)}")

    # -- .out -----------------------------------------------------------------------------------------------
    def _do_out(self, it):
        n = parse_out_pin(it["arg"], self.env)
        o = OutCfg(n, line=it["line"])
        rows = {"lut": {}, "oe": {}}
        for no, key, rest in self._lines(it):
            try:
                if key == "line":
                    if rest.lower() in ("none", "unbound"):
                        o.line_ = None
                    else:
                        o.line_ = evaluate_int(rest, self.env)
                        if not 0 <= o.line_ < M.N_LINES:
                            raise AsmError("line out of range")
                elif key == "sel":
                    v = tuple(evaluate_int(x, self.env) for x in rest.replace(",", " ").split())
                    if len(v) != 3 or any(not 0 <= x < M.OSYM_BITS for x in v):
                        raise AsmError(f"sel B0 B1 B2: three symbol bit numbers 0..{M.OSYM_BITS - 1}")
                    o.sel = v
                elif key in ("lut", "oe"):
                    if key == "oe" and rest.lower() in ("always", "on"):
                        val = (1 << (1 << M.PIN_LUT_IN_BITS)) - 1
                    elif key == "oe" and rest.lower() in ("never", "off"):
                        val = 0
                    else:
                        val = self._lut(rest, ["b0", "b1", "b2", "seg"], M.PIN_LUT_IN_BITS, [1, 1, 1, 2])
                    setattr(o, key, val)
                elif key in ("lutraw", "oeraw"):
                    setattr(o, key[:-3], evaluate_int(rest, self.env) & 0xFFFFFFFF)
                elif key.startswith(("seg", "oeseg")):
                    m = re.fullmatch(r"(oe)?seg\s*(\d)\s*:\s*(.*)", (key + " " + rest).strip(), re.I)
                    if not m:
                        raise AsmError("segN: v0..v7   (levels for table input b2 b1 b0 = 0..7)")
                    seg = int(m.group(2))
                    vals = [evaluate_int(x, self.env) for x in m.group(3).replace(",", " ").split()]
                    if seg > 3 or len(vals) != 8:
                        raise AsmError("segN: needs seg 0..3 and eight values")
                    rows["oe" if m.group(1) else "lut"][seg] = vals
                else:
                    raise AsmError(f"unknown out setting {key!r}{suggest(key, OUT_KEYS)}")
            except (AsmError, ExprError) as ex:
                raise _wrap(ex, no, self.name) from None
        for attr, table in rows.items():
            if table:
                v = 0
                for seg, vals in table.items():
                    for i, b in enumerate(vals):
                        if b & 1:
                            v |= 1 << (seg * 8 + i)
                setattr(o, attr, v)
        if o.oe and n >= M.N_OE_PINS:
            self.prog.warnings.append(f"out O{n}: pin has no output-enable table; 'oe' ignored")
            o.oe = 0
        self.prog.outs[n] = o

    # -- .stream --------------------------------------------------------------------------------------------
    def _do_stream(self, it):
        n = evaluate_int(it["arg"], self.env)
        if not 0 <= n < M.N_STREAMS:
            raise AsmError(f"stream must be 0..{M.N_STREAMS - 1}")
        s = StreamCfg(n, line=it["line"])
        for no, key, rest in self._lines(it):
            try:
                v = rest.lower()
                if key == "mode":
                    if v not in ("tx", "transmit", "rx", "receive"):
                        raise AsmError("mode tx|rx")
                    s.rx = int(v in ("rx", "receive"))
                elif key == "order":
                    if v not in ("msb", "lsb"):
                        raise AsmError("order msb|lsb")
                    s.msb = int(v == "msb")
                elif key in ("start", "len", "mark"):
                    val = evaluate_int(rest, self.env)
                    lim = {"start": M.DATA_BYTES - 1, "len": M.DATA_BYTES, "mark": M.DATA_BYTES}[key]
                    if not 0 <= val <= lim:
                        raise AsmError(f"stream {key} {val} outside 0..{lim}")
                    setattr(s, key, val)
                else:
                    raise AsmError(f"unknown stream setting {key!r}{suggest(key, STREAM_KEYS)}")
            except (AsmError, ExprError) as ex:
                raise _wrap(ex, no, self.name) from None
        self.prog.streams[n] = s


def assemble_text(text: str, name: str = "<src>") -> Program:
    return Assembler(text, name).assemble()


def assemble_file(path) -> Program:
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
    ap = argparse.ArgumentParser(prog="metronome2_tools.asm", description="Metronome v2 assembler")
    ap.add_argument("source")
    ap.add_argument("-o", "--output", help="program image JSON to write")
    ap.add_argument("-l", "--listing", action="store_true")
    ap.add_argument("--no-check", action="store_true", help="skip the static checks (SPEC v2 10.4)")
    ap.add_argument("-v", "--verbose", action="store_true")
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
