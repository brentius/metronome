"""Small safe expression evaluator used for immediates, .equ values, rates and truth-table expressions."""
from __future__ import annotations

import ast
import operator

__all__ = ["ExprError", "evaluate", "evaluate_int"]


class ExprError(ValueError):
    pass


_BIN = {ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul, ast.FloorDiv: operator.floordiv,
        ast.Div: operator.truediv, ast.Mod: operator.mod, ast.LShift: operator.lshift, ast.RShift: operator.rshift,
        ast.BitAnd: operator.and_, ast.BitOr: operator.or_, ast.BitXor: operator.xor, ast.Pow: operator.pow}
_CMP = {ast.Eq: operator.eq, ast.NotEq: operator.ne, ast.Lt: operator.lt, ast.LtE: operator.le,
        ast.Gt: operator.gt, ast.GtE: operator.ge}


def _rev(value: int, width: int) -> int:
    return int(format(value & ((1 << width) - 1), f"0{width}b")[::-1], 2)


_FUNCS = {"min": min, "max": max, "abs": abs, "int": int, "round": round,
          "maj": lambda a, b, c: (a & b) | (a & c) | (b & c), "rev": _rev}


def evaluate(text: str, env: dict | None = None):
    env = env or {}
    try:
        tree = ast.parse(text.strip(), mode="eval")
    except SyntaxError as e:
        raise ExprError(f"bad expression {text!r}: {e.msg}") from None

    def ev(n):
        if isinstance(n, ast.Expression):
            return ev(n.body)
        if isinstance(n, ast.Constant) and isinstance(n.value, (int, float, bool)):
            return n.value
        if isinstance(n, ast.Name):
            if n.id in env:
                return env[n.id]
            raise ExprError(f"unknown name {n.id!r} in {text!r}")
        if isinstance(n, ast.BinOp) and type(n.op) in _BIN:
            try:
                return _BIN[type(n.op)](ev(n.left), ev(n.right))
            except (ZeroDivisionError, ValueError, OverflowError) as e:
                raise ExprError(f"{e} in {text!r}") from None
        if isinstance(n, ast.UnaryOp):
            v = ev(n.operand)
            if isinstance(n.op, ast.USub):
                return -v
            if isinstance(n.op, ast.UAdd):
                return +v
            if isinstance(n.op, ast.Invert):
                return ~int(v)
            if isinstance(n.op, ast.Not):
                return int(not v)
        if isinstance(n, ast.BoolOp):
            vals = [ev(v) for v in n.values]
            return int(all(vals)) if isinstance(n.op, ast.And) else int(any(vals))
        if isinstance(n, ast.Compare):
            left = ev(n.left)
            for op, comp in zip(n.ops, n.comparators):
                right = ev(comp)
                if type(op) not in _CMP or not _CMP[type(op)](left, right):
                    return 0
                left = right
            return 1
        if isinstance(n, ast.IfExp):
            return ev(n.body) if ev(n.test) else ev(n.orelse)
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in _FUNCS and not n.keywords:
            return _FUNCS[n.func.id](*[ev(a) for a in n.args])
        raise ExprError(f"unsupported syntax in {text!r}")

    return ev(tree)


def evaluate_int(text: str, env: dict | None = None) -> int:
    v = evaluate(text, env)
    if isinstance(v, float):
        if v != int(v):
            raise ExprError(f"{text!r} = {v} is not an integer")
        v = int(v)
    return int(v)
