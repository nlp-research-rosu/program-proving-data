#!/usr/bin/env python3
"""py2mpy — a *pure* CPython-AST -> K-constructor transliterator.

Reads a .py file and prints the matching `.mpy` term: a Lisp-indented tree of K
constructors that a (future) K semantics will parse. The design rule is strict:

    PURE TRANSLITERATION. Every Python AST node maps to exactly one K
    constructor with the same structure. The front-end makes NO semantic
    decisions — it does not desugar, simplify, normalize, or "interpret"
    anything. All meaning lives in the K semantics that consumes the term.

Consequences of that rule (vs. a "helpful" front-end):

  * `is` / `is not` transliterate to `CmpOp("is", ...)` / `CmpOp("is not", ...)`
    — NOT to `==` / `!=`. K decides what identity means.
  * a chained comparison `a < b < c` stays a single `Compare` carrying the
    chain (`Compare(a, CmpOp("<", b), CmpOp("<", c))`) — it is NOT pre-expanded
    into `a < b and b < c`.
  * a method call `x.append(v)` stays `Call(Attribute(Name("x"), "append"), v)`
    — there is no special `MethodCall` constructor folding the receiver in.
  * `a[i] = v` stays `Assign(Subscript(Name("a"), Name("i")), v)` — the target
    is just an expression in store position; no special `SubscriptAssign`.

The only choices the transliterator makes are unavoidably *syntactic* — e.g. a
`bool` literal becomes `Bool(...)` not `Int(...)`, because that is the literal's
actual Python type as read off the AST, not a semantic judgement.

Anything outside the covered subset raises `Unsupported`, naming the node, so
coverage gaps fail loudly instead of being silently dropped.

Usage:
    python scripts/py2mpy.py FILE.py          # print the .mpy term (default)
    python scripts/py2mpy.py FILE.py --ast    # print the Python AST (ast.dump)
"""
from __future__ import annotations

import argparse
import symtable
import ast
import json
import sys


class Unsupported(Exception):
    """Raised for any AST node the transliterator does not cover."""


# ---------------------------------------------------------------------------
# Term model: a .mpy term is a tree of these three node kinds.
#   Ctor(name, *args)  -> `name(arg, arg, ...)`  (comma-separated args)
#   Seq([item, ...])   -> a statement list: juxtaposed, no parens, no commas
#   str                -> a leaf token already in K surface form
#                         (a quoted string `"op"`, a number `0`, `true`, `Break`)
# ---------------------------------------------------------------------------
class Ctor:
    __slots__ = ("name", "args")

    def __init__(self, name: str, *args):
        self.name = name
        self.args = list(args)


class Seq:
    __slots__ = ("items",)

    def __init__(self, items):
        self.items = list(items)


def q(s: str) -> str:
    """A Python string as a K String token (double-quoted, escaped)."""
    return json.dumps(s)


# --- Operator spellings (string tokens carried inside constructors) ----------
# These are transliterations of the operator *symbol*, not its meaning.
_BINOP = {
    ast.Add: "+", ast.Sub: "-", ast.Mult: "*", ast.Div: "/",
    ast.FloorDiv: "//", ast.Mod: "%", ast.Pow: "**",
    ast.BitOr: "|", ast.BitAnd: "&", ast.BitXor: "^",
    ast.LShift: "<<", ast.RShift: ">>", ast.MatMult: "@",
}
_UNARY = {ast.USub: "-", ast.UAdd: "+", ast.Not: "not", ast.Invert: "~"}
_BOOLOP = {ast.And: "and", ast.Or: "or"}
_CMPOP = {
    ast.Eq: "==", ast.NotEq: "!=", ast.Lt: "<", ast.LtE: "<=",
    ast.Gt: ">", ast.GtE: ">=", ast.Is: "is", ast.IsNot: "is not",
    ast.In: "in", ast.NotIn: "not in",
}


# ---------------------------------------------------------------------------
# Closure scopes (Python's own symtable, faithfully exposed)
# ---------------------------------------------------------------------------
# (name, lineno) -> (cellvars, freevars, nested). A def/lambda gets the
# ANNOTATED node form iff it is nested inside a function or has cells/frees;
# module-level capture-free defs keep the old shape (zero churn).
SCOPES: dict = {}


def _frees(table):
    return set(table.get_frees()) if isinstance(table, symtable.Function) else set()


def _deep_frees(table):
    out = _frees(table)
    for g in table.get_children():
        out |= _deep_frees(g) - set(table.get_locals())
    return out


def _walk_symtable(table, depth=0):
    for child in table.get_children():
        if child.get_type() in ("function", "lambda"):
            frees = sorted(_frees(child))
            cells = sorted(
                s for s in child.get_locals()
                if any(s in _deep_frees(g) for g in child.get_children())
            )
            SCOPES[(child.get_name(), child.get_lineno())] = (
                cells, frees, depth > 0 or table.get_type() != "module")
        _walk_symtable(child, depth + (1 if child.get_type() in ("function", "lambda") else 0))


def scope_info(name, lineno):
    return SCOPES.get((name, lineno))


# ---------------------------------------------------------------------------
# Expressions
# ---------------------------------------------------------------------------
def emit_expr(node: ast.expr):
    if isinstance(node, ast.Constant):
        v = node.value
        if v is None:
            return "NoneVal"
        if isinstance(v, bool):                 # MUST precede int (bool ⊂ int)
            return Ctor("Bool", "true" if v else "false")
        if isinstance(v, int):
            return Ctor("Int", str(v))
        if isinstance(v, float):
            return Ctor("Float", repr(v))
        if isinstance(v, str):
            return Ctor("Str", q(v))
        raise Unsupported(f"Constant {type(v).__name__}")

    if isinstance(node, ast.Name):
        return Ctor("Name", q(node.id))

    if isinstance(node, ast.Lambda):
        a = node.args
        if a.vararg or a.kwarg or a.kwonlyargs or a.defaults or a.kw_defaults:
            raise Unsupported("complex lambda signature")
        names = [p.arg for p in (a.posonlyargs + a.args)]
        params = Ctor("Params", *(q(n) for n in names))
        info = scope_info("lambda", node.lineno)
        if info and (info[0] or info[1] or info[2]):
            cells, frees, _ = info
            return Ctor("Lambda", params,
                        Ctor("CellVars", *(q(n) for n in cells)),
                        Ctor("FreeVars", *(q(n) for n in frees)),
                        emit_expr(node.body))
        return Ctor("Lambda", params, emit_expr(node.body))

    if isinstance(node, ast.BinOp):
        op = _BINOP.get(type(node.op))
        if op is None:
            raise Unsupported(f"BinOp {type(node.op).__name__}")
        return Ctor("BinOp", q(op), emit_expr(node.left), emit_expr(node.right))

    if isinstance(node, ast.UnaryOp):
        op = _UNARY.get(type(node.op))
        if op is None:
            raise Unsupported(f"UnaryOp {type(node.op).__name__}")
        return Ctor("UnaryOp", q(op), emit_expr(node.operand))

    if isinstance(node, ast.BoolOp):
        op = _BOOLOP[type(node.op)]
        return Ctor("BoolOp", q(op), *(emit_expr(v) for v in node.values))

    if isinstance(node, ast.Compare):
        # Faithful, non-desugared: left operand + a chain of (op, comparator).
        # Single comparison => one CmpOp; `a < b < c` => two CmpOps.
        chain = [
            Ctor("CmpOp", q(_op_or_raise(_CMPOP, op, "Compare")), emit_expr(c))
            for op, c in zip(node.ops, node.comparators)
        ]
        return Ctor("Compare", emit_expr(node.left), *chain)

    if isinstance(node, ast.List):
        return Ctor("ListExpr", *(emit_expr(e) for e in node.elts))

    if isinstance(node, ast.Tuple):
        return Ctor("TupleExpr", *(emit_expr(e) for e in node.elts))

    if isinstance(node, ast.Set):
        return Ctor("SetExpr", *(emit_expr(e) for e in node.elts))

    if isinstance(node, ast.Dict):
        entries = []
        for k, v in zip(node.keys, node.values):
            if k is None:
                raise Unsupported("dict unpacking {**x}")
            entries.append(Ctor("Entry", emit_expr(k), emit_expr(v)))
        return Ctor("DictExpr", *entries)

    if isinstance(node, ast.Subscript):
        return Ctor("Subscript", emit_expr(node.value), emit_index(node.slice))

    if isinstance(node, ast.Attribute):
        return Ctor("Attribute", emit_expr(node.value), q(node.attr))

    if isinstance(node, ast.Call):
        if any(isinstance(a, ast.Starred) for a in node.args):
            raise Unsupported("*args unpacking")
        if any(kw.arg is None for kw in node.keywords):
            raise Unsupported("**kwargs unpacking")
        # Call grammar is `Call(Expr, Exprs)` — the comma is mandatory, so a zero-arg
        # call must render as `Call(f, )` (empty Exprs), NOT `Call(f)` (which won't parse).
        args = [emit_expr(a) for a in node.args]
        args += [Ctor("KwArg", q(kw.arg), emit_expr(kw.value)) for kw in node.keywords]
        args = args or [""]
        return Ctor("Call", emit_expr(node.func), *args)

    if isinstance(node, ast.IfExp):
        # AST field order: test, body, orelse — kept verbatim.
        return Ctor("IfExp", emit_expr(node.test),
                    emit_expr(node.body), emit_expr(node.orelse))

    if isinstance(node, ast.ListComp):
        return Ctor("ListComp", emit_expr(node.elt), _gens(node.generators))
    if isinstance(node, ast.SetComp):
        return Ctor("SetComp", emit_expr(node.elt), _gens(node.generators))
    if isinstance(node, ast.GeneratorExp):
        return Ctor("GenExp", emit_expr(node.elt), _gens(node.generators))
    if isinstance(node, ast.DictComp):
        return Ctor("DictComp", emit_expr(node.key), emit_expr(node.value),
                    _gens(node.generators))

    raise Unsupported(f"Expr {type(node).__name__}")


def _op_or_raise(table, op, label):
    spelled = table.get(type(op))
    if spelled is None:
        raise Unsupported(f"{label} {type(op).__name__}")
    return spelled


def _compfor(g):
    """A single generator -> CompFor(target, iter, <ifs as Exprs; .Exprs if none>)."""
    if getattr(g, "is_async", 0):
        raise Unsupported("async comprehension")
    ifs = [emit_expr(c) for c in g.ifs] or [Ctor("Bool", "true")]
    return Ctor("CompFor", emit_expr(g.target), emit_expr(g.iter), *ifs)


def _gens(generators):
    """The generator list -> a juxtaposed CompFors (a Seq of CompFor)."""
    return Seq([_compfor(g) for g in generators])


def emit_index(node: ast.expr):
    """Subscript index position: an `ast.Slice` -> `Slice(...)`, else the expr."""
    # Python <3.9 wrapped the index in ast.Index; unwrap if present.
    inner = getattr(ast, "Index", None)
    if inner is not None and isinstance(node, inner):
        node = node.value
    if isinstance(node, ast.Slice):
        def bound(b):
            # omitted bound (absent field) OR an explicit None constant -> NoBound.
            # Python treats `a[None:5]` exactly like `a[:5]`; only a *value* None
            # (Constant(None) outside a slice) becomes NoneVal. Keeping the two
            # distinct lets NoneVal be a real value without perturbing slices.
            if b is None or (isinstance(b, ast.Constant) and b.value is None):
                return "NoBound"
            return emit_expr(b)
        return Ctor("Slice", bound(node.lower), bound(node.upper), bound(node.step))
    return emit_expr(node)


# ---------------------------------------------------------------------------
# Statements
# ---------------------------------------------------------------------------
def emit_stmt(node: ast.stmt):
    if isinstance(node, ast.FunctionDef):
        a = node.args
        if a.vararg or a.kwarg or a.kwonlyargs or a.defaults or a.kw_defaults:
            raise Unsupported("complex function signature (defaults/varargs/kwonly)")
        if node.decorator_list:
            raise Unsupported("decorators")
        names = [p.arg for p in (a.posonlyargs + a.args)]  # type annotations ignored
        params = Ctor("Params", *(q(n) for n in names))
        info = scope_info(node.name, node.lineno)
        if info and (info[0] or info[1] or info[2]):
            cells, frees, _ = info
            return Ctor("FuncDef", q(node.name), params,
                        Ctor("CellVars", *(q(n) for n in cells)),
                        Ctor("FreeVars", *(q(n) for n in frees)),
                        emit_stmts(node.body))
        return Ctor("FuncDef", q(node.name), params, emit_stmts(node.body))

    if isinstance(node, ast.Return):
        if node.value is None:
            return Ctor("Return")
        return Ctor("Return", emit_expr(node.value))

    if isinstance(node, ast.Assign):
        if len(node.targets) != 1:
            raise Unsupported("chained assignment (a = b = ...)")
        # Target is just an expression in store position (Name / Tuple / Subscript / Attribute).
        return Ctor("Assign", emit_expr(node.targets[0]), emit_expr(node.value))

    if isinstance(node, ast.AugAssign):
        op = _BINOP.get(type(node.op))
        if op is None:
            raise Unsupported(f"AugAssign {type(node.op).__name__}")
        return Ctor("AugAssign", emit_expr(node.target), q(op), emit_expr(node.value))

    if isinstance(node, ast.If):
        return Ctor("If", emit_expr(node.test),
                    emit_stmts(node.body), emit_stmts(node.orelse))

    if isinstance(node, ast.For):
        if node.orelse:
            raise Unsupported("for-else")
        return Ctor("For", emit_expr(node.target), emit_expr(node.iter),
                    emit_stmts(node.body))

    if isinstance(node, ast.While):
        if node.orelse:
            raise Unsupported("while-else")
        return Ctor("While", emit_expr(node.test), emit_stmts(node.body))

    if isinstance(node, ast.Break):
        return "Break"
    if isinstance(node, ast.Continue):
        return "Continue"
    if isinstance(node, ast.Pass):
        return "Pass"

    if isinstance(node, ast.Assert):
        if node.msg is not None:
            return Ctor("Assert", emit_expr(node.test), emit_expr(node.msg))
        return Ctor("Assert", emit_expr(node.test))

    if isinstance(node, ast.Expr):
        return Ctor("Expr", emit_expr(node.value))

    if isinstance(node, ast.Import):
        return Ctor("Import", *(q(n.name) for n in node.names))
    if isinstance(node, ast.ImportFrom):
        mod = node.module if node.module is not None else ""
        return Ctor("ImportFrom", q(mod), *(q(n.name) for n in node.names))

    raise Unsupported(f"Stmt {type(node).__name__}")


def emit_stmts(stmts) -> Seq:
    return Seq([emit_stmt(s) for s in stmts])


def emit_module(tree: ast.Module) -> Ctor:
    return Ctor("Module", emit_stmts(tree.body))


# ---------------------------------------------------------------------------
# Lisp-style pretty printer
# ---------------------------------------------------------------------------
WIDTH = 72  # an expression constructor wider than this breaks onto its own lines


def render(node, ind: int = 0) -> str:
    if isinstance(node, str):
        return node

    if isinstance(node, Seq):
        if not node.items:
            return ""
        pad = "  " * ind
        return ("\n" + pad).join(render(it, ind) for it in node.items)

    # Ctor
    cind = ind + 1
    cpad = "  " * cind
    has_block = any(isinstance(a, Seq) for a in node.args)

    if not has_block:
        inline = node.name + "(" + ", ".join(render(a, ind) for a in node.args) + ")"
        if "\n" not in inline and len("  " * ind) + len(inline) <= WIDTH:
            return inline
        parts = [render(a, cind) for a in node.args]
        return node.name + "(\n" + cpad + (",\n" + cpad).join(parts) + ")"

    # Has a statement block: inline the args before the first block, then put
    # each remaining arg (blocks included) on its own indented line.
    first = next(i for i, a in enumerate(node.args) if isinstance(a, Seq))
    head = node.args[:first]
    rest = node.args[first:]
    open_line = node.name + "(" + ", ".join(render(a, ind) for a in head) + ("," if head else "")
    lines = []
    for k, a in enumerate(rest):
        comma = "," if k < len(rest) - 1 else ""
        lines.append(cpad + render(a, cind) + comma)
    return open_line + "\n" + "\n".join(lines) + ")"


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        prog="py2mpy",
        description="Pure CPython-AST -> K-constructor transliterator.",
    )
    ap.add_argument("file", help="Python source file")
    ap.add_argument("--ast", action="store_true",
                    help="print the Python AST (ast.dump) instead of the .mpy term")
    args = ap.parse_args(argv)

    with open(args.file, "r", encoding="utf-8") as fh:
        src = fh.read()
    tree = ast.parse(src, filename=args.file)
    _walk_symtable(symtable.symtable(src, args.file, "exec"))

    if args.ast:
        print(ast.dump(tree, indent=2))
    else:
        print(render(emit_module(tree)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
