#!/usr/bin/env python3
"""py2mpy_traced — the vendored py2mpy transliterator + LineMark interleaving.

Wraps vendor/klever/scripts/py2mpy.py (imported, not forked) and intercepts its
`emit_stmts` so that every statement list gets a `LineMark(<lineno>)` before each
statement. Loop statements (While/For) additionally get a LineMark of the loop
header line appended at the END of their body: sys.settrace re-logs the header
line before every condition/iterator re-check, and the body-end marker
reproduces that cadence exactly (initial marker + one per completed iteration =
iterations + 1 header events, matching CPython; `break` skips it, also matching
CPython; `continue` would skip one — known limitation, no sample uses it).

With --no-linemarks the output is byte-identical to the vendored py2mpy
(golden-checked by scripts/validate.py).
"""
from __future__ import annotations

import argparse
import ast
import symtable
import sys
from pathlib import Path

VENDOR_SCRIPTS = Path(__file__).resolve().parent.parent / "vendor" / "klever" / "scripts"
sys.path.insert(0, str(VENDOR_SCRIPTS))
import py2mpy as p2m  # noqa: E402


def _traced_emit_stmts(stmts) -> "p2m.Seq":
    items = []
    for s in stmts:
        items.append(p2m.Ctor("LineMark", str(s.lineno)))
        node = p2m.emit_stmt(s)  # nested bodies re-enter this function via the patch
        if isinstance(s, (ast.While, ast.For)):
            body_seq = node.args[-1]
            assert isinstance(body_seq, p2m.Seq)
            body_seq.items.append(p2m.Ctor("LineMark", str(s.lineno)))
        items.append(node)
    return p2m.Seq(items)


def to_mpy(path: str, linemarks: bool = True) -> str:
    src = Path(path).read_text(encoding="utf-8")
    tree = ast.parse(src, filename=path)
    p2m.SCOPES.clear()
    p2m._walk_symtable(symtable.symtable(src, path, "exec"))
    orig = p2m.emit_stmts
    if linemarks:
        p2m.emit_stmts = _traced_emit_stmts
    try:
        term = p2m.emit_module(tree)
    finally:
        p2m.emit_stmts = orig
    return p2m.render(term) + "\n"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="py2mpy_traced")
    ap.add_argument("file")
    ap.add_argument("--no-linemarks", action="store_true",
                    help="plain vendored py2mpy output (golden-identity mode)")
    args = ap.parse_args(argv)
    sys.stdout.write(to_mpy(args.file, linemarks=not args.no_linemarks))
    return 0


if __name__ == "__main__":
    sys.exit(main())
