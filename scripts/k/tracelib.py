"""tracelib — shared assembly of CWM-style event streams.

Two producers, one event schema:
  * K side  : kastjson raw events -> resolved events (call names/def lines via
              the program's own `ast`, return lines via frame tracking,
              exception synthesis from the final <exc> cell).
  * CPython : sys.settrace reference stream, normalized identically.

Event schema (dicts):
  {"event": "line",      "line": int, "locals": {...}}
  {"event": "call",      "line": def_line, "func": str, "locals": bound-args}
  {"event": "return",    "line": int, "value": any, "locals": {...}}
  {"event": "exception", "line": int, "exc": str, "locals": {...}}

Documented normalizations (both sides -> common form):
  N1 module-frame call/return events are dropped (CPython emits them; the K
     module scope has no frame).
  N2 function/builtin values render as "<function NAME>"; dunder keys dropped.
  N3 after the first exception event, CPython's unwind returns and propagated
     per-frame exception duplicates are dropped (the K side halts at raise).
"""
from __future__ import annotations

import ast
import sys
from pathlib import Path
from typing import Any


# --------------------------------------------------------------------------
# Program facts from the source itself
# --------------------------------------------------------------------------
class FuncTable:
    def __init__(self, path: str):
        self.path = path
        src = Path(path).read_text()
        self.source = src
        self.lines = src.splitlines()
        tree = ast.parse(src, filename=path)
        self.funcs: dict[str, dict] = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                body_lines = [n.lineno for n in ast.walk(node) if hasattr(n, "lineno")]
                self.funcs[node.name] = {
                    "def_line": node.lineno,
                    "params": [a.arg for a in node.args.args],
                    "span": (min(body_lines), max(body_lines)),
                }

    def func_of_line(self, line: int) -> str | None:
        for name, f in self.funcs.items():
            lo, hi = f["span"]
            if lo <= line <= hi and line != f["def_line"]:
                return name
        return None

    def src_line(self, line: int) -> str:
        return self.lines[line - 1].strip() if 0 < line <= len(self.lines) else ""


# --------------------------------------------------------------------------
# K side: resolve raw kastjson events into the common schema
# --------------------------------------------------------------------------
def assemble_k_events(raw: list[tuple], ft: FuncTable, final_exc: str | None) -> list[dict]:
    events: list[dict] = []
    frame_last_line: list[int] = []  # per open frame, the last observed line

    for i, ev in enumerate(raw):
        kind = ev[0]
        if kind == "line":
            _, line, locs = ev
            if frame_last_line:
                frame_last_line[-1] = line
            events.append({"event": "line", "line": line, "locals": locs})
        elif kind == "call":
            _, args = ev
            # the callee is the function owning the next line event's line
            callee = None
            for nxt in raw[i + 1:]:
                if nxt[0] == "line":
                    callee = ft.func_of_line(nxt[1])
                    break
            assert callee is not None, "call event with no callee body line"
            f = ft.funcs[callee]
            events.append({
                "event": "call", "line": f["def_line"], "func": callee,
                "locals": dict(zip(f["params"], args)),
            })
            frame_last_line.append(f["def_line"])
        elif kind == "return":
            _, value, locs = ev
            line = frame_last_line.pop() if frame_last_line else 0
            events.append({"event": "return", "line": line, "value": value, "locals": locs})
        else:
            raise ValueError(kind)

    if final_exc is not None:
        last_line = next((e for e in reversed(events) if e["event"] == "line"), None)
        assert last_line is not None
        events.append({"event": "exception", "line": last_line["line"],
                       "exc": final_exc, "locals": last_line["locals"]})
    return events


# --------------------------------------------------------------------------
# CPython side: sys.settrace reference stream (the oracle)
# --------------------------------------------------------------------------
def _norm_val(v: Any) -> Any:
    if callable(v) and hasattr(v, "__name__"):
        return f"<function {v.__name__}>"
    return v


def _norm_locals(d: dict) -> dict:
    return {k: _norm_val(v) for k, v in d.items() if not k.startswith("__")}


def cpython_events(path: str) -> list[dict]:
    src = Path(path).read_text()
    code = compile(src, path, "exec")
    events: list[dict] = []

    def tracer(frame, event, arg):
        if frame.f_code.co_filename != path:
            return None
        is_module = frame.f_code.co_name == "<module>"
        if event == "line":
            events.append({"event": "line", "line": frame.f_lineno,
                           "locals": _norm_locals(frame.f_locals)})
        elif event == "call" and not is_module:                      # N1
            events.append({"event": "call", "line": frame.f_lineno,
                           "func": frame.f_code.co_name,
                           "locals": _norm_locals(frame.f_locals)})
        elif event == "return" and not is_module:                    # N1
            events.append({"event": "return", "line": frame.f_lineno,
                           "value": _norm_val(arg),
                           "locals": _norm_locals(frame.f_locals)})
        elif event == "exception":
            etype = arg[0]
            events.append({"event": "exception", "line": frame.f_lineno,
                           "exc": etype.__name__,
                           "locals": _norm_locals(frame.f_locals)})
        return tracer

    g: dict = {}
    sys.settrace(tracer)
    try:
        exec(code, g)
    except AssertionError:
        pass
    finally:
        sys.settrace(None)

    # N3: keep only the first exception event; drop everything after it
    for i, e in enumerate(events):
        if e["event"] == "exception":
            return events[: i + 1]
    return events


# --------------------------------------------------------------------------
# Comparison
# --------------------------------------------------------------------------
def diff_events(k_events: list[dict], py_events: list[dict]) -> list[str]:
    problems = []
    for i in range(max(len(k_events), len(py_events))):
        k = k_events[i] if i < len(k_events) else None
        p = py_events[i] if i < len(py_events) else None
        if k != p:
            problems.append(f"step {i}:\n  K : {k}\n  PY: {p}")
    return problems
