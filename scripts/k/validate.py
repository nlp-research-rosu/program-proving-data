#!/usr/bin/env python3
"""validate — standalone re-checks over the committed corpus/ (no regeneration).

  1. frontend golden identity: py2mpy_traced --no-linemarks is byte-identical
     to the vendored py2mpy on every program
  2. concrete samples: the stored trace (ignoring k_rules) must equal a fresh
     CPython sys.settrace run, event by event
  3. symbolic samples: every leaf must be witness-validated; each witness is
     re-run in CPython and must reproduce the leaf's line path and return value
  4. verification samples: results match expectations (c1/c2 + all kb ports
     proved, c3 refuted); c3's counterexample is re-run in CPython and must
     violate the ensures clause; kb records' concrete witness finals are
     re-run in CPython and compared binding for binding

Full regeneration (K side) is `make k-data`; this is the cheap invariant check.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts"))

import tracelib  # noqa: E402
from py2mpy_traced import to_mpy  # noqa: E402

FAILURES: list[str] = []


def check(cond: bool, msg: str) -> None:
    tag = "ok" if cond else "FAIL"
    print(f"[{tag}] {msg}")
    if not cond:
        FAILURES.append(msg)


def frontend_identity() -> None:
    for py in sorted((ROOT / "programs").glob("*.py")):
        ours = to_mpy(str(py), linemarks=False)
        theirs = subprocess.run(
            [sys.executable, str(ROOT / "vendor/klever/scripts/py2mpy.py"), str(py)],
            capture_output=True, text=True, check=True).stdout
        check(ours == theirs, f"frontend golden identity: {py.name}")


def concrete() -> None:
    for path in sorted((ROOT / "corpus/k/concrete").glob("*.jsonl")):
        rec = json.loads(path.read_text())
        stored = [{k: v for k, v in e.items() if k != "k_rules"} for e in rec["trace"]]
        fresh = tracelib.cpython_events(str(ROOT / rec["source"]["file"]))
        check(stored == fresh, f"concrete vs sys.settrace: {path.stem} "
                               f"({len(stored)} events)")
        check(all("k_rules" in e for e in rec["trace"]),
              f"k_rules present on every event: {path.stem}")


def _subst_magics(code: str, witness: dict) -> str:
    magics = {"x": "31337", "a": "31337", "b": "31338", "c": "31339"}
    for var, val in witness.items():
        code = code.replace(magics[var], str(val))
    return code


def symbolic() -> None:
    for path in sorted((ROOT / "corpus/k/symbolic").glob("*.jsonl")):
        rec = json.loads(path.read_text())
        src_file = ROOT / rec["source"]["file"]
        for lf in rec["leaves"]:
            check(lf["witness_validated"], f"{path.stem} node {lf['node']}: stored witness_validated")
            code = _subst_magics(src_file.read_text(), lf["witness"])
            with tempfile.TemporaryDirectory() as td:
                tmp = Path(td) / src_file.name
                tmp.write_text(code)
                g: dict = {}
                exec(compile(code, str(tmp), "exec"), g)
                lines = [e["line"] for e in tracelib.cpython_events(str(tmp))
                         if e["event"] == "line"]
            leaf_lines = [e["line"] for e in lf["trace"]]
            check(lines == leaf_lines,
                  f"{path.stem} node {lf['node']}: witness line path {lf['witness']}")
            expected = lf["value"]
            if isinstance(expected, str) and re.fullmatch(r"[xabc0-9+\-*/% ()]+", expected):
                # a symbolic arithmetic term over the args: evaluate under the witness
                expected = eval(expected, {}, dict(lf["witness"]))
            check(g["result"] == expected,
                  f"{path.stem} node {lf['node']}: witness result {g['result']!r}")
        if path.stem.startswith("b2"):
            check(len(rec["pruned_infeasible"]) == 3,
                  "b2: three infeasible paths documented")


def verification() -> None:
    expect = {"c1_range_loop": "proved", "c2_abs_val": "proved",
              "c3_buggy_abs": "refuted",
              "c4_kb_assign": "proved", "c5_kb_swap": "proved",
              "c6_kb_chain": "proved", "c7_kb_double_half": "proved",
              "c8_kb_arith_mix": "proved", "c9_kb_abs": "proved",
              "c10_kb_max": "proved", "c11_kb_min": "proved",
              "c12_kb_countdown": "proved", "c13_kb_countup": "proved",
              "c14_kb_sum": "proved", "c15_kb_add_loop": "proved",
              "c16_kb_sub_loop": "proved", "c17_kb_max3": "proved",
              "c18_kb_clamp": "proved", "c19_kb_abs_times": "proved",
              "c20_kb_sumdiff": "proved", "c21_kb_mult_loop": "proved",
              "c22_kb_triangle_down": "proved", "c23_kb_sum_up": "proved",
              "c24_kb_count_even": "proved", "c25_kb_loop_max": "proved",
              "c26_kb_pure_nested": "proved", "c27_kb_mult_nested": "proved",
              "c28_kb_triangle_nested": "proved",
              "c29_kb_squares_cubic": "proved",
              "c30_kb_rows_sum_nested": "proved",
              "c31_kb_nested_with_branch": "proved",
              "c32_kb_pipeline": "proved", "c33_kb_stats_pipeline": "proved",
              "c34_kb_normalize_count": "proved"}
    committed = {p.stem for p in (ROOT / "corpus/k/verification").glob("*.jsonl")}
    check(committed == set(expect),
          f"verification records match the expectation table ({len(expect)})")
    for stem, want in expect.items():
        rec = json.loads((ROOT / "corpus/k/verification" / f"{stem}.jsonl").read_text())
        check(rec["result"] == want, f"{stem}: result == {want}")
        if rec.get("concrete_witness"):
            # module-level ported case: re-run the program at its magic literals
            # and compare every final binding against the stored witness
            g: dict = {}
            src = (ROOT / rec["source"]["file"]).read_text()
            exec(compile(src, rec["source"]["file"], "exec"), g)
            finals = {k: v for k, v in g.items()
                      if not k.startswith("__") and isinstance(v, (int, bool))}
            check(finals == rec["concrete_witness"]["finals"],
                  f"{stem}: concrete witness finals re-run in CPython")
        if want == "refuted":
            ce = rec["counterexample"]
            g: dict = {}
            exec(compile(ce["failing_trace"]["code"], "ce.py", "exec"), g)
            r, x = g["result"], ce["model"]["x"]
            violated = not (isinstance(r, int) and r >= 0 and (r == x or r == -x))
            check(violated, f"{stem}: counterexample x={x} violates the ensures in CPython")


def main() -> int:
    frontend_identity()
    concrete()
    symbolic()
    verification()
    print(f"\n{'ALL CHECKS PASS' if not FAILURES else f'{len(FAILURES)} FAILURES'}")
    return 1 if FAILURES else 0


if __name__ == "__main__":
    sys.exit(main())
