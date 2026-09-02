#!/usr/bin/env python3
"""run_proofs — generate the C-family (verification-trace) samples.

Per case: kompile the case's verification module (haskell backend, cached),
run kprove under a memory cap + watchdog, and package the outcome:

  C1 range-loop  (vendored klever proof) : loop-invariant circularity + entry
                                           claim -> expect #Top
  C2 abs-val     (this repo's spec)      : branching functional spec -> #Top
  C3 buggy-abs   (this repo's spec)      : same spec, buggy program -> expect
                                           REFUTED; the stuck claim state's
                                           path condition yields the
                                           counterexample, which is replayed
                                           concretely into a failing trace.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts"))

import kastjson  # noqa: E402
import tracelib  # noqa: E402
from py2mpy_traced import to_mpy  # noqa: E402

KOMPILE_T = 600
KPROVE_T = 900

# KleverBench upstream pin (provenance for the kb-* cases; problems are ported —
# translated IMP -> MiniPy + respecced over MPY — not vendored).
KLEVERBENCH = {
    "repo": "https://github.com/nlp-research-rosu/KleverBench",
    "sha": "b5eced33b16d13b28b9998f05e7b7e945f2fb482",
}


def kb_case(num: int, problem: str, spec: dict, source_code: str, args: dict,
            note: str, program_imp: str, invariants: list | None = None) -> dict:
    """A ported-KleverBench case: module-level program, full-characterization claim."""
    stem = problem.replace("-", "_")
    return {
        "id": f"c{num}_kb_{stem}",
        "dir": ROOT / f"specs/kb-{problem}",
        "module": f"KB-{problem.upper()}",
        "expect": "proved",
        "entry": None,  # module-level program: no entry function
        "program": f"programs/kb_{stem}.py",
        "source_code": source_code,
        "args": args,
        "spec": {**spec, "invariants": invariants or []},
        "note": note,
        "upstream": {**KLEVERBENCH, "problem": f"problems/imp/{problem}",
                     "program_imp": program_imp},
    }


CASES = [
    {
        "id": "c1_range_loop",
        "dir": ROOT / "vendor/klever/tests/verification/range-loop",
        "module": "RANGE-LOOP",
        "expect": "proved",
        "entry": "f",
        "source_code": (
            "def f(n):\n    total = 0\n    i = 0\n    for i in range(n):\n"
            "        total += i\n    return total\n\nresult = f(n)\n"
        ),
        "spec": {
            "requires": "n >= 0",
            "ensures": "result == n * (n - 1) // 2",
            "invariants": [{
                "loc": "for-loop over range(n)",
                "formula": "0 <= i <= n and, when the loop finishes, "
                           "total' == total + (n*(n-1) - i*(i-1)) // 2",
                "role": "circularity claim — kprove uses it as the induction "
                        "hypothesis for the unbounded symbolic loop",
            }],
        },
        "note": "Re-run of the klever reference proof (vendored verbatim); "
                "proves the Gauss closed form for a SYMBOLIC bound n over the "
                "whole reference semantics.",
    },
    {
        "id": "c2_abs_val",
        "dir": ROOT / "specs/abs-val",
        "module": "ABS-VAL",
        "expect": "proved",
        "entry": "abs_val",
        "source_code": (
            "def abs_val(x):\n    if x < 0:\n        return -x\n    return x\n"
            "\nresult = abs_val(x)\n"
        ),
        "spec": {
            "requires": "True (any int x)",
            "ensures": "result >= 0 and (result == x or result == -x)",
            "invariants": [],
        },
        "note": "Branching functional-correctness proof, all paths.",
    },
    {
        "id": "c3_buggy_abs",
        "dir": ROOT / "specs/buggy-abs",
        "module": "BUGGY-ABS",
        "expect": "refuted",
        "entry": "buggy_abs",
        "program": "programs/buggy_abs.py",
        "source_code": (
            "def buggy_abs(x):\n    if x < 0:\n        return -x\n"
            "    elif x > 0:\n        return x\n\nresult = buggy_abs(x)\n"
        ),
        "spec": {
            "requires": "True (any int x)",
            "ensures": "result >= 0 and (result == x or result == -x)",
            "invariants": [],
        },
        "note": "Same spec as c2 over the buggy implementation (missing x == 0 "
                "case falls through to None). The prover must NOT prove it.",
    },
    # ---- ported KleverBench problems (see programs/PROVENANCE.md) ----------
    kb_case(4, "assign",
            spec={"requires": "True (any int a)",
                  "ensures": "b == a + 4 and a unchanged"},
            source_code="b = a + 4\n",
            args={"a": "symbolic int (pre-bound)"},
            note="Straight-line full characterization: the final scope pins "
                 "both bindings exactly (a unchanged, b = a + 4).",
            program_imp="b = a + 4 ;"),
    kb_case(5, "swap",
            spec={"requires": "True (any ints a, b)",
                  "ensures": "a == B, b == A, r == A (swap via temporary r)"},
            source_code="r = a\na = b\nb = r\n",
            args={"a": "symbolic int (pre-bound)", "b": "symbolic int (pre-bound)"},
            note="Three-assignment dataflow; finals are closed forms written "
                 "directly in the scope RHS (no existentials). Initial r is dead "
                 "in the IMP source and dropped.",
            program_imp="r = a ; a = b ; b = r ;"),
    kb_case(6, "chain",
            spec={"requires": "True (any int a)",
                  "ensures": "x == a + 1, y == (a + 1) * 2, "
                             "z == (a + 1) * 2 - a; a unchanged"},
            source_code="x = a + 1\ny = x * 2\nz = y - a\n",
            args={"a": "symbolic int (pre-bound)"},
            note="Three-step dataflow chain; all three computed finals pinned as "
                 "direct closed forms of the symbolic input.",
            program_imp="x = a + 1 ; y = x * 2 ; z = y - a ;"),
    kb_case(7, "double-half",
            spec={"requires": "True (any int a)",
                  "ensures": "r == a (doubling then floor-halving is exact); "
                             "a unchanged"},
            source_code="r = a + a\nr = r // 2\n",
            args={"a": "symbolic int (pre-bound)"},
            note="IMP `/` becomes `//`; a + a is always even, so the division is "
                 "exact and z3 discharges the floor algebra with no lemma imports.",
            program_imp="r = a + a ; r = r / 2 ;"),
    kb_case(8, "arith-mix",
            spec={"requires": "True (any ints a, b)",
                  "ensures": "res == a*b + a - b; a and b unchanged"},
            source_code="res = a * b + a - b\n",
            args={"a": "symbolic int (pre-bound)", "b": "symbolic int (pre-bound)"},
            note="Nonlinear closed form (a*b over two symbolic ints) pinned "
                 "exactly; no arithmetic lemmas needed.",
            program_imp="res = a * b + a - b ;"),
    kb_case(9, "abs",
            spec={"requires": "True (any int a)",
                  "ensures": "res == absInt(a); a unchanged"},
            source_code="if a < 0:\n    res = 0 - a\nelse:\n    res = a\n",
            args={"a": "symbolic int (pre-bound)"},
            note="Branching functional spec via the absInt hook, both paths; the "
                 "IMP shape (if/else assignment, `0 - a`) is kept verbatim, "
                 "unlike the early-return abs_val of c2.",
            program_imp="if (a < 0) { res = 0 - a ; } else { res = a ; }"),
    kb_case(10, "max",
            spec={"requires": "True (any ints a, b)",
                  "ensures": "max == maxInt(a, b); a and b unchanged"},
            source_code="if a <= b:\n    max = b\nelse:\n    max = a\n",
            args={"a": "symbolic int (pre-bound)", "b": "symbolic int (pre-bound)"},
            note="Branching spec via the maxInt hook over two symbolic ints; the "
                 "module-level binding keeps the IMP variable name `max`.",
            program_imp="if (a <= b) { max = b ; } else { max = a ; }"),
    kb_case(11, "min",
            spec={"requires": "True (any ints a, b)",
                  "ensures": "res == minInt(a, b); a and b unchanged"},
            source_code="if a <= b:\n    res = a\nelse:\n    res = b\n",
            args={"a": "symbolic int (pre-bound)", "b": "symbolic int (pre-bound)"},
            note="Branching spec via the minInt hook, dual of c10.",
            program_imp="if (a <= b) { res = a ; } else { res = b ; }"),
    kb_case(12, "countdown",
            spec={"requires": "n >= 0",
                  "ensures": "n == 0 (the loop drains n exactly to zero)"},
            source_code="while 0 < n:\n    n = n - 1\n",
            args={"n": "symbolic int (pre-bound)"},
            note="First ported while-loop proof: a circularity claim anchored on "
                 "the mid-execution #while redex (n = I >= 0 at the loop head "
                 "ends at exactly 0) plus the entry claim, the same two-claim "
                 "shape as the vendored range-loop proof. Guard `!(n <= 0)` is "
                 "written idiomatically as `0 < n`, `n + -1` as `n - 1`.",
            program_imp="while (!(n <= 0)) { n = n + -1 ; }",
            invariants=[{
                "loc": "while-loop head (#while circularity claim)",
                "formula": "n = I with I >= 0; the remaining iterations end "
                           "with n == 0",
                "role": "circularity claim — the back edge re-enters it at "
                        "I - 1 (guard 0 < I keeps I - 1 >= 0); on exit "
                        "I <= 0 and I >= 0 force I == 0",
            }]),
    kb_case(13, "countup",
            spec={"requires": "True (any ints n, r)",
                  "ensures": "r == maxInt(n, r0) for initial r0 (climb to n, "
                             "no-op when r0 >= n); n unchanged"},
            source_code="while r < n:\n    r = r + 1\n",
            args={"n": "symbolic int (pre-bound)", "r": "symbolic int (pre-bound)"},
            note="While-loop proof with NO precondition: the invariant's closed "
                 "form maxInt(n, r) covers both the climbing and the no-op case; "
                 "z3 discharges maxInt(N, I+1) == maxInt(N, I) under I < N on "
                 "the back edge. Guard `!(n <= r)` written as `r < n`.",
            program_imp="while (!(n <= r)) { r = r + 1 ; }",
            invariants=[{
                "loc": "while-loop head (#while circularity claim)",
                "formula": "n = N unchanged, r = I arbitrary; the remaining "
                           "iterations end with r == maxInt(N, I)",
                "role": "circularity claim — back edge re-establishes the "
                        "closed form at I + 1; exit branch has N <= I, where "
                        "maxInt(N, I) == I",
            }]),
    kb_case(14, "sum",
            spec={"requires": "n >= 0",
                  "ensures": "n == 0 and sum == sum0 + n*(n+1)/2 (the "
                             "triangular sum added into an arbitrary initial "
                             "sum0)"},
            source_code="while 0 < n:\n    sum = sum + n\n    n = n - 1\n",
            args={"n": "symbolic int (pre-bound)",
                  "sum": "symbolic int (pre-bound)"},
            note="The Gauss benchmark: the circularity's closed form carries "
                 "the division by 2 (z3 discharges the floored /Int algebra, "
                 "as in the vendored range-loop proof); requires is exactly "
                 "the intent's n >= 0, sum fully arbitrary.",
            program_imp="while (!(n <= 0)) { sum = sum + n ; n = n + -1 ; }",
            invariants=[{
                "loc": "while-loop head (#while circularity claim)",
                "formula": "n = I >= 0, sum = J; the remaining iterations end "
                           "with n == 0 and sum == J + I*(I+1)/2",
                "role": "circularity claim — closed form of the remaining "
                        "triangular sum; the back edge re-establishes it at "
                        "I - 1 with J + I accumulated",
            }]),
    kb_case(15, "add-loop",
            spec={"requires": "True (any ints n, res, a)",
                  "ensures": "n == minInt(n, 0), res == res0 + a * maxInt(n, 0) "
                             "(adds a exactly max(n,0) times); a unchanged"},
            source_code="while 0 < n:\n    res = res + a\n    n = n - 1\n",
            args={"n": "symbolic int (pre-bound)", "res": "symbolic int (pre-bound)",
                  "a": "symbolic int (pre-bound)"},
            note="Repeated addition with NO precondition: the piecewise "
                 "minInt/maxInt closed form covers the no-op branch; z3 "
                 "discharges the nonlinear a*maxInt back-edge algebra unaided.",
            program_imp="while (0 < n) { res = res + a ; n = n - 1 ; }",
            invariants=[{
                "loc": "while-loop head (#while circularity claim)",
                "formula": "from n = I, res = S (a = A unchanged): the loop "
                           "ends with n == minInt(I, 0), res == S + A*maxInt(I, 0)",
                "role": "circularity claim, no requires — the closed form is "
                        "total over all I",
            }]),
    kb_case(16, "sub-loop",
            spec={"requires": "True (any ints a, b)",
                  "ensures": "a == a0 - maxInt(b, 0), b == minInt(b, 0)"},
            source_code="while 0 < b:\n    a = a - 1\n    b = b - 1\n",
            args={"a": "symbolic int (pre-bound)", "b": "symbolic int (pre-bound)"},
            note="Lockstep decrement, no precondition; direct analogue of "
                 "c15's piecewise closed form.",
            program_imp="while (0 < b) { a = a - 1 ; b = b - 1 ; }",
            invariants=[{
                "loc": "while-loop head (#while circularity claim)",
                "formula": "from a = A2, b = I: the loop ends with "
                           "a == A2 - maxInt(I, 0), b == minInt(I, 0)",
                "role": "circularity claim, total over all I",
            }]),
    kb_case(17, "max3",
            spec={"requires": "True (any ints a, b, n)",
                  "ensures": "max == maxInt(maxInt(a, b), n); a, b, n unchanged"},
            source_code="max = a\nif max <= b:\n    max = b\nif max <= n:\n"
                        "    max = n\n",
            args={"a": "symbolic int (pre-bound)", "b": "symbolic int (pre-bound)",
                  "n": "symbolic int (pre-bound)"},
            note="Two sequential branches; the prover's 4-way case split "
                 "collapses into the nested maxInt closed form.",
            program_imp="max = a ; if (max <= b) { max = b ; } else { } "
                        "if (max <= n) { max = n ; } else { }"),
    kb_case(18, "clamp",
            spec={"requires": "True (any int a)",
                  "ensures": "res == minInt(maxInt(a, 0), 10) (a clamped to "
                             "[0, 10]); a unchanged"},
            source_code="if a < 0:\n    res = 0\nelse:\n    if 10 < a:\n"
                        "        res = 10\n    else:\n        res = a\n",
            args={"a": "symbolic int (pre-bound)"},
            note="Nested branches; the three-way split collapses into the "
                 "composed minInt/maxInt clamp form.",
            program_imp="if (a < 0) { res = 0 ; } else { if (10 < a) "
                        "{ res = 10 ; } else { res = a ; } }"),
    kb_case(19, "abs-times",
            spec={"requires": "True (any ints a, b)",
                  "ensures": "t == absInt(a) and res == absInt(a) * b; "
                             "a, b unchanged"},
            source_code="if a < 0:\n    t = 0 - a\nelse:\n    t = a\n"
                        "res = t * b\n",
            args={"a": "symbolic int (pre-bound)", "b": "symbolic int (pre-bound)"},
            note="Branch feeding a nonlinear multiply: both the intermediate "
                 "t and the product res are pinned exactly (absInt hook).",
            program_imp="if (a < 0) { t = 0 - a ; } else { t = a ; } "
                        "res = t * b ;"),
    kb_case(20, "sumdiff",
            spec={"requires": "True (any ints a, b)",
                  "ensures": "t == 0 and res == 2 * absInt(a - b)"},
            source_code="if a < b:\n    t = b - a\nelse:\n    t = a - b\n"
                        "res = 0\nwhile 0 < t:\n    res = res + 2\n"
                        "    t = t - 1\n",
            args={"a": "symbolic int (pre-bound)", "b": "symbolic int (pre-bound)"},
            note="Multi-stage: a branch computes |a - b|, a loop consumes it. "
                 "The entry claim splits on the branch, each side feeding the "
                 "loop circularity whose minInt/maxInt closed form collapses "
                 "to res == 2*|a - b| since |a - b| >= 0.",
            program_imp="if (a < b) { t = b - a ; } else { t = a - b ; } "
                        "res = 0 ; while (0 < t) { res = res + 2 ; "
                        "t = t - 1 ; }",
            invariants=[{
                "loc": "while-loop head (#while circularity claim)",
                "formula": "from t = T, res = R (a, b unchanged): the loop "
                           "ends with t == minInt(T, 0), res == R + 2*maxInt(T, 0)",
                "role": "circularity claim, total over all T (no-op branch "
                        "covered by the piecewise form)",
            }]),
    kb_case(21, "mult-loop",
            spec={"requires": "True (any ints n, a)",
                  "ensures": "res == a * maxInt(n, 0) (multiplication as "
                             "repeated addition), n == minInt(n, 0); a unchanged"},
            source_code="res = 0\nwhile 0 < n:\n    res = res + a\n"
                        "    n = n - 1\n",
            args={"n": "symbolic int (pre-bound)", "a": "symbolic int (pre-bound)"},
            note="Same loop as c15 with res seeded to 0 by the program "
                 "itself, so the final res is the pure product a*maxInt(n, 0).",
            program_imp="res = 0 ; while (0 < n) { res = res + a ; "
                        "n = n - 1 ; }",
            invariants=[{
                "loc": "while-loop head (#while circularity claim)",
                "formula": "from n = I, res = S (a = A unchanged): the loop "
                           "ends with n == minInt(I, 0), res == S + A*maxInt(I, 0)",
                "role": "circularity claim, total over all I",
            }]),
    kb_case(22, "triangle-down",
            spec={"requires": "True (any int n)",
                  "ensures": "sum == maxInt(n, 0)*(maxInt(n, 0)+1)/2 (the "
                             "triangle number of max(n,0); no-op for n <= 0), "
                             "n == minInt(n, 0)"},
            source_code="sum = 0\nwhile 0 < n:\n    sum = sum + n\n"
                        "    n = n - 1\n",
            args={"n": "symbolic int (pre-bound)"},
            note="c14's Gauss form with NO precondition: the piecewise "
                 "maxInt/minInt closed form absorbs the no-op branch, and z3 "
                 "still discharges the nonlinear /Int 2 triangle algebra "
                 "unaided. The dead initial sum binding of the IMP source is "
                 "dropped (the program seeds sum = 0 itself).",
            program_imp="sum = 0 ; while (0 < n) { sum = sum + n ; "
                        "n = n - 1 ; }",
            invariants=[{
                "loc": "while-loop head (#while circularity claim)",
                "formula": "from n = I, sum = S: the loop ends with "
                           "n == minInt(I, 0), sum == S + "
                           "maxInt(I, 0)*(maxInt(I, 0)+1)/2",
                "role": "circularity claim, total over all I",
            }]),
    kb_case(23, "sum-up",
            spec={"requires": "n >= 0",
                  "ensures": "sum == n*(n+1)/2 and i == n + 1; n unchanged"},
            source_code="sum = 0\ni = 1\nwhile i <= n:\n    sum = sum + i\n"
                        "    i = i + 1\n",
            args={"n": "symbolic int (pre-bound)"},
            note="Upward Gauss sum: the circularity carries the "
                 "single-division closed form (n*(n+1) - i*(i-1))/2 from the "
                 "vendored range-loop proof, which keeps the back-edge "
                 "algebra a plain div fact for z3.",
            program_imp="sum = 0 ; i = 1 ; while (i <= n) "
                        "{ sum = sum + i ; i = i + 1 ; }",
            invariants=[{
                "loc": "while-loop head (#while circularity claim)",
                "formula": "1 <= i == I <= n + 1, sum = S; the loop ends "
                           "with i == n + 1 and sum == S + "
                           "(n*(n+1) - I*(I-1))/2",
                "role": "circularity claim — closed form of the remaining "
                        "ascending sum I + (I+1) + ... + n",
            }]),
    kb_case(24, "count-even",
            spec={"requires": "n >= 0",
                  "ensures": "count == (n+1)/2 (the evens among 0..n-1) and "
                             "i == n; n unchanged"},
            source_code="count = 0\ni = 0\nwhile i < n:\n"
                        "    if i % 2 == 0:\n        count = count + 1\n"
                        "    i = i + 1\n",
            args={"n": "symbolic int (pre-bound)"},
            note="Conditional accumulator with parity: the invariant counts "
                 "the remaining evens as (n+1)/2 - (i+1)/2; the program's "
                 "i % 2 guard expands to pyMod atoms with literal modulus, "
                 "decided by z3 with no lemma imports.",
            program_imp="count = 0 ; i = 0 ; while (i < n) { if (i % 2 == 0) "
                        "{ count = count + 1 ; } else { } i = i + 1 ; }",
            invariants=[{
                "loc": "while-loop head (#while circularity claim)",
                "formula": "0 <= i == I <= n, count = C; the loop ends with "
                           "i == n and count == C + (n+1)/2 - (I+1)/2",
                "role": "circularity claim — closed form of the count of "
                        "evens in I..n-1",
            }]),
    kb_case(25, "loop-max",
            spec={"requires": "n >= 1",
                  "ensures": "max == maxInt(a, n-1) (fold of max over "
                             "0..n-1 seeded with a) and i == n; a, n unchanged"},
            source_code="max = a\ni = 0\nwhile i < n:\n    if max < i:\n"
                        "        max = i\n    i = i + 1\n",
            args={"a": "symbolic int (pre-bound)", "n": "symbolic int (pre-bound)"},
            note="Running maximum with a branch in the body: the circularity "
                 "holds for i <= n-1 (guard true); the back edge landing on "
                 "i == n is discharged by one extra unfold that exits, so a "
                 "single circularity suffices. requires is the intent's n >= 1.",
            program_imp="max = a ; i = 0 ; while (i < n) { if (max < i) "
                        "{ max = i ; } else { } i = i + 1 ; }",
            invariants=[{
                "loc": "while-loop head (#while circularity claim)",
                "formula": "i == I <= n-1, max = M; the loop ends with "
                           "i == n and max == maxInt(M, n-1)",
                "role": "circularity claim — folding max over the nonempty "
                        "range I..n-1 yields maxInt(M, n-1)",
            }]),
    kb_case(26, "pure-nested",
            spec={"requires": "a >= 1",
                  "ensures": "i == 0 and j == minInt(b, 0); a, b unchanged"},
            source_code="i = a\nwhile 0 < i:\n    j = b\n    while 0 < j:\n"
                        "        j = j - 1\n    i = i - 1\n",
            args={"a": "symbolic int (pre-bound)", "b": "symbolic int (pre-bound)"},
            note="First nested-loop port: one circularity per loop level, the "
                 "inner claim first and total (no requires — it must cover "
                 "every state each outer iteration creates), the outer under "
                 "i >= 1. The first outer iteration (j still unbound) unfolds "
                 "in the entry claim before the outer circularity anchors. "
                 "Magic literals downsized to 137/138 so the concrete run "
                 "stays instant.",
            program_imp="i = a ; while (0 < i) { j = b ; while (0 < j) "
                        "{ j = j - 1 ; } i = i - 1 ; }",
            invariants=[
                {"loc": "inner #while circularity",
                 "formula": "j = J drains to minInt(J, 0); a, b, i unchanged",
                 "role": "total inner-loop summary the prover applies each "
                         "time it walks the outer body"},
                {"loc": "outer #while circularity",
                 "formula": "i = I >= 1 drains to 0, j ends at minInt(b, 0)",
                 "role": "outer circularity; back edge at I - 1 >= 1, the "
                         "I - 1 == 0 boundary discharged by one extra unfold"},
            ]),
    kb_case(27, "mult-nested",
            spec={"requires": "a >= 1",
                  "ensures": "res == a * maxInt(b, 0) (multiplication as "
                             "nested repeated increment), i == 0, "
                             "j == minInt(b, 0)"},
            source_code="res = 0\ni = a\nwhile 0 < i:\n    j = b\n"
                        "    while 0 < j:\n        res = res + 1\n"
                        "        j = j - 1\n    i = i - 1\n",
            args={"a": "symbolic int (pre-bound)", "b": "symbolic int (pre-bound)"},
            note="Nested multiplication: the inner claim adds maxInt(j, 0) "
                 "to res, the outer's nonlinear back edge "
                 "res + max(b,0) + (i-1)*max(b,0) == res + i*max(b,0) is "
                 "discharged by z3 unaided. Magic literals 137/138.",
            program_imp="res = 0 ; i = a ; while (0 < i) { j = b ; "
                        "while (0 < j) { res = res + 1 ; j = j - 1 ; } "
                        "i = i - 1 ; }",
            invariants=[
                {"loc": "inner #while circularity",
                 "formula": "j => minInt(j, 0), res += maxInt(j, 0); "
                            "a, b, i unchanged",
                 "role": "total inner-loop summary (no-op side included)"},
                {"loc": "outer #while circularity",
                 "formula": "i = I >= 1 => 0, res += I * maxInt(b, 0), "
                            "j => minInt(b, 0)",
                 "role": "outer circularity with the nonlinear product "
                         "closed form"},
            ]),
    kb_case(28, "triangle-nested",
            spec={"requires": "n >= 1",
                  "ensures": "count == n*(n+1)/2 (the triangle number, "
                             "counted one inner iteration at a time), "
                             "i == 0, j == 0"},
            source_code="count = 0\ni = n\nwhile 0 < i:\n    j = i\n"
                        "    while 0 < j:\n        count = count + 1\n"
                        "        j = j - 1\n    i = i - 1\n",
            args={"n": "symbolic int (pre-bound)"},
            note="The Gauss form again, now as a doubly nested count: the "
                 "outer circularity carries the single-division shape "
                 "(i*(i+1))/2 from c23. Magic literal 137 (31337 would mean "
                 "~491M inner iterations concretely).",
            program_imp="count = 0 ; i = n ; while (0 < i) { j = i ; "
                        "while (0 < j) { count = count + 1 ; j = j - 1 ; } "
                        "i = i - 1 ; }",
            invariants=[
                {"loc": "inner #while circularity",
                 "formula": "j => minInt(j, 0), count += maxInt(j, 0); "
                            "n, i unchanged",
                 "role": "total inner-loop summary"},
                {"loc": "outer #while circularity",
                 "formula": "i = I >= 1 => 0, j => 0, count += (I*(I+1))/2",
                 "role": "outer circularity, triangle closed form"},
            ]),
    kb_case(29, "squares-cubic",
            spec={"requires": "n >= 1",
                  "ensures": "res == n*(n+1)*(2n+1)/6 (the sum of squares "
                             "1² + ... + n²), i == 0, j == 0"},
            source_code="res = 0\ni = n\nwhile 0 < i:\n    j = i\n"
                        "    while 0 < j:\n        res = res + i\n"
                        "        j = j - 1\n    i = i - 1\n",
            args={"n": "symbolic int (pre-bound)"},
            note="Sum of squares via i added i times: the outer circularity "
                 "carries the cubic closed form as one whole-numerator "
                 "division by 6, and z3 discharges the per-step delta "
                 "i*(i+1)*(2i+1)/6 - (i-1)*i*(2i-1)/6 == i² unaided. Magic "
                 "literal 137.",
            program_imp="res = 0 ; i = n ; while (0 < i) { j = i ; "
                        "while (0 < j) { res = res + i ; j = j - 1 ; } "
                        "i = i - 1 ; }",
            invariants=[
                {"loc": "inner #while circularity",
                 "formula": "j => minInt(j, 0), res += i * maxInt(j, 0); "
                            "n, i unchanged",
                 "role": "total inner-loop summary (adds i per iteration)"},
                {"loc": "outer #while circularity",
                 "formula": "i = I >= 1 => 0, j => 0, "
                            "res += (I*(I+1)*(2I+1))/6",
                 "role": "outer circularity, sum-of-squares closed form"},
            ]),
    kb_case(30, "rows-sum-nested",
            spec={"requires": "a >= 1",
                  "ensures": "2*sum == a * maxInt(b,0)*(maxInt(b,0)+1) "
                             "(a rows, each summing b..1), i == 0, "
                             "j == minInt(b, 0)"},
            source_code="sum = 0\ni = a\nwhile 0 < i:\n    j = b\n"
                        "    while 0 < j:\n        sum = sum + j\n"
                        "        j = j - 1\n    i = i - 1\n",
            args={"a": "symbolic int (pre-bound)", "b": "symbolic int (pre-bound)"},
            note="Row sums: the ensures is stated in the division-free form "
                 "2*sum == a*max(b,0)*(max(b,0)+1) (which pins sum exactly), "
                 "and the outer loop needs TWO circularities — one for the "
                 "b >= 1 side and one for the empty-row b <= 0 side — since "
                 "a single piecewise form left z3 in a nonlinear div context.",
            program_imp="sum = 0 ; i = a ; while (0 < i) { j = b ; "
                        "while (0 < j) { sum = sum + j ; j = j - 1 ; } "
                        "i = i - 1 ; }",
            invariants=[
                {"loc": "inner #while circularity",
                 "formula": "j = J >= 1 => 0, 2*sum += J*(J+1); a, b, i "
                            "unchanged",
                 "role": "inner row-sum summary, guard-true side"},
                {"loc": "outer #while circularity (b >= 1 side)",
                 "formula": "i = I >= 1 => 0, j => 0, 2*sum += I*b*(b+1)",
                 "role": "outer circularity where rows are nonempty"},
                {"loc": "outer #while circularity (b <= 0 side)",
                 "formula": "i = I >= 1 => 0, j => b, sum unchanged",
                 "role": "outer circularity where every row is empty"},
            ]),
    kb_case(31, "nested-with-branch",
            spec={"requires": "a >= 1 and b >= 1",
                  "ensures": "res == m*(m+1)/2 for m = minInt(a, b) (only "
                             "rows i <= b are admitted), i == 0, j == 0"},
            source_code="res = 0\ni = a\nwhile 0 < i:\n    if i <= b:\n"
                        "        j = i\n        while 0 < j:\n"
                        "            res = res + 1\n            j = j - 1\n"
                        "    i = i - 1\n",
            args={"a": "symbolic int (pre-bound)", "b": "symbolic int (pre-bound)"},
            note="The hardest port: a branch guards the inner loop, so the "
                 "outer circularity splits into admitted (i <= b) and "
                 "skipped (b < i) regions, each in j-unbound and j-bound "
                 "variants (four outer claims + the inner one). Its "
                 "verification module adds two documented proof-only minInt "
                 "simplification rules firing on the non-strict <= atoms the "
                 "path actually carries (the stock equations require strict "
                 "comparisons, and deciding those pushed z3 into an unknown).",
            program_imp="res = 0 ; i = a ; while (0 < i) { if (i <= b) "
                        "{ j = i ; while (0 < j) { res = res + 1 ; "
                        "j = j - 1 ; } } else { } i = i - 1 ; }",
            invariants=[
                {"loc": "inner #while circularity",
                 "formula": "j = J >= 1 => 0, res += J",
                 "role": "guard-true inner summary (c25 style)"},
                {"loc": "outer #while circularities (admitted region, "
                        "j-unbound and j-bound)",
                 "formula": "i = I >= 1, I <= b: i => 0, j => 0, "
                            "res += (I*(I+1))/2",
                 "role": "the region where every remaining row fires"},
                {"loc": "outer #while circularities (skipped region, "
                        "j-unbound and j-bound)",
                 "formula": "i = I, b < I, b >= 1: i => 0, j => 0, "
                            "res += (b*(b+1))/2",
                 "role": "rows above b are skipped until i reaches b"},
            ]),
    kb_case(32, "pipeline",
            spec={"requires": "n >= 0",
                  "ensures": "t == absInt(a*b), i == n, and "
                             "res == absInt(a*b) * n + a"},
            source_code="t = a * b\nif t < 0:\n    t = 0 - t\nres = 0\n"
                        "i = 0\nwhile i < n:\n    res = res + t\n"
                        "    i = i + 1\nres = res + a\n",
            args={"a": "symbolic int (pre-bound)", "b": "symbolic int (pre-bound)",
                  "n": "symbolic int (pre-bound)"},
            note="Tier-5 pipeline: branch computes t = |a*b|, a loop "
                 "accumulates it n times, a final adjustment adds a — the "
                 "branch and epilogue stages are consumed by the entry "
                 "claim's symbolic execution around one loop circularity, "
                 "with the intermediate t carried symbolically end to end.",
            program_imp="t = a * b ; if (t < 0) { t = 0 - t ; } else { } "
                        "res = 0 ; i = 0 ; while (i < n) { res = res + t ; "
                        "i = i + 1 ; } res = res + a ;",
            invariants=[{
                "loc": "while-loop head (#while circularity claim)",
                "formula": "i = I <= n, res = R; the loop ends with i == n "
                           "and res == R + t*(n - I) (t frozen)",
                "role": "circularity claim; z3 discharges the nonlinear "
                        "t*(n-I) distributivity on the back edge",
            }]),
    kb_case(33, "stats-pipeline",
            spec={"requires": "n >= 0",
                  "ensures": "m == minInt(a,b), x == maxInt(a,b), t == x - m "
                             "(the range), i == n, and res == "
                             "(maxInt(a,b) - minInt(a,b)) * n + minInt(a,b)"},
            source_code="if a <= b:\n    m = a\n    x = b\nelse:\n    m = b\n"
                        "    x = a\nt = x - m\nres = 0\ni = 0\n"
                        "while i < n:\n    res = res + t\n    i = i + 1\n"
                        "res = res + m\n",
            args={"a": "symbolic int (pre-bound)", "b": "symbolic int (pre-bound)",
                  "n": "symbolic int (pre-bound)"},
            note="Five intermediates carried symbolically across three "
                 "stages: the min/max branch, the range t, the accumulation "
                 "loop, and the +m epilogue; all five finals pinned. One "
                 "circularity suffices (only one loop).",
            program_imp="if (a <= b) { m = a ; x = b ; } else { m = b ; "
                        "x = a ; } t = x - m ; res = 0 ; i = 0 ; "
                        "while (i < n) { res = res + t ; i = i + 1 ; } "
                        "res = res + m ;",
            invariants=[{
                "loc": "while-loop head (#while circularity claim)",
                "formula": "i = I <= n, res = R (m, x, t frozen); the loop "
                           "ends with i == n and res == R + t*(n - I)",
                "role": "circularity claim, total over the states both "
                        "branch stages create",
            }]),
    kb_case(34, "normalize-count",
            spec={"requires": "True (any ints a, b, n)",
                  "ensures": "n == 0, count == absInt(n0), and "
                             "res == absInt(n0) * a + b"},
            source_code="if n < 0:\n    n = 0 - n\ncount = 0\n"
                        "while 0 < n:\n    n = n - 1\n"
                        "    count = count + 1\nres = count * a + b\n",
            args={"a": "symbolic int (pre-bound)", "b": "symbolic int (pre-bound)",
                  "n": "symbolic int (pre-bound)"},
            note="No precondition: n is normalized to |n| by the branch, "
                 "drained by the loop (the total minInt/maxInt circularity "
                 "of c12 covers both), then res == |n|*a + b closes the "
                 "pipeline — the nonlinear count*a product resolves once "
                 "the circularity substitutes count == maxInt(±n, 0) under "
                 "each branch path.",
            program_imp="if (n < 0) { n = 0 - n ; } else { } count = 0 ; "
                        "while (0 < n) { n = n - 1 ; count = count + 1 ; } "
                        "res = count * a + b ;",
            invariants=[{
                "loc": "while-loop head (#while circularity claim)",
                "formula": "from n = N, count = C: the loop ends with "
                           "n == minInt(N, 0), count == C + maxInt(N, 0)",
                "role": "total circularity (covers the no-op side), c12/c15 "
                        "style",
            }]),
]


def sh(cmd: list[str], timeout: int) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 30)


def kompile_case(case) -> Path:
    out = ROOT / "build/k/verif" / case["dir"].name
    if (out / "timestamp").exists():
        return out
    p = sh(["timeout", str(KOMPILE_T), "kompile", str(case["dir"] / "verification.k"),
            "--backend", "haskell", "--main-module", f"{case['module']}-VERIFICATION",
            "--syntax-module", "MPY-SYNTAX", "--output-definition", str(out)], KOMPILE_T)
    assert p.returncode == 0, f"kompile failed: {p.stderr[-1500:]}"
    return out


def kprove_case(case, defn: Path) -> dict:
    t0 = time.time()
    p = sh(["systemd-run", "--user", "--scope", "-p", "MemoryMax=8G",
            "-p", "MemorySwapMax=0", "--quiet", "timeout", str(KPROVE_T),
            "kprove", str(case["dir"] / "spec.k"), "--definition", str(defn),
            "--spec-module", f"{case['module']}-SPEC"], KPROVE_T)
    wall = round(time.time() - t0, 1)
    proved = "#Top" in p.stdout
    return {"proved": proved, "wall_seconds": wall, "exit_code": p.returncode,
            "stdout": p.stdout, "stderr": p.stderr}


# --------------------------------------------------------------------------
# C3: counterexample from the stuck claim state
# --------------------------------------------------------------------------
def stuck_constraints(stdout: str) -> list[str]:
    """Collect `{ true/false #Equals X <op>Int <n> }` constraints on X."""
    pat = re.compile(r"\{\s*(true|false)\s*#Equals\s*X\s*(<Int|<=Int|>Int|>=Int|==Int)\s*\(?\s*(-?\d+)\s*\)?\s*\}")
    seen, out = set(), []
    for pol, op, num in pat.findall(stdout):
        key = (pol, op, num)
        if key in seen:
            continue
        seen.add(key)
        smt_op = {"<Int": "<", "<=Int": "<=", ">Int": ">", ">=Int": ">=", "==Int": "="}[op]
        atom = f"({smt_op} x {num})"
        out.append(atom if pol == "true" else f"(not {atom})")
    return out


def z3_model_x(constraints: list[str]) -> int:
    smt = "(declare-const x Int)" + "".join(f"(assert {c})" for c in constraints)
    smt += "(check-sat)(get-value (x))"
    p = subprocess.run(["timeout", "60", "z3", "-in"], input=smt,
                       capture_output=True, text=True)
    assert p.stdout.startswith("sat"), f"z3 says: {p.stdout!r} for {constraints}"
    m = re.search(r"\(x\s+\(?(-?)\s*(\d+)\)?\)", p.stdout)
    return int(m.group(1) + m.group(2))


def failing_trace(case, x_val: int) -> dict:
    """Replay the counterexample concretely through the traced build."""
    src = (ROOT / case["program"]).read_text().replace("31337", str(x_val))
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td) / "counterexample.py"
        tmp.write_text(src)
        ft = tracelib.FuncTable(str(tmp))
        mpy = Path(td) / "counterexample.mpy"
        mpy.write_text(to_mpy(str(tmp)))
        p = subprocess.run(["timeout", "120", "krun", "--definition",
                            str(ROOT / "build/k/traced"), str(mpy), "--output", "json"],
                           capture_output=True, text=True)
        term = json.loads(p.stdout)["term"]
        events = tracelib.assemble_k_events(kastjson.raw_events(term), ft,
                                            kastjson.exc_name(term))
        result = kastjson.module_result(term)
    # confirm in CPython too
    g: dict = {}
    exec(compile(src, "counterexample.py", "exec"), g)
    assert g["result"] == result, "replay divergence between K and CPython"
    return {"input": {"x": x_val}, "result": result, "code": src, "trace": events,
            "violates": case["spec"]["ensures"],
            "why": f"result is {result!r}, which fails `{case['spec']['ensures']}`"}


# --------------------------------------------------------------------------
def build_case(case) -> dict:
    defn = kompile_case(case)
    pr = kprove_case(case, defn)
    outcome = "proved" if pr["proved"] else "refuted"
    assert outcome == case["expect"], (
        f"{case['id']}: prover said {outcome}, expected {case['expect']}\n"
        f"stdout tail: {pr['stdout'][-800:]}\nstderr tail: {pr['stderr'][-800:]}")

    rec = {
        "id": f"verification/{case['dir'].name}",
        "kind": "proof_trace",
        "source": {"code": case["source_code"], "entry": case["entry"],
                   "args": case.get("args")
                           or {"n" if case["entry"] == "f" else "x": "symbolic int"}},
        "spec": {**case["spec"], "claim_k": (case["dir"] / "spec.k").read_text()},
        "result": outcome,
        "prover": {"tool": "kprove (K haskell backend + z3)",
                   "wall_seconds": pr["wall_seconds"],
                   "verdict_marker": "#Top" if pr["proved"] else "stuck claim state",
                   "memory_cap": "8G (systemd-run scope)"},
        "counterexample": None,
        "note": case["note"],
        "provenance": {"definition": f"build/k/verif/{case['dir'].name}",
                       "spec_module": f"{case['module']}-SPEC"},
    }
    if case.get("upstream"):
        rec["provenance"]["upstream"] = case["upstream"]
    if case["entry"] is None and case.get("program"):
        # module-level program: record the concrete run at the magic literals as
        # an independently re-checkable witness (validate.py re-execs and compares)
        rec["source"]["file"] = case["program"]
        g: dict = {}
        src = (ROOT / case["program"]).read_text()
        exec(compile(src, case["program"], "exec"), g)
        rec["concrete_witness"] = {
            "finals": {k: v for k, v in g.items()
                       if not k.startswith("__") and isinstance(v, (int, bool))}}
    if outcome == "refuted":
        cons = stuck_constraints(pr["stdout"])
        assert cons, "no X-constraints found in stuck state output"
        x_val = z3_model_x(cons)
        rec["counterexample"] = {
            "stuck_path_condition": cons,
            "model": {"x": x_val},
            "model_source": "z3 on the stuck claim state's path condition",
            "failing_trace": failing_trace(case, x_val),
        }
        # keep the interesting slice of the stuck state for the record
        m = re.search(r'"result" \|-> \S+', pr["stdout"])
        rec["prover"]["stuck_state_excerpt"] = m.group(0) if m else None
    return rec


def to_markdown(rec: dict) -> str:
    s = rec["spec"]
    lines = [f"# {rec['id']} — **{rec['result'].upper()}**", "",
             "```python", rec["source"]["code"].rstrip(), "```", "",
             f"- requires: `{s['requires']}`",
             f"- ensures: `{s['ensures']}`"]
    for inv in s["invariants"]:
        lines.append(f"- invariant @ {inv['loc']}: `{inv['formula']}` ({inv['role']})")
    lines += ["", f"Prover: {rec['prover']['tool']} — "
              f"**{rec['prover']['verdict_marker']}** in {rec['prover']['wall_seconds']}s "
              f"(mem cap {rec['prover']['memory_cap']})", "", rec["note"], ""]
    up = rec["provenance"].get("upstream")
    if up:
        lines += [f"Ported from KleverBench [`{up['problem']}`]({up['repo']}) "
                  f"@ `{up['sha'][:7]}` — original IMP: `{up['program_imp']}`", ""]
    if rec["counterexample"]:
        ce = rec["counterexample"]
        ft = ce["failing_trace"]
        lines += ["## Counterexample", "",
                  f"- stuck-state path condition: `{' and '.join(ce['stuck_path_condition'])}`",
                  f"- z3 model: `x = {ce['model']['x']}`",
                  f"- concrete replay: `result = {ft['result']!r}` — {ft['why']}", "",
                  "| # | event | line | locals / value |", "|---|---|---|---|"]
        for i, e in enumerate(ft["trace"]):
            d = (json.dumps(e.get("locals", {})) if e["event"] != "return"
                 else f"returns `{e['value']}`")
            lines.append(f"| {i} | {e['event']} | {e['line']} | {d} |")
        lines.append("")
    lines += ["## K claims (verbatim)", "", "```k", rec["spec"]["claim_k"].rstrip(), "```", ""]
    return "\n".join(lines)


def main() -> int:
    only = sys.argv[sys.argv.index("--only") + 1].split(",") if "--only" in sys.argv else None
    outdir = ROOT / "data/k/verification"
    outdir.mkdir(parents=True, exist_ok=True)
    for case in CASES:
        if only is not None and case["id"] not in only:
            continue
        rec = build_case(case)
        (outdir / f"{case['id']}.jsonl").write_text(json.dumps(rec, sort_keys=True) + "\n")
        (outdir / f"{case['id']}.md").write_text(to_markdown(rec))
        extra = ""
        if rec["counterexample"]:
            extra = f" — counterexample x={rec['counterexample']['model']['x']}, replayed"
        print(f"[ok] {case['id']}: {rec['result']} in {rec['prover']['wall_seconds']}s{extra}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
