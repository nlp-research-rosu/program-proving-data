#!/usr/bin/env python3
"""gen_lean_kb_loops — emit PROVED parametric execution-leg files for the
single-while-loop KleverBench ports (KMiniPy/Verification/C<n>Kb*Legs.lean),
generalizing the C12 countdown legs to a table (KB_LOOPS below): multiple
loop variables, an optional branch BEFORE the loop (two prologue legs), one
or two body legs (a branch inside the body), and an optional epilogue (post-
loop statements). The hand-written reachability-logic derivations compose
these legs exactly as C12KbCountdown.lean composes its five.

Method identical to gen_c1/gen_kb_countdown in gen_lean_paths.py: every leg
is generated CONCRETELY at witness seeds (hints run for the rule sequence —
depth-bounded, since the stock literals may drive hundreds of thousands of
steps — and a krun sweep for the configs), sliced at `whileUnfold`
boundaries, then parameterized by pure text substitution with hard asserts
that no witness digits survive and that all leg endpoints coincide with the
shared `loopCfg`/`loopExit` bodies.

Seed discipline: every leg picks its own seed values; the engine builds the
digit->parameter substitution map per leg and asserts pairwise printed-form
uniqueness (seeds, computed values, and program constants must not collide).

Watchdogs: every subprocess runs under timeout (krun 120 s each)."""
from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_lean_traces as glt  # noqa: E402
import gen_lean_paths as glp  # noqa: E402  (TACTIC/subst/emit_path/step_proof et al.)

from pyk.kore.parser import KoreParser  # noqa: E402

ROOT = glt.ROOT
PKG = glt.PKG
INT_LIT = glp.INT_LIT
VAL_INT = glp.VAL_INT
NILSTMTS = glp.NILSTMTS
NIL_FRAME = glp.NIL_FRAME


# ---------------------------------------------------------------------------
# The table. Per program:
#   name/stem       — Lean file prefix (C13KbCountup) / program stem
#   params          — input binder names, in magic-literal order (31337, ...)
#   loop_vars       — env variables live at the loop head, in env (first-
#                     write) order; each is a loopCfg parameter
#   entry           — loopCfg instance expressions at loop entry, keyed by
#                     loop var ('n', '0', '1', or for a branch prologue a
#                     per-path dict)
#   prologue        — [ {tag, seeds, conds: [hyp strings], vals: [exprs]} ]
#                     one entry (plain) or two (branch before the loop);
#                     vals are computed closed forms substituted in configs
#   body            — [ {tag, seeds, conds, vals, out} ]: out maps each loop
#                     var to its value expression after ONE iteration
#   exit_           — {seeds, cond}: guard-false witness + exit hypothesis
#   epilogue_vals   — computed closed forms appearing after the loop (in
#                     terms of the loop vars at exit); [] if the While is the
#                     last statement (the epilogue is then the module tail)
#   final_slots     — final env value expression per binding, in env order
#                     (defines `final`'s parameters implicitly: each distinct
#                     expression becomes a `final` argument in order)
#   ground_limit    — max program literal for assert_counters_ground
#   claim           — one-line docstring of the K claim
# Seeds may be ANY distinct integers; pick them so printed digit forms never
# collide (the engine asserts this).
# ---------------------------------------------------------------------------

KB_LOOPS: list[dict] = [
    dict(name="C13KbCountup", stem="kb_countup", params=["n", "r"],
         loop_vars=["n", "r"], ground_limit=1,
         claim="r climbs to maxInt(n, r0); n unchanged",
         prologue=[dict(tag="", seeds={"n": 31337, "r": 31338},
                        entry={"n": "n", "r": "r"})],
         body=[dict(tag="", seeds={"n": 31339, "r": 31337},
                    conds=["h : r < n"], vals=["(r + 1)"],
                    out={"n": "n", "r": "(r + 1)"})],
         exit_=dict(seeds={"n": 31337, "r": 31338}, cond="h : n ≤ r"),
         final_params="(n r : SortInt)", final_args_at_exit="n r",
         final_slots=[]),
    dict(name="C14KbSum", stem="kb_sum", params=["n", "sum"],
         loop_vars=["n", "sum"], ground_limit=1,
         claim="n drains to 0, sum gains the triangular sum n*(n+1)/2",
         prologue=[dict(tag="", seeds={"n": 31337, "sum": 31338},
                        entry={"n": "n", "sum": "sum"})],
         body=[dict(tag="", seeds={"n": 31337, "sum": 31338},
                    conds=["h : 0 < n"], vals=["(sum + n)", "(n - 1)"],
                    out={"n": "(n - 1)", "sum": "(sum + n)"})],
         exit_=dict(seeds={"n": -31337, "sum": 31338}, cond="h : n ≤ 0"),
         final_params="(n sum : SortInt)", final_args_at_exit="n sum",
         final_slots=[]),
    dict(name="C15KbAddLoop", stem="kb_add_loop", params=["n", "res", "a"],
         loop_vars=["n", "res", "a"], ground_limit=1,
         claim="res gains a * maxInt(n, 0); n drains to minInt(n, 0); a unchanged",
         prologue=[dict(tag="", seeds={"n": 31337, "res": 31338, "a": 31339},
                        entry={"n": "n", "res": "res", "a": "a"})],
         body=[dict(tag="", seeds={"n": 31337, "res": 31338, "a": 31339},
                    conds=["h : 0 < n"], vals=["(res + a)", "(n - 1)"],
                    out={"n": "(n - 1)", "res": "(res + a)", "a": "a"})],
         exit_=dict(seeds={"n": -31337, "res": 31338, "a": 31339},
                    cond="h : n ≤ 0"),
         final_params="(n res a : SortInt)", final_args_at_exit="n res a",
         final_slots=[]),
    dict(name="C16KbSubLoop", stem="kb_sub_loop", params=["a", "b"],
         loop_vars=["a", "b"], ground_limit=1,
         claim="a loses maxInt(b, 0); b drains to minInt(b, 0)",
         prologue=[dict(tag="", seeds={"a": 31337, "b": 31338},
                        entry={"a": "a", "b": "b"})],
         body=[dict(tag="", seeds={"a": 31337, "b": 31353},
                    conds=["h : 0 < b"], vals=["(a - 1)", "(b - 1)"],
                    out={"a": "(a - 1)", "b": "(b - 1)"})],
         exit_=dict(seeds={"a": 31337, "b": -31338}, cond="h : b ≤ 0"),
         final_params="(a b : SortInt)", final_args_at_exit="a b",
         final_slots=[]),
    dict(name="C21KbMultLoop", stem="kb_mult_loop", params=["n", "a"],
         init_lits={"res": 0}, loop_vars=["n", "a", "res"], ground_limit=1,
         claim="res ends as a * maxInt(n, 0) from 0; n drains to minInt(n, 0)",
         prologue=[dict(tag="", seeds={"n": 31337, "a": 31338},
                        entry={"n": "n", "a": "a", "res": "0"})],
         body=[dict(tag="", seeds={"n": 31337, "a": 31338, "res": 31339},
                    conds=["h : 0 < n"], vals=["(res + a)", "(n - 1)"],
                    out={"n": "(n - 1)", "a": "a", "res": "(res + a)"})],
         exit_=dict(seeds={"n": -31337, "a": 31338, "res": 31339},
                    cond="h : n ≤ 0"),
         final_params="(n a res : SortInt)", final_args_at_exit="n a res",
         final_slots=[]),
    dict(name="C22KbTriangleDown", stem="kb_triangle_down", params=["n"],
         init_lits={"sum": 0}, loop_vars=["n", "sum"], ground_limit=1,
         claim="sum ends as the triangle number of maxInt(n, 0) from 0; "
               "n drains to minInt(n, 0)",
         prologue=[dict(tag="", seeds={"n": 31337},
                        entry={"n": "n", "sum": "0"})],
         body=[dict(tag="", seeds={"n": 31337, "sum": 31338},
                    conds=["h : 0 < n"], vals=["(sum + n)", "(n - 1)"],
                    out={"n": "(n - 1)", "sum": "(sum + n)"})],
         exit_=dict(seeds={"n": -31337, "sum": 31338}, cond="h : n ≤ 0"),
         final_params="(n sum : SortInt)", final_args_at_exit="n sum",
         final_slots=[]),
    dict(name="C23KbSumUp", stem="kb_sum_up", params=["n"],
         init_lits={"sum": 0, "i": 1}, loop_vars=["n", "sum", "i"],
         ground_limit=1,
         claim="sum climbs to n*(n+1)/2, i to n + 1, for n >= 0",
         prologue=[dict(tag="", seeds={"n": 31337},
                        entry={"n": "n", "sum": "0", "i": "1"})],
         body=[dict(tag="", seeds={"n": 31339, "sum": 31344, "i": 31337},
                    conds=["h : i ≤ n"], vals=["(sum + i)", "(i + 1)"],
                    out={"n": "n", "sum": "(sum + i)", "i": "(i + 1)"})],
         exit_=dict(seeds={"n": 31337, "sum": 31338, "i": 31353},
                    cond="h : n < i"),
         final_params="(n sum i : SortInt)", final_args_at_exit="n sum i",
         final_slots=[]),
    # ---- S2: a branch inside the loop body (two body legs) -----------------
    dict(name="C24KbCountEven", stem="kb_count_even", params=["n"],
         init_lits={"count": 0, "i": 0}, loop_vars=["n", "count", "i"],
         ground_limit=2,
         claim="count ends as (n+1)/2 (the evens among 0..n-1), i as n, "
               "for n >= 0",
         prologue=[dict(tag="", seeds={"n": 31337},
                        entry={"n": "n", "count": "0", "i": "0"})],
         body=[dict(tag="even", seeds={"n": 31351, "count": 31344, "i": 31338},
                    conds=["h1 : i < n", "h2 : i % 2 = 0"],
                    vals=["(count + 1)", "(i + 1)"],
                    out={"n": "n", "count": "(count + 1)", "i": "(i + 1)"}),
               dict(tag="odd", seeds={"n": 31351, "count": 31344, "i": 31337},
                    conds=["h1 : i < n", "h2 : i % 2 = 1"],
                    vals=["(i + 1)"],
                    out={"n": "n", "count": "count", "i": "(i + 1)"})],
         exit_=dict(seeds={"n": 31337, "count": 31344, "i": 31351},
                    cond="h : n ≤ i"),
         final_params="(n count i : SortInt)", final_args_at_exit="n count i",
         final_slots=[]),
    dict(name="C25KbLoopMax", stem="kb_loop_max", params=["a", "n"],
         aliases={"m": "max"},
         init_anchors={"max": 'Assign(Name("max"), Name("a"))'},
         init_lits={"i": 0}, loop_vars=["a", "n", "m", "i"], ground_limit=1,
         claim="max folds over 0..n-1 seeded with a (maxInt(a, n-1) for "
               "n >= 1), i ends as n",
         prologue=[dict(tag="", seeds={"a": 31337, "n": 31338},
                        entry={"a": "a", "n": "n", "m": "a", "i": "0"})],
         body=[dict(tag="upd", seeds={"a": 31344, "n": 31351, "m": 31338,
                                      "i": 31339},
                    conds=["h1 : i < n", "h2 : m < i"], vals=["(i + 1)"],
                    out={"a": "a", "n": "n", "m": "i", "i": "(i + 1)"}),
               dict(tag="noupd", seeds={"a": 31344, "n": 31351, "m": 31341,
                                        "i": 31339},
                    conds=["h1 : i < n", "h2 : i ≤ m"], vals=["(i + 1)"],
                    out={"a": "a", "n": "n", "m": "m", "i": "(i + 1)"})],
         exit_=dict(seeds={"a": 31344, "n": 31337, "m": 31340, "i": 31351},
                    cond="h : n ≤ i"),
         final_params="(a n m i : SortInt)", final_args_at_exit="a n m i",
         final_slots=[]),
    # ---- S3: a branch BEFORE the loop and/or post-loop statements ----------
    dict(name="C20KbSumdiff", stem="kb_sumdiff", params=["a", "b"],
         init_lits={"res": 0},
         init_anchors={"t": 'Assign(Name("t"), BinOp("-", Name("b"), Name("a")))'},
         loop_vars=["a", "b", "t", "res"], ground_limit=2,
         claim="res ends as 2*|a - b|, t drains to 0",
         prologue=[dict(tag="lt", seeds={"a": 31337, "b": 62688},
                        conds=["h : a < b"], vals=["(b - a)"],
                        entry={"a": "a", "b": "b", "t": "(b - a)", "res": "0"}),
                   dict(tag="ge", seeds={"a": 62688, "b": 31337},
                        conds=["h : b ≤ a"], vals=["(a - b)"],
                        entry={"a": "a", "b": "b", "t": "(a - b)", "res": "0"})],
         body=[dict(tag="", seeds={"a": 31338, "b": 62689, "t": 31351,
                                   "res": 31344},
                    conds=["h : 0 < t"], vals=["(res + 2)", "(t - 1)"],
                    out={"a": "a", "b": "b", "t": "(t - 1)",
                         "res": "(res + 2)"})],
         exit_=dict(seeds={"a": 31338, "b": 62689, "t": -31351, "res": 31344},
                    cond="h : t ≤ 0"),
         final_params="(a b t res : SortInt)", final_args_at_exit="a b t res",
         final_slots=[]),
    dict(name="C32KbPipeline", stem="kb_pipeline", params=["a", "b", "n"],
         init_anchors={"t": 'Assign(Name("t"), BinOp("*", Name("a"), Name("b")))'},
         init_lits={"res": 0, "i": 0},
         loop_vars=["a", "b", "n", "t", "res", "i"], ground_limit=1,
         claim="res ends as |a*b|*n + a for n >= 0; t holds |a*b|, i ends "
               "as n",
         prologue=[dict(tag="neg", seeds={"a": -31337, "b": 31344, "n": 31351},
                        conds=["h : a * b < 0"],
                        vals=["(a * b)", "(0 - a * b)"],
                        entry={"a": "a", "b": "b", "n": "n",
                               "t": "(0 - a * b)", "res": "0", "i": "0"}),
                   dict(tag="nonneg", seeds={"a": 31337, "b": 31344,
                                             "n": 31351},
                        conds=["h : 0 ≤ a * b"], vals=["(a * b)"],
                        entry={"a": "a", "b": "b", "n": "n", "t": "(a * b)",
                               "res": "0", "i": "0"})],
         body=[dict(tag="", seeds={"a": 31337, "b": 31353, "n": 31352,
                                   "t": 31351, "res": 31344, "i": 31338},
                    conds=["h : i < n"], vals=["(res + t)", "(i + 1)"],
                    out={"a": "a", "b": "b", "n": "n", "t": "t",
                         "res": "(res + t)", "i": "(i + 1)"})],
         exit_=dict(seeds={"a": 31337, "b": 31353, "n": 31338, "t": 31351,
                           "res": 31344, "i": 31352},
                    cond="h : n ≤ i", vals=["(res + a)"]),
         final_params="(a b n t res i : SortInt)",
         final_args_at_exit="a b n t (res + a) i",
         final_slots=[("(res + a)", "res")]),
    dict(name="C33KbStatsPipeline", stem="kb_stats_pipeline",
         params=["a", "b", "n"],
         init_anchors={"m": 'Assign(Name("m"), Name("a"))',
                       "x": 'Assign(Name("x"), Name("b"))',
                       "t": 'Assign(Name("t"), BinOp("-", Name("x"), Name("m")))'},
         init_lits={"res": 0, "i": 0},
         loop_vars=["a", "b", "n", "m", "x", "t", "res", "i"], ground_limit=1,
         claim="res ends as (max a b - min a b)*n + min a b for n >= 0; "
               "m/x/t hold min/max/range, i ends as n",
         prologue=[dict(tag="le", seeds={"a": 31337, "b": 62688, "n": 31352},
                        conds=["h : a ≤ b"], vals=["(b - a)"],
                        entry={"a": "a", "b": "b", "n": "n", "m": "a",
                               "x": "b", "t": "(b - a)", "res": "0",
                               "i": "0"}),
                   dict(tag="gt", seeds={"a": 62688, "b": 31337, "n": 31352},
                        conds=["h : b < a"], vals=["(a - b)"],
                        entry={"a": "a", "b": "b", "n": "n", "m": "b",
                               "x": "a", "t": "(a - b)", "res": "0",
                               "i": "0"})],
         body=[dict(tag="", seeds={"a": 31337, "b": 62690, "n": 31352,
                                   "m": 31340, "x": 31341, "t": 31351,
                                   "res": 31344, "i": 31338},
                    conds=["h : i < n"], vals=["(res + t)", "(i + 1)"],
                    out={"a": "a", "b": "b", "n": "n", "m": "m", "x": "x",
                         "t": "t", "res": "(res + t)", "i": "(i + 1)"})],
         exit_=dict(seeds={"a": 31337, "b": 62690, "n": 31338, "m": 31340,
                           "x": 31341, "t": 31351, "res": 31344, "i": 31352},
                    cond="h : n ≤ i", vals=["(res + m)"]),
         final_params="(a b n m x t res i : SortInt)",
         final_args_at_exit="a b n m x t (res + m) i",
         final_slots=[("(res + m)", "res")]),
    dict(name="C34KbNormalizeCount", stem="kb_normalize_count",
         params=["a", "b", "n"], init_lits={"count": 0},
         loop_vars=["a", "b", "n", "count"], ground_limit=1,
         claim="count ends as |n|, res as |n|*a + b; n normalized then "
               "drained to 0",
         prologue=[dict(tag="neg", seeds={"a": 31337, "b": 31344, "n": -31351},
                        conds=["h : n < 0"], vals=["(0 - n)"],
                        entry={"a": "a", "b": "b", "n": "(0 - n)",
                               "count": "0"}),
                   dict(tag="nonneg", seeds={"a": 31337, "b": 31344,
                                             "n": 31351},
                        conds=["h : 0 ≤ n"],
                        entry={"a": "a", "b": "b", "n": "n", "count": "0"})],
         body=[dict(tag="", seeds={"a": 31337, "b": 31344, "n": 31351,
                                   "count": 31338},
                    conds=["h : 0 < n"], vals=["(n - 1)", "(count + 1)"],
                    out={"a": "a", "b": "b", "n": "(n - 1)",
                         "count": "(count + 1)"})],
         exit_=dict(seeds={"a": 31337, "b": 31344, "n": 0, "count": 31338},
                    ground={"n": "0"},
                    vals=["(count * a)", "(count * a + b)"]),
         final_params="(a b count res : SortInt)",
         final_args_at_exit="a b count (count * a + b)",
         final_slots=[("(count * a + b)", "res")]),
]


def digits_of(v: int) -> str:
    return f"({v})" if v < 0 else str(v)


def check_no_collisions(pairs: list[tuple[str, str]], limit: int) -> None:
    """Every substitution's old printed form must be unique and must not be a
    substring of another old form except via the parenthesized-negative rule
    (handled by longest-first ordering)."""
    olds = [o for o, _ in pairs]
    assert len(set(olds)) == len(olds), f"duplicate substitution sources: {olds}"
    for o in olds:
        m = re.search(r"» (\(?-?\d+\)?)\)$", o)
        assert m, o
        d = m.group(1).strip("()")
        assert abs(int(d.lstrip("-"))) > limit, \
            f"seed/value {d} collides with program-constant range ≤ {limit}"


class Engine:
    def __init__(self, printer, arities, ord2label, rule_by_label):
        self.printer = printer
        self.arities = arities
        self.ord2label = ord2label
        self.rule_by_label = rule_by_label

    def prints(self, kores: list[str]):
        kpats = [KoreParser(c).pattern() for c in kores]
        raws = [str(self.printer._transform_pattern(p, concrete=True)) for p in kpats]
        return kpats, raws

    def build(self, kpats, raws, rules_slice, subs, gone, limit, post=None):
        assert len(raws) == len(rules_slice) + 1, \
            f"{len(raws)} configs vs {len(rules_slice)} rules"
        texts = [post(t) for t in raws] if post else list(raws)
        cterms = [glp.subst(t, subs, gone) for t in texts]
        for t in cterms:
            glp.assert_counters_ground(t, limit)
        steps = []
        for j, lbl in enumerate(rules_slice):
            sp = glp.subst(glp.step_proof(lbl, self.arities,
                                          self.rule_by_label.get(lbl),
                                          kpats[j], self.printer),
                           subs, gone)
            steps.append((lbl, sp))
        return cterms, steps, len(rules_slice)

    def seeded_mpy(self, cfg, seeds: dict) -> str:
        """Program mpy with each param's magic literal replaced by the seed
        (two-stage placeholders: seeds may permute the magics)."""
        stock = (ROOT / "build/lean/mpy" / f"{cfg['stem']}.mpy").read_text()
        magics = {p: glp.KB_MAGICS[i] for i, p in enumerate(cfg["params"])}
        out = stock
        for i, p in enumerate(cfg["params"]):
            if p not in seeds:
                continue
            assert f"Int({magics[p]})" in out, (cfg["stem"], p)
            out = out.replace(f"Int({magics[p]})", f"Int(@{i}@)")
        for i, p in enumerate(cfg["params"]):
            if p in seeds:
                out = out.replace(f"@{i}@", str(seeds[p]))
        return out

    def leg_subs(self, cfg, seeds: dict, vals: list[str], env: dict) -> tuple[list, tuple]:
        """Substitutions for one leg: param seeds -> param names, computed
        expressions (evaluated in `env`, which includes the seed values under
        their PARAMETER-EXPRESSION meaning) -> their expression text."""
        pairs, gone = [], set()
        for p in cfg["params"]:
            d = digits_of(seeds[p])
            pairs += [(INT_LIT.format(d), INT_LIT.format(p)),
                      (VAL_INT.format(d), VAL_INT.format(p))]
            gone.add(str(abs(seeds[p])))
        seen = {digits_of(v) for v in seeds.values()}
        for expr in vals:
            v = eval(expr.replace("//", "//"), {}, dict(env))
            d = digits_of(v)
            assert d not in seen, f"computed {expr} = {v} collides with a seed/value"
            seen.add(d)
            pairs.append((VAL_INT.format(d), VAL_INT.format(expr)))
            gone.add(str(abs(v)))
        check_no_collisions(pairs, cfg["ground_limit"])
        pairs.sort(key=lambda s: len(s[0]), reverse=True)
        return pairs, tuple(sorted(gone, key=len, reverse=True))

    def rules_for(self, tag: str, mpy_text: str, depth: int | None):
        path = ROOT / "build/lean/mpy" / f"{tag}.mpy"
        path.write_text(mpy_text)
        rules = [self.ord2label[o]
                 for o in glp.rule_sequence_depth(tag, path, depth=depth)]
        return path, rules


def wu_indexes(rules: list[str]) -> list[int]:
    return [k for k, l in enumerate(rules) if l == "whileUnfold"]


def make_post_rest(s0: str):
    """Parameterize the ground continuation: rightmost occurrence inside the
    k cell (C12's fix: the nil frame text can also occur inside a frozen
    else-branch of the heated guard)."""
    def post_rest(t: str) -> str:
        k_end = t.index(" }, env := ")
        assert s0 in t[:k_end], "loop continuation not found in k cell"
        assert t.count(s0, k_end) == 0, "continuation text outside the k cell"
        i = t.rindex(s0, 0, k_end)
        return t[:i] + "rest" + t[i + len(s0):]
    return post_rest


def gen_one(eng: Engine, cfg: dict) -> None:
    """Generate <name>Legs.lean for one single-loop program."""
    name, stem = cfg["name"], cfg["stem"]
    lvars = cfg["loop_vars"]
    limit = cfg["ground_limit"]
    src = (glt.REPO / "programs" / f"{stem}.py").read_text()

    def seeded(seeds: dict) -> str:
        """Seed input params (magic replacement) and prologue-initialized
        loop vars (initializer-literal rewrite)."""
        out = eng.seeded_mpy(cfg, {p: seeds[p] for p in cfg["params"]
                                    if p in seeds})
        aliases = cfg.get("aliases", {})
        for var, lit in cfg.get("init_lits", {}).items():
            binder = next((b for b, pv in aliases.items() if pv == var), var)
            if binder in seeds:
                anchor = f'Assign(Name("{var}"), Int({lit}))'
                assert out.count(anchor) == 1, (stem, anchor)
                out = out.replace(anchor,
                                  f'Assign(Name("{var}"), Int({seeds[binder]}))')
        for var, anchor in cfg.get("init_anchors", {}).items():
            binder = next((b for b, pv in aliases.items() if pv == var), var)
            if binder in seeds:
                assert out.count(anchor) == 1, (stem, anchor)
                out = out.replace(anchor,
                                  f'Assign(Name("{var}"), Int({seeds[binder]}))')
        return out

    def lsubs(seeds: dict, vals: list[str], names: dict | None = None,
              env_extra: dict | None = None) -> tuple[list, tuple]:
        """Digit->name substitutions over the LEG's binder names: `names`
        maps seed keys to binder names (default: identity); `env_extra`
        widens the eval environment for `vals` (ground exit slots)."""
        names = names or {}
        pairs, gone = [], set()
        for k, v in seeds.items():
            d = digits_of(v)
            nm = names.get(k, k)
            pairs += [(INT_LIT.format(d), INT_LIT.format(nm)),
                      (VAL_INT.format(d), VAL_INT.format(nm))]
            gone.add(f"\u00bb {d})")
        seen = {digits_of(v) for v in seeds.values()}
        env = {names.get(k, k): v for k, v in (env_extra or seeds).items()}
        for expr in vals:
            v = eval(expr, {}, dict(env))
            d = digits_of(v)
            assert d not in seen, f"{stem}: computed {expr} = {v} collides"
            seen.add(d)
            pairs.append((VAL_INT.format(d), VAL_INT.format(expr)))
            gone.add(f"\u00bb {d})")
        check_no_collisions(pairs, limit)
        pairs.sort(key=lambda s: len(s[0]), reverse=True)
        return pairs, tuple(sorted(gone, key=len, reverse=True))

    # ---- exit witness: guard false at first arrival; yields s0/loopExit/
    # exit leg and the epilogue slice (boundary = first seqDone past the
    # unfold, popping the unfolded block's residue)
    ex = cfg["exit_"]
    ground = ex.get("ground", {})  # binder -> literal expr pinned in exit/epilogue
    ex_path, ex_rules = eng.rules_for(f"{stem}_exit", seeded(ex["seeds"]), None)
    ewu = wu_indexes(ex_rules)
    assert len(ewu) == 1, f"{stem}: exit witness ran {len(ewu)} unfolds"
    lo = ewu[0]
    sd = next(k for k in range(lo, len(ex_rules)) if ex_rules[k] == "seqDone")
    boundary = sd + 1
    ex_kp, ex_raw = eng.prints(glp.sweep_range(ex_path, lo, len(ex_rules)))
    s0 = glp.kval_of(ex_raw[boundary - lo])
    post_rest = make_post_rest(s0)

    ex_seed_named = {k: v for k, v in ex["seeds"].items() if k not in ground}
    ex_env = dict(ex["seeds"])
    ex_subs, ex_gone = lsubs(ex_seed_named, ex.get("vals", []), env_extra=ex_env)
    exit_ct, exit_steps, n_exit = eng.build(
        ex_kp[:boundary - lo + 1], ex_raw[:boundary - lo + 1],
        ex_rules[lo:boundary], ex_subs, ex_gone, limit, post=post_rest)
    epi_ct, epi_steps, n_epi = eng.build(
        ex_kp[boundary - lo:], ex_raw[boundary - lo:],
        ex_rules[boundary:], ex_subs, ex_gone, limit)
    assert n_epi >= 1, f"{stem}: empty epilogue — adapt like C12's fallback note"
    loopexit_body = exit_ct[-1]
    for v, lit in ground.items():
        assert loopexit_body.count(VAL_INT.format(lit)) == 1, \
            f"{stem}: ground slot {v} not unique in loopExit"
        loopexit_body = loopexit_body.replace(VAL_INT.format(lit),
                                              VAL_INT.format(v))
    assert loopexit_body.count("{ val := rest }") == 1
    lx_at_ground = loopexit_body
    for v, lit in ground.items():
        lx_at_ground = lx_at_ground.replace(VAL_INT.format(v),
                                            VAL_INT.format(lit))
    assert epi_ct[0] == lx_at_ground.replace(
        "{ val := rest }", "{ val := " + s0 + " }"), \
        f"{stem}: epilogue start vs loopExit at loopRest"
    final_body = epi_ct[-1]

    # ---- body legs: loopCfg body from the FIRST body witness
    body_res = []
    for b in cfg["body"]:
        b_path, b_rules = eng.rules_for(f"{stem}_body_{b['tag'] or 'b'}",
                                        seeded(b["seeds"]),
                                        b.get("depth", 120))
        bwu = wu_indexes(b_rules)
        assert len(bwu) >= 2, f"{stem}/{b['tag']}: <2 unfolds at body witness"
        b_kp, b_raw = eng.prints(glp.sweep_range(b_path, bwu[0], bwu[1]))
        b_subs, b_gone = lsubs(b["seeds"], b.get("vals", []))
        ct, steps, n = eng.build(b_kp, b_raw, b_rules[bwu[0]:bwu[1]],
                                 b_subs, b_gone, limit, post=post_rest)
        body_res.append((b, ct, steps, n))

    loopcfg_body = body_res[0][1][0]
    assert loopcfg_body.count("(rest)") == 1
    for v in lvars:
        assert loopcfg_body.count(VAL_INT.format(v)) == 1, \
            f"{stem}: loop var {v} slot not unique in loopCfg"

    def inst_loopcfg(vmap: dict, rest: str) -> str:
        t = loopcfg_body.replace("(rest)", "@R@")
        for i, v in enumerate(lvars):
            t = t.replace(VAL_INT.format(v), f"@V{i}@")
        for i, v in enumerate(lvars):
            t = t.replace(f"@V{i}@", VAL_INT.format(vmap[v]))
        return t.replace("@R@", rest)

    nil_rest = "(SortK.kseq (SortKItem.inj_SortStmts " + NILSTMTS + ") (rest))"
    for b, ct, _steps, _n in body_res:
        assert ct[0] == loopcfg_body, f"{stem}/{b['tag']}: body start ≠ loopCfg"
        assert ct[-1] == inst_loopcfg(b["out"], nil_rest), \
            f"{stem}/{b['tag']}: body end ≠ loopCfg out (nil-frame rest)"
    exit_inst = {**{v: v for v in lvars}, **ground}
    if ground:
        assert exit_ct[0] == inst_loopcfg(exit_inst, "(rest)"), \
            f"{stem}: exit start ≠ loopCfg at ground slots"
    else:
        assert exit_ct[0] == inst_loopcfg(exit_inst, "(rest)") == loopcfg_body, \
            f"{stem}: exit start ≠ loopCfg"

    # ---- prologue leg(s): start .. first unfold; endpoint = entry instance
    pro_res = []
    for pr in cfg["prologue"]:
        p_path, p_rules = eng.rules_for(f"{stem}_pro_{pr['tag'] or 'p'}",
                                        seeded(pr["seeds"]),
                                        pr.get("depth", 120))
        pwu = wu_indexes(p_rules)
        assert pwu, f"{stem}/{pr['tag']}: no unfold at prologue witness"
        p_kp, p_raw = eng.prints(glp.sweep_range(p_path, 0, pwu[0]))
        p_subs, p_gone = lsubs(pr["seeds"], pr.get("vals", []))
        ct, steps, n = eng.build(p_kp, p_raw, p_rules[:pwu[0]],
                                 p_subs, p_gone, limit)
        entry = pr["entry"]
        assert ct[-1] == inst_loopcfg(entry, "(" + s0 + ")"), \
            f"{stem}/{pr['tag']}: prologue end ≠ loopCfg entry loopRest"
        pro_res.append((pr, ct, steps, n))

    init_body = pro_res[0][1][0]
    for pr, ct, _s, _n in pro_res[1:]:
        assert ct[0] == init_body, f"{stem}: prologue inits disagree"

    # ---- emission
    lv_params = "(" + " ".join(lvars) + " : SortInt)"
    lv_args = " ".join(lvars)
    in_params = "(" + " ".join(cfg["params"]) + " : SortInt)"
    in_args = " ".join(cfg["params"])
    sections, counts = [], []

    for pr, ct, steps, n in pro_res:
        tag = f"prologue{('_' + pr['tag']) if pr['tag'] else ''}"
        conds = "".join(f" ({c})" for c in pr.get("conds", []))
        hargs = "".join(" " + c.split(" : ")[0] for c in pr.get("conds", []))
        entry_args = " ".join(e if e.isalnum() or e.startswith("(") else f"({e})"
                              for e in (pr["entry"][v] for v in lvars))
        defs, fold = glp.emit_path(tag, in_params, in_args,
                                   in_params + conds, in_args + hargs,
                                   f"(init {in_args})",
                                   f"(loopCfg {entry_args} loopRest)",
                                   ct, steps, n)
        rec = f"set_option maxRecDepth {max(2048, 16 * n)} in\n"
        sections.append(f"""{defs}
{rec}/-- Program start to the loop head{(' (' + ', '.join(pr['conds']) + ')') if pr.get('conds') else ''}. -/
theorem {tag}_leg {in_params}{conds} :
    Rewrites (init {in_args}) (loopCfg {entry_args} loopRest) :=
  {fold}
""")
        counts.append((tag, n))

    for b, ct, steps, n in body_res:
        tag = f"body{('_' + b['tag']) if b['tag'] else ''}"
        conds = "".join(f" ({c})" for c in b["conds"])
        hargs = "".join(" " + c.split(" : ")[0] for c in b["conds"])
        out_args = " ".join(e if e.isalnum() or e.startswith("(") else f"({e})"
                            for e in (b["out"][v] for v in lvars))
        vp = lv_params + " (rest : SortK)"
        va = lv_args + " rest"
        defs, fold = glp.emit_path(tag, vp, va, vp + conds, va + hargs,
                                   f"(loopCfg {lv_args} rest)",
                                   f"(loopCfg {out_args} {NIL_FRAME})",
                                   ct, steps, n)
        rec = f"set_option maxRecDepth {max(2048, 16 * n)} in\n"
        sections.append(f"""{defs}
{rec}/-- One loop iteration ({', '.join(b['conds'])}); the unfolded block leaves
one residue frame on the continuation. -/
theorem {tag}_leg {vp}{conds} :
    Rewrites (loopCfg {lv_args} rest) (loopCfg {out_args} {NIL_FRAME}) :=
  {fold}
""")
        counts.append((tag, n))

    ex_vars = [v for v in lvars if v not in ground]
    exv_params = "(" + " ".join(ex_vars) + " : SortInt)"
    exv_args = " ".join(ex_vars)
    lc_ex_args = " ".join(ground.get(v, v) for v in lvars)
    vp = exv_params + " (rest : SortK)"
    va = exv_args + " rest"
    cond_b = f" ({ex['cond']})" if ex.get("cond") else ""
    cond_a = " " + ex["cond"].split(" : ")[0] if ex.get("cond") else ""
    defs, fold = glp.emit_path("exitp", vp, va, vp + cond_b, va + cond_a,
                               f"(loopCfg {lc_ex_args} rest)",
                               f"(loopExit {lc_ex_args} rest)",
                               exit_ct, exit_steps, n_exit)
    sections.append(f"""{defs}
set_option maxRecDepth {max(2048, 16 * n_exit)} in
/-- Loop exit{(' (' + ex['cond'] + ')') if ex.get('cond') else ' (guard false at the pinned slot)'}: guard false, the exiting unfold's
residue popped; the k cell becomes the continuation `rest`. -/
theorem exit_leg {vp}{cond_b} :
    Rewrites (loopCfg {lc_ex_args} rest) (loopExit {lc_ex_args} rest) :=
  {fold}
""")
    counts.append(("exit", n_exit))

    final_params = cfg["final_params"]
    final_args_at_exit = cfg["final_args_at_exit"]
    defs, fold = glp.emit_path("epilogue", exv_params, exv_args,
                               exv_params, exv_args,
                               f"(loopExit {lc_ex_args} loopRest)",
                               f"(final {final_args_at_exit})",
                               epi_ct, epi_steps, n_epi)
    sections.append(f"""{defs}
set_option maxRecDepth {max(2048, 16 * n_epi)} in
/-- From loop exit at the ground continuation through the module tail
(post-loop statements included) to the terminal configuration. -/
theorem epilogue_leg {exv_params} :
    Rewrites (loopExit {lc_ex_args} loopRest) (final {final_args_at_exit}) :=
  {fold}
""")
    counts.append(("epilogue", n_epi))

    # `final` def: parameterize the epilogue's terminal config by final_slots
    fin = final_body
    for slot_expr, param in cfg["final_slots"]:
        assert fin.count(VAL_INT.format(slot_expr)) == 1, \
            f"{stem}: final slot {slot_expr!r} not unique"
        fin = fin.replace(VAL_INT.format(slot_expr), VAL_INT.format(param))

    counts_doc = ", ".join(f"{t} {n}" for t, n in counts)
    body_txt = f"""import KMiniPy.Relations

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false  -- uniform leg binders; hyps used only on guard steps

/-! {name}Legs: PROVED parametric execution legs for `{stem}` — the
fragments its reachability-logic derivation ({name}.lean) composes,
generated by witness generalization exactly like the C12 countdown legs
(see C12KbCountdownLegs.lean for the architecture notes: `rest : SortK`
continuation parameter, one nil residue frame per iteration, exit through
`loopExit`/`nil_step`/`epilogue_leg`).
Program (CPython-validated against the same K semantics):
{chr(10).join('    ' + l for l in src.rstrip().splitlines())}
Proof: tran-folds of {counts_doc} steps; nil_step is one `seqDone`.
-/

namespace {name}Legs

def init {in_params} : SortGeneratedTopCell :=
  {init_body}

def final {final_params} : SortGeneratedTopCell :=
  {fin}

/-- The ground continuation below the While statement on loop entry. -/
def loopRest : SortK :=
  {s0}

/-- Loop-head configuration at the start of a `whileUnfold` step. -/
def loopCfg {lv_params} (rest : SortK) : SortGeneratedTopCell :=
  {loopcfg_body}

/-- Post-loop configuration: guard false, block residue popped, k = rest. -/
def loopExit {lv_params} (rest : SortK) : SortGeneratedTopCell :=
  {loopexit_body}

/-- Pops one residue frame (`seqDone`). -/
theorem nil_step {lv_params} (rest : SortK) :
    Rewrites (loopExit {lv_args} {NIL_FRAME})
      (loopExit {lv_args} rest) :=
  Rewrites.seqDone

{chr(10).join(sections)}
end {name}Legs
"""
    out = PKG / "KMiniPy" / "Verification" / f"{name}Legs.lean"
    out.write_text(body_txt)
    print(f"[ok] {name}Legs: proved, {counts_doc}")


# ---------------------------------------------------------------------------
# NESTED loops (c26–c31 family). Architecture per docs: the INNER loop enters
# the RL derivation as a ∀-quantified Rewrites lemma proved by fuel induction
# in the hand-written derivation file; only the OUTER loop is a Circularity.
# The legs here are the raw material: two outer loop-head shapes (j unbound at
# the first arrival -> 3-entry env `outerCfg3`; bound afterwards ->
# `outerCfg4`), inner loop-head/exit shapes parametric in an opaque
# `irest : SortK`, and ONE concrete mid-continuation `midK rest` (the outer
# body's tail below the inner While: `[i = i - 1; While_outer]` over `rest`).
#
# Witness discipline (everything Lean re-checks; the asserts certify the
# endpoint identities the derivation's tran-folds rely on):
#   * entry3/inner witnesses seed `i` by REWRITING the `i = a` initializer
#     (the C25 init_anchor idea), so `i`'s env value is independent of `a`.
#   * the entry4 witness runs the STOCK shape past the first outer iteration
#     (b = 2 -> exactly 2 inner iterations) and slices at the SECOND outer
#     unfold; outer-vs-inner whileUnfold ordinals are told apart by the
#     interleaving pattern computed from the seeds AND by asserting the
#     k-cell head at the slice start is the outer While. The dead `j` slot
#     (0 = min(b, 0) there, colliding with the guard literal) is generalized
#     by a slot-targeted substitution on the env text — legal because `j` is
#     never read in the leg (immediately overwritten by `j = b`).
#   * the inner-exit/post-inner witness drives `j = b < 0` (guard false on
#     inner entry), so `j`'s value collides with `b`'s: the `b` slot is
#     pinned first by the same slot-targeted substitution ( `b` is never read
#     in these legs), then every remaining occurrence is `j`.
#   * the outer-exit witness needs a 4-entry env with the guard false, which
#     NO real run reaches with collision-free values (i = 0 and j ∈ {0, b}
#     at any real exit): its program additionally INSERTS a `j = <seed>`
#     initializer before the While — same env shape/order, same ground
#     continuation, distinct seed everywhere; cross-asserted against the
#     entry4-derived `outerCfg4` body.
# ---------------------------------------------------------------------------

# Nested-table schema (per program; env order everywhere):
#   lits            — input params -> stock init literals
#   accs            — accumulator vars -> stock init literals (0), seeded via
#                     their initializer anchors
#   i_from          — the param copied into i (`i = a` / `i = n` anchor)
#   inner_bound     — the var copied into j at inner entry ("b" or "i")
#   body_out        — post-one-inner-iteration value expression per changed var
#   entry_conds     — entry3/entry4 hypothesis binders (default ["h : 0 < i"])
#   skip3           — c31 only: the refused-branch outer iteration witness
#   prologue/entry3 — witness seeds (+ hints depth)
#   entry4          — small-bound seeds; k2 = wu index of the SECOND outer
#                     unfold (computed from the seeds' interleave, asserted
#                     against the config shape); `state` = expected env values
#                     at that head for non-param vars, each handled by "sub"
#                     (ordinary digit substitution) or "slot" (slot-targeted:
#                     the value collides with a program constant or another
#                     binder but the var is dead in the leg)
#   inner_body      — witness sliced at the SECOND inner head (wu[2]..wu[3]);
#                     `head` = observed values there (evolved accs + j)
#   inner_exit      — mode "bneg" (j = b < 0 at the first inner head; b slot
#                     pinned, j generalized) or "ground0" (bound is i: the
#                     leg is stated at the ground drained bound j = 0, from a
#                     small-i witness; `head` = evolved acc values there)
#   exit_           — outer-exit witness: i < 0 plus an INSERTED j initializer
#   surgery_doc / midk_doc / midk_def_doc / doc3 / doc4 / postin_doc /
#   body_doc        — emitted documentation fragments (c26 wording is frozen)

C26_SURGERY = """the entry4 leg is sliced at the SECOND outer
unfold of a small-`b` run (interleave pattern asserted; the dead `j` slot is
generalized by a slot-targeted env substitution); the inner-exit/post-inner
witness drives `j = b < 0`, with the never-read `b` slot pinned first; the
outer-exit witness INSERTS a `j` initializer before the While (no real run
reaches a collision-free 4-env exit state) — same env order and ground
continuation, asserted against the entry4-derived `outerCfg4`."""

KB_NESTED: list[dict] = [
    dict(name="C26KbPureNested", stem="kb_pure_nested",
         lits={"a": 137, "b": 138}, accs={}, i_from="a", inner_bound="b",
         body_out={"j": "(j - 1)"},
         ground_limit=1,
         claim="i drains to 0 through the pure nested drain, j ends "
               "minInt(b, 0); a and b unchanged (K claim requires a >= 1)",
         surgery_doc=C26_SURGERY,
         prologue=dict(seeds={"a": 31337, "b": 31338}, depth=60),
         entry3=dict(seeds={"a": 31337, "b": 31338, "i": 31351}, depth=120),
         entry4=dict(seeds={"a": 31337, "b": 2}, depth=260, k2=4,
                     state={"i": (31336, "sub"), "j": (0, "slot")}),
         inner_body=dict(seeds={"a": 31337, "b": 31344, "i": 31351}, depth=160,
                         head={"j": 31343}),
         inner_exit=dict(seeds={"a": 31337, "b": -31338, "i": 31351}, depth=140,
                         mode="bneg"),
         exit_=dict(seeds={"a": 31337, "b": 31338, "i": -31351, "j": 31344})),
    dict(name="C27KbMultNested", stem="kb_mult_nested",
         lits={"a": 137, "b": 138}, accs={"res": 0}, i_from="a",
         inner_bound="b", body_out={"res": "(res + 1)", "j": "(j - 1)"},
         ground_limit=1,
         claim="res gains a * maxInt(b, 0) by nested repeated increment; "
               "i to 0, j to minInt(b, 0) (K claim requires a >= 1)",
         body_doc="`res += 1`, `j -= 1`",
         surgery_doc="""the entry4 leg is sliced at the SECOND outer
unfold of a small-`b` run (interleave pattern asserted; the dead `j` and
`res` slots — `res` equals `b` there — are generalized by slot-targeted env
substitutions); the inner-exit/post-inner witness drives `j = b < 0`, with
the never-read `b` slot pinned first; the outer-exit witness INSERTS a `j`
initializer before the While (no real run reaches a collision-free 5-env
exit state) — same env order and ground continuation, asserted against the
entry4-derived `outerCfg4`.""",
         prologue=dict(seeds={"a": 31337, "b": 31338}, depth=80),
         entry3=dict(seeds={"a": 31337, "b": 31338, "res": 31344, "i": 31351},
                     depth=140),
         entry4=dict(seeds={"a": 31337, "b": 2}, depth=320, k2=4,
                     state={"res": (2, "slot"), "i": (31336, "sub"),
                            "j": (0, "slot")}),
         inner_body=dict(seeds={"a": 31337, "b": 31344, "res": 31305,
                                "i": 31351},
                         depth=220, head={"res": 31306, "j": 31343}),
         inner_exit=dict(seeds={"a": 31337, "b": -31338, "res": 31344,
                                "i": 31351},
                         depth=180, mode="bneg"),
         exit_=dict(seeds={"a": 31337, "b": 31338, "res": 31344, "i": -31351,
                           "j": 31305})),
    dict(name="C28KbTriangleNested", stem="kb_triangle_nested",
         lits={"n": 137}, accs={"count": 0}, i_from="n", inner_bound="i",
         body_out={"count": "(count + 1)", "j": "(j - 1)"},
         ground_limit=1,
         claim="count gains the triangle number n*(n+1)/2, one inner "
               "iteration at a time; i to 0, j to 0 (K claim requires n >= 1)",
         body_doc="`count += 1`, `j -= 1`",
         surgery_doc="""the entry4 leg is sliced at the SECOND outer
unfold of a small-`n` run (interleave pattern asserted; the dead `j` and
`count` slots — `count` equals `n` there — are generalized by slot-targeted
env substitutions); the inner bound is the OUTER counter (`j := i`), so no
real run reaches an inner head with `j ≤ 0` and collision-free values — the
inner-exit leg is stated at the ground drained bound `j = 0` (the only shape
`inner_all` needs under `0 ≤ j`), from a small-`i` witness; the outer-exit
witness INSERTS a `j` initializer before the While — same env order and
ground continuation, asserted against the entry4-derived `outerCfg4`.""",
         prologue=dict(seeds={"n": 31337}, depth=80),
         entry3=dict(seeds={"n": 31337, "count": 31344, "i": 31351},
                     depth=140),
         entry4=dict(seeds={"n": 3}, depth=340, k2=5,
                     state={"count": (3, "slot"), "i": (2, "sub"),
                            "j": (0, "slot")}),
         inner_body=dict(seeds={"n": 31337, "count": 31305, "i": 31351},
                         depth=220, head={"count": 31306, "j": 31350}),
         inner_exit=dict(seeds={"n": 31337, "count": 31305, "i": 3},
                         depth=320, mode="ground0", head={"count": 31308}),
         exit_=dict(seeds={"n": 31337, "count": 31344, "i": -31351,
                           "j": 31305})),
    dict(name="C29KbSquaresCubic", stem="kb_squares_cubic",
         lits={"n": 137}, accs={"res": 0}, i_from="n", inner_bound="i",
         body_out={"res": "(res + i)", "j": "(j - 1)"},
         ground_limit=1,
         claim="res gains the sum of squares n*(n+1)*(2n+1)/6 (i added i "
               "times per row); i to 0, j to 0 (K claim requires n >= 1)",
         body_doc="`res += i`, `j -= 1`",
         surgery_doc="""the entry4 leg is sliced at the SECOND outer
unfold of a small-`n` run (interleave pattern asserted; the dead `j` slot is
generalized by a slot-targeted env substitution); the inner bound is the
OUTER counter (`j := i`), so the inner-exit leg is stated at the ground
drained bound `j = 0` (the only shape `inner_all` needs under `0 ≤ j`), from
a small-`i` witness; the outer-exit witness INSERTS a `j` initializer before
the While — same env order and ground continuation, asserted against the
entry4-derived `outerCfg4`.""",
         prologue=dict(seeds={"n": 31337}, depth=80),
         entry3=dict(seeds={"n": 31337, "res": 31344, "i": 31351}, depth=140),
         entry4=dict(seeds={"n": 3}, depth=340, k2=5,
                     state={"res": (9, "sub"), "i": (2, "sub"),
                            "j": (0, "slot")}),
         inner_body=dict(seeds={"n": 31337, "res": 31200, "i": 31351},
                         depth=220, head={"res": 62551, "j": 31350}),
         inner_exit=dict(seeds={"n": 31337, "res": 31200, "i": 3},
                         depth=320, mode="ground0", head={"res": 31209}),
         exit_=dict(seeds={"n": 31337, "res": 31344, "i": -31351,
                           "j": 31305})),
    dict(name="C30KbRowsSumNested", stem="kb_rows_sum_nested",
         lits={"a": 137, "b": 138}, accs={"sum": 0}, i_from="a",
         inner_bound="b", body_out={"sum": "(sum + j)", "j": "(j - 1)"},
         ground_limit=1,
         claim="sum gains a rows of the row sum b + ... + 1 (2*sum = "
               "a*maxInt(b,0)*(maxInt(b,0)+1)); i to 0, j to minInt(b, 0) "
               "(K claim requires a >= 1)",
         body_doc="`sum += j`, `j -= 1`",
         surgery_doc="""the entry4 leg is sliced at the SECOND outer
unfold of a small-`b` run (interleave pattern asserted; the dead `j` slot is
generalized by a slot-targeted env substitution); the inner-exit/post-inner
witness drives `j = b < 0`, with the never-read `b` slot pinned first; the
outer-exit witness INSERTS a `j` initializer before the While — same env
order and ground continuation, asserted against the entry4-derived
`outerCfg4`.""",
         prologue=dict(seeds={"a": 31337, "b": 31338}, depth=80),
         entry3=dict(seeds={"a": 31337, "b": 31338, "sum": 31344, "i": 31351},
                     depth=140),
         entry4=dict(seeds={"a": 31337, "b": 2}, depth=320, k2=4,
                     state={"sum": (3, "sub"), "i": (31336, "sub"),
                            "j": (0, "slot")}),
         inner_body=dict(seeds={"a": 31337, "b": 31344, "sum": 31200,
                                "i": 31351},
                         depth=220, head={"sum": 62544, "j": 31343}),
         inner_exit=dict(seeds={"a": 31337, "b": -31338, "sum": 31344,
                                "i": 31351},
                         depth=180, mode="bneg"),
         exit_=dict(seeds={"a": 31337, "b": 31338, "sum": 31344, "i": -31351,
                           "j": 31305})),
    dict(name="C31KbNestedWithBranch", stem="kb_nested_with_branch",
         lits={"a": 137, "b": 138}, accs={"res": 0}, i_from="a",
         inner_bound="i", body_out={"res": "(res + 1)", "j": "(j - 1)"},
         entry_conds=["h1 : 0 < i", "h2 : i ≤ b"],
         ground_limit=1,
         claim="res gains m*(m+1)/2 for m = minInt(a, b) (only rows i <= b "
               "admitted); i to 0, j to 0 (K claim requires a >= 1, b >= 1)",
         body_doc="`res += 1`, `j -= 1`",
         midk_doc="(the outer body's tail below the inner While: the emptied "
                  "then-branch\nresidue, `[i = i - 1]` and the re-heated "
                  "outer While over `rest`)",
         midk_def_doc="The concrete continuation below the INNER While inside "
                      "the outer body:\nthe emptied then-branch residue, then "
                      "the outer block's remaining\nstatements (`i = i - 1`, "
                      "the outer While loop-back) over `rest`.",
         doc3="First-arrival outer iteration head into the inner loop head: "
              "guard\ntrue, branch `i ≤ b` admitted, `j := i` (binding j — "
              "the env grows to 5\nentries), the inner While heated over the "
              "concrete mid-continuation\n`midK rest`.",
         doc4="Subsequent-arrival outer iteration head into the inner loop "
              "head\n(5-entry env, `j` dead on entry): guard true, branch "
              "admitted, `j := i`,\nthe inner While heated over `midK rest`.",
         postin_doc="From the drained inner loop at the concrete "
                    "mid-continuation: the\nthen-branch residue pops, "
                    "`i -= 1` and the outer While heats — one residue\nframe "
                    "per completed outer iteration.",
         surgery_doc="""the outer body's branch adds a `skip3_leg` (a `b < i`
iteration that only decrements `i`; skipping can only happen while `j` is
still unbound — once `i ≤ b` every later iteration has `i' < i ≤ b` and is
admitted — so no 4-env skip leg exists); the entry4 leg is sliced at the
SECOND outer unfold of a small-`a ≤ b` run (interleave pattern asserted; the
dead `j` and `res` slots — `res` equals `a` there — are generalized by
slot-targeted env substitutions); the inner bound is the OUTER counter
(`j := i`), so the inner-exit leg is stated at the ground drained bound
`j = 0`, from a small-`i` admitted witness; the outer-exit witness INSERTS a
`j` initializer before the While — same env order and ground continuation,
asserted against the entry4-derived `outerCfg4`.""",
         skip3=dict(seeds={"a": 31337, "b": 31344, "res": 31305, "i": 31351},
                    depth=140, conds=["h1 : 0 < i", "h2 : b < i"]),
         prologue=dict(seeds={"a": 31337, "b": 31338}, depth=80),
         entry3=dict(seeds={"a": 31337, "b": 31351, "res": 31305, "i": 31340},
                     depth=160),
         entry4=dict(seeds={"a": 3, "b": 31338}, depth=360, k2=5,
                     state={"res": (3, "slot"), "i": (2, "sub"),
                            "j": (0, "slot")}),
         inner_body=dict(seeds={"a": 31337, "b": 31351, "res": 31305,
                                "i": 31340},
                         depth=240, head={"res": 31306, "j": 31339}),
         inner_exit=dict(seeds={"a": 31337, "b": 31351, "res": 31305, "i": 3},
                         depth=340, mode="ground0", head={"res": 31308}),
         exit_=dict(seeds={"a": 31337, "b": 31338, "res": 31344, "i": -31351,
                           "j": 31305})),
]

WHILE_CTOR = "«While(_,_)"


def kseq_split(kval: str) -> tuple[str, str]:
    """Split a printed `SortK.kseq (ITEM) (TAIL)` k-cell value into
    (ITEM, TAIL) by balanced-paren scan (TAIL loses its outer parens)."""
    pre = "SortK.kseq ("
    assert kval.startswith(pre), kval[:80]
    depth, k = 1, len(pre)
    while depth:
        if kval[k] == "(":
            depth += 1
        elif kval[k] == ")":
            depth -= 1
        k += 1
    item = kval[len(pre):k - 1]
    rest = kval[k + 1:]
    assert rest.startswith("(") and rest.endswith(")"), rest[:80]
    return item, rest[1:-1]


def make_post_tail(needle: str, var: str):
    """make_post_rest generalized: replace the rightmost occurrence of the
    concrete continuation `needle` inside the k cell by the binder `var`."""
    def post(t: str) -> str:
        k_end = t.index(" }, env := ")
        assert needle in t[:k_end], "continuation not found in k cell"
        assert t.count(needle, k_end) == 0, "continuation text outside the k cell"
        i = t.rindex(needle, 0, k_end)
        return t[:i] + var + t[i + len(needle):]
    return post


def make_slot_post(var: str, digits: str, required: bool):
    """Slot-targeted env substitution: `"<var>" (intV <digits>)` becomes the
    binder `var` — for env values whose digits collide with another binder or
    a program constant but are NEVER READ in the leg (asserted implicitly:
    Lean re-checks every step for arbitrary `var`)."""
    old = f'"{var}" ' + VAL_INT.format(digits)
    new = f'"{var}" ' + VAL_INT.format(var)

    def post(t: str) -> str:
        c = t.count(old)
        assert c == 1 if required else c <= 1, f"env slot {var}: {c} occurrences"
        return t.replace(old, new)
    return post


def compose_posts(*fs):
    def post(t: str) -> str:
        for f in fs:
            t = f(t)
        return t
    return post


def gen_nested(eng: Engine, cfg: dict) -> None:
    """Generate <name>Legs.lean for one nested-loop program: an outer
    countdown over an inner drain, optional accumulator(s), inner bound `b`
    or the outer counter `i`, optional guarding branch (c31, + skip3_leg)."""
    name, stem = cfg["name"], cfg["stem"]
    limit = cfg["ground_limit"]
    src = (glt.REPO / "programs" / f"{stem}.py").read_text()
    stock = (ROOT / "build/lean/mpy" / f"{stem}.mpy").read_text()
    params = list(cfg["lits"])
    accs = dict(cfg["accs"])
    i_from = cfg["i_from"]
    bound = cfg["inner_bound"]
    body_out = cfg["body_out"]
    vars0 = params + list(accs) + ["i"]
    varsj = vars0 + ["j"]
    v0_args = " ".join(vars0)
    vj_args = " ".join(varsj)
    in_args = " ".join(params)
    i_anchor = f'Assign(Name("i"), Name("{i_from}"))'
    entry_conds = cfg.get("entry_conds", ["h : 0 < i"])

    def cstr(conds):
        return "".join(f" ({c})" for c in conds)

    def cargs(conds):
        return "".join(" " + c.split(" : ")[0] for c in conds)

    def seeded(seeds: dict) -> str:
        """params via the program's magic literals; accs via their
        initializer anchors; i by rewriting the `i = <param>` initializer;
        j (outer-exit witness only) by inserting an initializer right after
        it (same env order, same ground continuation)."""
        out = stock
        for k, (p, lit) in enumerate(cfg["lits"].items()):
            if p in seeds:
                assert out.count(f"Int({lit})") == 1, (stem, p)
                out = out.replace(f"Int({lit})", f"Int(@{k}@)")
        for k, p in enumerate(cfg["lits"]):
            if p in seeds:
                out = out.replace(f"@{k}@", str(seeds[p]))
        for acc, lit in accs.items():
            if acc in seeds:
                anchor = f'Assign(Name("{acc}"), Int({lit}))'
                assert out.count(anchor) == 1, (stem, anchor)
                out = out.replace(anchor,
                                  f'Assign(Name("{acc}"), Int({seeds[acc]}))')
        if "i" in seeds:
            repl = f'Assign(Name("i"), Int({seeds["i"]}))'
            if "j" in seeds:
                repl += f'\n  Assign(Name("j"), Int({seeds["j"]}))'
            assert out.count(i_anchor) == 1, (stem, i_anchor)
            out = out.replace(i_anchor, repl)
        else:
            assert "j" not in seeds
        return out

    def nsubs(seeds: dict, vals: list[str] | None = None) -> tuple[list, tuple]:
        """Digit->binder substitutions keyed by BINDER NAME (`seeds` maps the
        leg's binder names to witness values; `vals` are computed closed
        forms evaluated over those binders)."""
        pairs, gone = [], set()
        for nm, v in seeds.items():
            d = digits_of(v)
            pairs += [(INT_LIT.format(d), INT_LIT.format(nm)),
                      (VAL_INT.format(d), VAL_INT.format(nm))]
            gone.add(f"» {d})")
        seen = {digits_of(v) for v in seeds.values()}
        for expr in (vals or []):
            v = eval(expr, {}, dict(seeds))
            d = digits_of(v)
            assert d not in seen, f"{stem}: computed {expr} = {v} collides"
            seen.add(d)
            pairs.append((VAL_INT.format(d), VAL_INT.format(expr)))
            gone.add(f"» {d})")
        check_no_collisions(pairs, limit)
        pairs.sort(key=lambda s: len(s[0]), reverse=True)
        return pairs, tuple(sorted(gone, key=len, reverse=True))

    def nilframe(r: str) -> str:
        return "SortK.kseq (SortKItem.inj_SortStmts " + NILSTMTS + ") " + r

    def inst(body: str, slots: dict[str, str], rest_old: str, rest_new: str) -> str:
        """Config-def body instantiated at slot expressions (two-stage
        placeholders: instances may repeat binders, e.g. j := b)."""
        t = body.replace(rest_old, "@R@")
        for k, v in enumerate(slots):
            t = t.replace(VAL_INT.format(v), f"@V{k}@")
        for k, (v, e) in enumerate(slots.items()):
            t = t.replace(f"@V{k}@", VAL_INT.format(e))
        return t.replace("@R@", rest_new)

    def ident(extra: dict[str, str]) -> dict[str, str]:
        """Identity slot map over varsj (or vars0 keys of `extra`), updated."""
        return {**{v: v for v in varsj}, **extra}

    def slot_text(v: str, val) -> str:
        return f'"{v}" ' + VAL_INT.format(digits_of(val) if isinstance(val, int) else val)

    # ---- outer-exit witness (i < 0 seed + inserted j initializer): guard
    # false at the ONLY unfold; yields outerRest0 (= s0), the exit leg, the
    # epilogue, and the outer While head text
    ex = cfg["exit_"]
    ex_path, ex_rules = eng.rules_for(f"{stem}_exit", seeded(ex["seeds"]), None)
    ewu = wu_indexes(ex_rules)
    assert len(ewu) == 1, f"{stem}: exit witness ran {len(ewu)} unfolds"
    lo = ewu[0]
    sd = next(k for k in range(lo, len(ex_rules)) if ex_rules[k] == "seqDone")
    boundary = sd + 1
    ex_kp, ex_raw = eng.prints(glp.sweep_range(ex_path, lo, len(ex_rules)))
    s0 = glp.kval_of(ex_raw[boundary - lo])
    w_out, ex_tail = kseq_split(glp.kval_of(ex_raw[0]))
    assert ex_tail == s0, f"{stem}: exit-witness tail is not the ground continuation"
    assert w_out.count(WHILE_CTOR) == 2, f"{stem}: outer While head shape"
    post_rest0 = make_post_tail(s0, "rest")
    ex_subs, ex_gone = nsubs(ex["seeds"])
    exit_ct, exit_steps, n_exit = eng.build(
        ex_kp[:boundary - lo + 1], ex_raw[:boundary - lo + 1],
        ex_rules[lo:boundary], ex_subs, ex_gone, limit, post=post_rest0)
    epi_ct, epi_steps, n_epi = eng.build(
        ex_kp[boundary - lo:], ex_raw[boundary - lo:],
        ex_rules[boundary:], ex_subs, ex_gone, limit)
    assert n_epi >= 1, f"{stem}: empty epilogue"
    outerexit_body = exit_ct[-1]
    assert outerexit_body.count("{ val := rest }") == 1
    assert epi_ct[0] == outerexit_body.replace(
        "{ val := rest }", "{ val := " + s0 + " }"), \
        f"{stem}: epilogue start vs outerExit at outerRest0"
    final_body = epi_ct[-1]
    for v in varsj:
        assert final_body.count(VAL_INT.format(v)) == 1, \
            f"{stem}: final slot {v} not unique"

    # ---- prologue: stock program, start .. first outer unfold
    pro = cfg["prologue"]
    pro_path, pro_rules = eng.rules_for(f"{stem}_pro", seeded(pro["seeds"]),
                                        pro.get("depth", 60))
    pwu = wu_indexes(pro_rules)
    assert pwu, f"{stem}: no unfold at prologue witness"
    pro_kp, pro_raw = eng.prints(glp.sweep_range(pro_path, 0, pwu[0]))
    pro_subs, pro_gone = nsubs(pro["seeds"])
    pro_ct, pro_steps, n_pro = eng.build(pro_kp, pro_raw, pro_rules[:pwu[0]],
                                         pro_subs, pro_gone, limit)
    init_body = pro_ct[0]

    # ---- entry3: first outer unfold .. first inner unfold (j-unbound
    # witness, i seeded independent of its source param); yields outerCfg3,
    # midK, and the inner While head
    e3 = cfg["entry3"]
    e3_path, e3_rules = eng.rules_for(f"{stem}_entry3", seeded(e3["seeds"]),
                                      e3.get("depth", 120))
    e3wu = wu_indexes(e3_rules)
    assert len(e3wu) >= 2, f"{stem}: <2 unfolds at entry3 witness"
    e3_kp, e3_raw = eng.prints(glp.sweep_range(e3_path, e3wu[0], e3wu[1]))
    head3, tail3 = kseq_split(glp.kval_of(e3_raw[0]))
    assert head3 == w_out and tail3 == s0, f"{stem}: entry3 slice start shape"
    w_in, e3_end_tail = kseq_split(glp.kval_of(e3_raw[-1]))
    assert w_in.count(WHILE_CTOR) == 1, f"{stem}: inner While head shape"
    e3_subs, e3_gone = nsubs(e3["seeds"])
    e3_ct, e3_steps, n_e3 = eng.build(e3_kp, e3_raw, e3_rules[e3wu[0]:e3wu[1]],
                                      e3_subs, e3_gone, limit, post=post_rest0)
    outercfg3_body = e3_ct[0]
    for v in vars0:
        assert outercfg3_body.count(VAL_INT.format(v)) == 1, \
            f"{stem}: outerCfg3 slot {v} not unique"
    assert outercfg3_body.count("(rest)") == 1
    # midK: the concrete mid-continuation below the inner While
    head3e, mid_rest = kseq_split(glp.kval_of(e3_ct[-1]))
    assert head3e == w_in
    assert mid_rest.count("(rest)") == 1, f"{stem}: midK rest slot not unique"
    midk_body = mid_rest.replace("(rest)", "rest")
    assert midk_body.count(WHILE_CTOR) == 2, f"{stem}: midK carries the outer While"

    def midk_exp(r: str) -> str:
        return mid_rest.replace("(rest)", r)

    assert e3_end_tail == midk_exp("(" + s0 + ")"), \
        f"{stem}: entry3-end tail vs midK at outerRest0"

    # ---- skip3 (c31): one refused-branch outer iteration, first unfold ..
    # second unfold (both outer; no inner unfold in between)
    sk = cfg.get("skip3")
    if sk:
        sk_path, sk_rules = eng.rules_for(f"{stem}_skip3", seeded(sk["seeds"]),
                                          sk.get("depth", 140))
        skwu = wu_indexes(sk_rules)
        assert len(skwu) >= 2, f"{stem}: <2 unfolds at skip3 witness"
        sk_kp, sk_raw = eng.prints(glp.sweep_range(sk_path, skwu[0], skwu[1]))
        headsk, tailsk = kseq_split(glp.kval_of(sk_raw[0]))
        assert headsk == w_out and tailsk == s0, f"{stem}: skip3 slice start shape"
        headsk2, _ = kseq_split(glp.kval_of(sk_raw[-1]))
        assert headsk2 == w_out, f"{stem}: skip3 does not end at the outer While"
        sk_subs, sk_gone = nsubs(sk["seeds"], vals=["(i - 1)"])
        sk_ct, sk_steps, n_sk = eng.build(sk_kp, sk_raw,
                                          sk_rules[skwu[0]:skwu[1]],
                                          sk_subs, sk_gone, limit,
                                          post=post_rest0)
        assert sk_ct[0] == outercfg3_body, f"{stem}: skip3 start vs outerCfg3"
        assert sk_ct[-1] == inst(outercfg3_body,
                                 {**{v: v for v in vars0}, "i": "(i - 1)"},
                                 "(rest)", "(" + nilframe("(rest)") + ")"), \
            f"{stem}: skip3 end vs outerCfg3 at (i - 1, nilK rest)"

    # ---- entry4: small-bound seeds; slice at the SECOND outer unfold
    e4 = cfg["entry4"]
    e4_path, e4_rules = eng.rules_for(f"{stem}_entry4", seeded(e4["seeds"]),
                                      e4.get("depth", 260))
    e4wu = wu_indexes(e4_rules)
    k2 = e4["k2"]
    assert len(e4wu) >= k2 + 2, \
        f"{stem}: {len(e4wu)} unfolds at entry4 witness, need {k2 + 2}"
    e4_kp, e4_raw = eng.prints(glp.sweep_range(e4_path, e4wu[k2], e4wu[k2 + 1]))
    head4, tail4 = kseq_split(glp.kval_of(e4_raw[0]))
    assert head4 == w_out, f"{stem}: entry4 slice does not start at the outer While"
    assert tail4 == nilframe("(" + s0 + ")"), \
        f"{stem}: entry4 tail is not one residue frame over outerRest0"
    sub_seeds = {p: e4["seeds"][p] for p in params}
    e4_posts = []
    for v, (val, how) in e4["state"].items():
        assert slot_text(v, val) in e4_raw[0], \
            f"{stem}: entry4 start {v} slot != {val}"
        if how == "slot":
            e4_posts.append(make_slot_post(v, digits_of(val),
                                           required=(v != "j")))
        else:
            sub_seeds[v] = val
    e4_subs, e4_gone = nsubs(sub_seeds)
    e4_ct, e4_steps, n_e4 = eng.build(
        e4_kp, e4_raw, e4_rules[e4wu[k2]:e4wu[k2 + 1]], e4_subs, e4_gone, limit,
        post=compose_posts(*e4_posts, make_post_tail(tail4, "rest")))
    outercfg4_body = e4_ct[0]
    for v in varsj:
        assert outercfg4_body.count(VAL_INT.format(v)) == 1, \
            f"{stem}: outerCfg4 slot {v} not unique"
    assert outercfg4_body.count("(rest)") == 1

    # ---- inner body: one guard-true inner iteration at the SECOND inner
    # head (j = bound - 1 there, distinct from the bound's own slot)
    ib = cfg["inner_body"]
    ib_path, ib_rules = eng.rules_for(f"{stem}_ibody", seeded(ib["seeds"]),
                                      ib.get("depth", 160))
    ibwu = wu_indexes(ib_rules)
    assert len(ibwu) >= 4, f"{stem}: <4 unfolds at inner-body witness"
    ib_kp, ib_raw = eng.prints(glp.sweep_range(ib_path, ibwu[2], ibwu[3]))
    headb, tailb = kseq_split(glp.kval_of(ib_raw[0]))
    assert headb == w_in, f"{stem}: inner-body slice does not start at the inner While"
    assert tailb == nilframe("(" + midk_exp("(" + s0 + ")") + ")"), \
        f"{stem}: inner-body tail is not one frame over midK outerRest0"
    for v, val in ib["head"].items():
        assert slot_text(v, val) in ib_raw[0], \
            f"{stem}: inner-body head {v} slot != {val}"
    ib_binds = {**ib["seeds"], **ib["head"]}
    ib_vals = [body_out[acc] for acc in accs if acc in body_out] + ["(j - 1)"]
    ib_subs, ib_gone = nsubs(ib_binds, vals=ib_vals)
    ib_ct, ib_steps, n_ib = eng.build(
        ib_kp, ib_raw, ib_rules[ibwu[2]:ibwu[3]], ib_subs, ib_gone, limit,
        post=make_post_tail(tailb, "irest"))
    innercfg_body = ib_ct[0]
    for v in varsj:
        assert innercfg_body.count(VAL_INT.format(v)) == 1, \
            f"{stem}: innerCfg slot {v} not unique"
    assert innercfg_body.count("(irest)") == 1

    # ---- inner exit + post-inner. mode "bneg": j = b < 0 at the FIRST
    # inner head (b's slot pinned, never read; every remaining occurrence of
    # the value is j). mode "ground0" (bound = i): the drained bound j = 0 at
    # the LAST inner head of a small-i witness — j stays GROUND in the exit
    # leg (its k-cell operand copies are textually ambiguous with the guard
    # literal 0), which is the only shape `inner_all` needs under `0 ≤ j`.
    ie = cfg["inner_exit"]
    mode = ie["mode"]
    ie_path, ie_rules = eng.rules_for(f"{stem}_iexit", seeded(ie["seeds"]),
                                      ie.get("depth", 140))
    iewu = wu_indexes(ie_rules)
    xw = 1 if mode == "bneg" else 1 + ie["seeds"]["i"]
    assert len(iewu) >= xw + 2, f"{stem}: {len(iewu)} unfolds at inner-exit witness"
    sd2 = next(k for k in range(iewu[xw], iewu[xw + 1])
               if ie_rules[k] == "seqDone")
    bnd = sd2 + 1
    ie_kp, ie_raw = eng.prints(glp.sweep_range(ie_path, iewu[xw], iewu[xw + 1]))
    headi, taili = kseq_split(glp.kval_of(ie_raw[0]))
    assert headi == w_in, f"{stem}: inner-exit slice does not start at the inner While"
    exp_tail = midk_exp("(" + s0 + ")")
    for _ in range(0 if mode == "bneg" else ie["seeds"]["i"]):
        exp_tail = nilframe("(" + exp_tail + ")")
    assert taili == exp_tail, f"{stem}: inner-exit tail shape"
    if mode == "bneg":
        bneg = ie["seeds"]["b"]
        assert bneg < 0, "inner-exit bneg witness needs b < 0"
        assert slot_text("j", bneg) in ie_raw[0], \
            f"{stem}: inner-exit start j slot != b"
        ie_binds = {k: v for k, v in ie["seeds"].items() if k != "b"}
        ie_binds["j"] = bneg
        ie_posts = [make_slot_post("b", digits_of(bneg), required=True)]
    else:
        assert slot_text("j", 0) in ie_raw[0], \
            f"{stem}: inner-exit start j slot != 0"
        for v, val in ie.get("head", {}).items():
            assert slot_text(v, val) in ie_raw[0], \
                f"{stem}: inner-exit head {v} slot != {val}"
        ie_binds = {**ie["seeds"], **ie.get("head", {})}
        ie_posts = []
    ie_subs, ie_gone = nsubs(ie_binds)
    ie_ct, ie_steps, n_ie = eng.build(
        ie_kp[:bnd - iewu[xw] + 1], ie_raw[:bnd - iewu[xw] + 1],
        ie_rules[iewu[xw]:bnd], ie_subs, ie_gone, limit,
        post=compose_posts(*ie_posts, make_post_tail(taili, "irest")))
    if mode == "bneg":
        innerexit_body = ie_ct[-1]
    else:
        jslot = slot_text("j", 0)
        assert ie_ct[-1].count(jslot) == 1
        innerexit_body = ie_ct[-1].replace(jslot, '"j" ' + VAL_INT.format("j"))
    assert innerexit_body.count("{ val := irest }") == 1
    # ground0: the witness's inner run left i nil frames below the inner
    # While — the machine drains them by seqDone right after the inner exit,
    # but in the derivation `inner_all` drains them INTERNALLY (one
    # inner_nil_step per fuel layer), so post_inner_leg starts AFTER the
    # drain, at the bare mid-continuation
    pi_lo = bnd
    if mode == "ground0":
        drain = ie["seeds"]["i"]
        assert ie_rules[bnd:bnd + drain] == ["seqDone"] * drain, \
            f"{stem}: expected {drain} inner-residue seqDones after the inner exit"
        pi_lo = bnd + drain
        assert glp.kval_of(ie_raw[pi_lo - iewu[xw]]) == midk_exp("(" + s0 + ")"), \
            f"{stem}: post-inner start k is not midK outerRest0 after the drain"
    pi_posts = list(ie_posts)
    if mode == "ground0":
        pi_posts.append(make_slot_post("j", "0", required=True))
    pi_subs, pi_gone = nsubs(ie_binds, vals=["(i - 1)"])
    pi_ct, pi_steps, n_pi = eng.build(
        ie_kp[pi_lo - iewu[xw]:], ie_raw[pi_lo - iewu[xw]:],
        ie_rules[pi_lo:iewu[xw + 1]], pi_subs, pi_gone, limit,
        post=compose_posts(*pi_posts, post_rest0))

    # ---- endpoint cross-asserts (text-level; the derivation's tran-folds
    # rely on exactly these definitional equalities)
    assert pro_ct[-1] == inst(
        outercfg3_body,
        {v: ("0" if v in accs else (i_from if v == "i" else v)) for v in vars0},
        "(rest)", "(" + s0 + ")"), \
        f"{stem}: prologue end vs outerCfg3 at the entry instance"
    inner_at_entry = inst(innercfg_body, ident({"j": bound}),
                          "(irest)", "(" + midk_exp("(rest)") + ")")
    assert e3_ct[-1] == inner_at_entry, \
        f"{stem}: entry3 end vs innerCfg at j := {bound} (midK rest)"
    assert e4_ct[-1] == inner_at_entry, \
        f"{stem}: entry4 end vs innerCfg at j := {bound} (midK rest)"
    assert ib_ct[-1] == inst(innercfg_body,
                             {v: body_out.get(v, v) for v in varsj},
                             "(irest)", "(" + nilframe("(irest)") + ")"), \
        f"{stem}: inner-body end vs innerCfg at the out instance (nilK irest)"
    if mode == "bneg":
        assert ie_ct[0] == innercfg_body, f"{stem}: inner-exit start vs innerCfg"
    else:
        assert ie_ct[0] == inst(innercfg_body, ident({"j": "0"}),
                                "(irest)", "(irest)"), \
            f"{stem}: inner-exit start vs innerCfg at j := 0"
    assert pi_ct[0] == innerexit_body.replace(
        "{ val := irest }", "{ val := " + midk_exp("(rest)") + " }"), \
        f"{stem}: post-inner start vs innerExit at midK rest"
    assert pi_ct[-1] == inst(outercfg4_body, ident({"i": "(i - 1)"}),
                             "(rest)", "(" + nilframe("(rest)") + ")"), \
        f"{stem}: post-inner end vs outerCfg4 at (i - 1, nilK rest)"
    assert exit_ct[0] == outercfg4_body, \
        f"{stem}: exit start vs outerCfg4 (insertion witness shape)"

    # ---- emission
    v0p = f"({v0_args} : SortInt)"
    vjp = f"({vj_args} : SortInt)"
    sections, counts = [], []

    def emit(tag, thm, vp, va, cond, harg, src_ref, dst_ref, ct, steps, n, doc):
        defs, fold = glp.emit_path(tag, vp, va, vp + cond, va + harg,
                                   src_ref, dst_ref, ct, steps, n)
        rec = f"set_option maxRecDepth {max(2048, 16 * n)} in\n"
        sections.append(f"""{defs}
{rec}/-- {doc} -/
theorem {thm} {vp}{cond} :
    Rewrites {src_ref} {dst_ref} :=
  {fold}
""")
        counts.append((thm, n))

    pro_inst = " ".join("0" if v in accs else (i_from if v == "i" else v)
                        for v in vars0)
    emit("prologue", "prologue_leg", f"({in_args} : SortInt)", in_args, "", "",
         f"(init {in_args})", f"(outerCfg3 {pro_inst} outerRest0)",
         pro_ct, pro_steps, n_pro,
         f"Program start to the first outer loop head: `i := {i_from}`, "
         f"{len(vars0)}-entry env.")
    entry_dst = f"(innerCfg {v0_args} {bound} (midK rest))"
    emit("entry3", "entry3_leg", v0p + " (rest : SortK)", v0_args + " rest",
         cstr(entry_conds), cargs(entry_conds),
         f"(outerCfg3 {v0_args} rest)", entry_dst,
         e3_ct, e3_steps, n_e3,
         cfg.get("doc3",
                 "First-arrival outer iteration head into the inner loop head: guard\n"
                 f"true, `j := {bound}` (binding j — the env grows to {len(varsj)} entries), the inner\n"
                 "While heated over the concrete mid-continuation `midK rest`."))
    emit("entry4", "entry4_leg", vjp + " (rest : SortK)", vj_args + " rest",
         cstr(entry_conds), cargs(entry_conds),
         f"(outerCfg4 {vj_args} rest)", entry_dst,
         e4_ct, e4_steps, n_e4,
         cfg.get("doc4",
                 "Subsequent-arrival outer iteration head into the inner loop head\n"
                 f"({len(varsj)}-entry env, `j` dead on entry): guard true, `j := {bound}`, the inner\n"
                 "While heated over `midK rest`."))
    if sk:
        skip_dst_args = " ".join("(i - 1)" if v == "i" else v for v in vars0)
        emit("skip3", "skip3_leg", v0p + " (rest : SortK)", v0_args + " rest",
             cstr(sk["conds"]), cargs(sk["conds"]),
             f"(outerCfg3 {v0_args} rest)",
             f"(outerCfg3 {skip_dst_args} (" + nilframe("rest") + "))",
             sk_ct, sk_steps, n_sk,
             "One SKIPPED outer iteration (branch `b < i` refused): only `i -= 1`,\n"
             "leaving one residue frame; the env keeps its j-unbound shape.")
    ib_dst_args = " ".join(body_out.get(v, v) for v in varsj)
    emit("ibody", "inner_body_leg", vjp + " (irest : SortK)", vj_args + " irest",
         " (h : 0 < j)", " h",
         f"(innerCfg {vj_args} irest)",
         f"(innerCfg {ib_dst_args} (" + nilframe("irest") + "))",
         ib_ct, ib_steps, n_ib,
         f"One inner iteration: guard true, {cfg.get('body_doc', '`j -= 1`')}; the unfolded inner block\n"
         "leaves one residue frame on the inner continuation.")
    if mode == "bneg":
        emit("iexit", "inner_exit_leg", vjp + " (irest : SortK)",
             vj_args + " irest", " (h : j ≤ 0)", " h",
             f"(innerCfg {vj_args} irest)", f"(innerExit {vj_args} irest)",
             ie_ct, ie_steps, n_ie,
             "Inner loop exit: guard false, the exiting unfold's residue popped;\n"
             "the k cell becomes the inner continuation `irest`.")
    else:
        emit("iexit", "inner_exit_leg", v0p + " (irest : SortK)",
             v0_args + " irest", "", "",
             f"(innerCfg {v0_args} 0 irest)", f"(innerExit {v0_args} 0 irest)",
             ie_ct, ie_steps, n_ie,
             "Inner loop exit at the drained bound `j = 0` — the only inner-exit\n"
             "shape reached with the bound `j := i ≥ 1` (ground `j` sidesteps the\n"
             "0-literal operand ambiguity; `inner_all` needs only `0 ≤ j`): residue\n"
             "popped, the k cell becomes the inner continuation `irest`.")
    pi_dst_args = " ".join("(i - 1)" if v == "i" else v for v in varsj)
    emit("postin", "post_inner_leg", vjp + " (rest : SortK)", vj_args + " rest",
         "", "",
         f"(innerExit {vj_args} (midK rest))",
         f"(outerCfg4 {pi_dst_args} (" + nilframe("rest") + "))",
         pi_ct, pi_steps, n_pi,
         cfg.get("postin_doc",
                 "From the drained inner loop at the concrete mid-continuation:\n"
                 "`i -= 1` and the outer While heats — one residue frame per\n"
                 "completed outer iteration."))
    emit("exitp", "exit_leg", vjp + " (rest : SortK)", vj_args + " rest",
         " (h : i ≤ 0)", " h",
         f"(outerCfg4 {vj_args} rest)", f"(outerExit {vj_args} rest)",
         exit_ct, exit_steps, n_exit,
         "Outer loop exit: guard false, residue popped, k cell = `rest`.")
    emit("epilogue", "epilogue_leg", vjp, vj_args, "", "",
         f"(outerExit {vj_args} outerRest0)", f"(final {vj_args})",
         epi_ct, epi_steps, n_epi,
         "From the outer exit at the ground continuation to the terminal\n"
         "configuration (the module tail's final `seqDone`).")

    midk_doc = cfg.get("midk_doc",
                       "(the outer body's tail below the inner While: `[i = i - 1]` and the re-heated\n"
                       "outer While over `rest`)")
    midk_def_doc = cfg.get("midk_def_doc",
                           "The concrete continuation below the INNER While inside the outer body:\n"
                           "the outer block's remaining statements (`i = i - 1`, then the outer While\n"
                           "loop-back) over the outer continuation `rest`.")
    counts_doc = ", ".join(f"{t} {n}" for t, n in counts)
    body_txt = f"""import KMiniPy.Relations

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false  -- uniform leg binders; hyps used only on guard steps

/-! {name}Legs: PROVED parametric execution legs for `{stem}` — the NESTED-loop
stage. The reachability-logic derivation ({name}.lean) keeps ONE Circularity
(the outer loop, over `outerCfg4`) and summarizes the whole inner loop as a
∀-quantified `Rewrites` lemma proved by fuel induction from `inner_body_leg` /
`inner_exit_leg` / `inner_nil_step`.

Two outer loop-head shapes (the env assoc-list grows when `j` is first bound
inside the first outer iteration): `outerCfg3 {v0_args} rest` at first arrival,
`outerCfg4 {vj_args} rest` afterwards. The inner configs take an opaque
`irest : SortK`; in the composition it is always the concrete `midK rest`
{midk_doc}.

Witness surgeries beyond the single-loop engine (each Lean-re-checked, all
endpoints cross-asserted): {cfg["surgery_doc"]}
Program (CPython-validated against the same K semantics):
{chr(10).join('    ' + l for l in src.rstrip().splitlines())}
Proof: tran-folds of {counts_doc} steps; each nil_step is one `seqDone`.
-/

namespace {name}Legs

def init ({in_args} : SortInt) : SortGeneratedTopCell :=
  {init_body}

def final {vjp} : SortGeneratedTopCell :=
  {final_body}

/-- The ground continuation below the OUTER While on loop entry: the emptied
module statement list over the empty k cell. -/
def outerRest0 : SortK :=
  {s0}

/-- {midk_def_doc} -/
def midK (rest : SortK) : SortK :=
  {midk_body}

/-- Outer loop head at FIRST arrival: `j` not yet bound ({len(vars0)}-entry env). -/
def outerCfg3 {v0p} (rest : SortK) : SortGeneratedTopCell :=
  {outercfg3_body}

/-- Outer loop head at every LATER arrival: `j` bound ({len(varsj)}-entry env). -/
def outerCfg4 {vjp} (rest : SortK) : SortGeneratedTopCell :=
  {outercfg4_body}

/-- Inner loop head: the inner While over the inner continuation `irest`. -/
def innerCfg {vjp} (irest : SortK) : SortGeneratedTopCell :=
  {innercfg_body}

/-- Inner post-loop configuration: inner guard false, residue popped, the k
cell IS the inner continuation `irest`. -/
def innerExit {vjp} (irest : SortK) : SortGeneratedTopCell :=
  {innerexit_body}

/-- Outer post-loop configuration: outer guard false, residue popped, k =
`rest`. -/
def outerExit {vjp} (rest : SortK) : SortGeneratedTopCell :=
  {outerexit_body}

/-- Pops one INNER residue frame (`seqDone`). -/
theorem inner_nil_step {vjp} (irest : SortK) :
    Rewrites (innerExit {vj_args} ({nilframe("irest")}))
      (innerExit {vj_args} irest) :=
  Rewrites.seqDone

/-- Pops one OUTER residue frame (`seqDone`). -/
theorem nil_step {vjp} (rest : SortK) :
    Rewrites (outerExit {vj_args} ({nilframe("rest")}))
      (outerExit {vj_args} rest) :=
  Rewrites.seqDone

{chr(10).join(sections)}
end {name}Legs
"""
    out = PKG / "KMiniPy" / "Verification" / f"{name}Legs.lean"
    out.write_text(body_txt)
    print(f"[ok] {name}Legs: proved, {counts_doc}")

def main() -> int:
    only = ([a for a in sys.argv[sys.argv.index("--only") + 1:] if not a.startswith("-")]
            if "--only" in sys.argv else None)
    glp.check_simp_names()
    printer = glt.load_printer()
    arities = glt.ctor_arities(PKG / "KMiniPy" / "Rewrite.lean")
    ord2label = glt.ordinal_to_label(glt.HINTS_DEFN)
    rule_by_label = {glt._rule_name(r): r for r in printer.defn.rewrites}
    eng = Engine(printer, arities, ord2label, rule_by_label)
    for cfg in KB_LOOPS:
        if only is not None and cfg["name"] not in only:
            continue
        gen_one(eng, cfg)
    for cfg in KB_NESTED:
        if only is not None and cfg["name"] not in only:
            continue
        gen_nested(eng, cfg)
    return 0


if __name__ == "__main__":
    sys.exit(main())
