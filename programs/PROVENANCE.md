# Provenance of ported programs (kb_*)

Programs prefixed `kb_` are ported from **KleverBench**, a benchmark of
auto-formalization problems: each problem is a tiny IMP program plus a reference
K reachability claim characterizing its exact final state.

- Source: https://github.com/nlp-research-rosu/KleverBench
- Git SHA: b5eced33b16d13b28b9998f05e7b7e945f2fb482
- Date ported: 2026-08-31
- Nothing is vendored. Each problem's IMP program (state variables pre-bound to
  integers) is translated to module-level MiniPy: inputs become module bindings
  initialized to the magic literals 31337/31338/31339 (replaced by symbolic
  integers in the specs), and IMP idioms are written as idiomatic Python
  (`!(n <= 0)` → `0 < n`, `n + -1` → `n - 1`, `/` → `//`); dead initial
  bindings (overwritten before any read) are dropped. The reference claim is
  restated over the vendored MPY semantics in `corpus/specs/kb-<problem>/` as a
  full-characterization claim: every binding the program creates is pinned to
  its exact final value. Each verification record carries the upstream problem
  id and original IMP text in `provenance.upstream`.

| program | KleverBench problem | tier |
|---|---|---|
| kb_assign.py | problems/imp/assign | 1 |
| kb_swap.py | problems/imp/swap | 1 |
| kb_chain.py | problems/imp/chain | 1 |
| kb_double_half.py | problems/imp/double-half | 1 |
| kb_arith_mix.py | problems/imp/arith-mix | 1 |
| kb_abs.py | problems/imp/abs | 2 |
| kb_max.py | problems/imp/max | 2 |
| kb_min.py | problems/imp/min | 2 |
| kb_countdown.py | problems/imp/countdown | 2 |
| kb_countup.py | problems/imp/countup | 2 |
| kb_sum.py | problems/imp/sum | 2 |
| kb_add_loop.py | problems/imp/add-loop | 2 |
| kb_sub_loop.py | problems/imp/sub-loop | 2 |
| kb_max3.py | problems/imp/max3 | 3 |
| kb_clamp.py | problems/imp/clamp | 3 |
| kb_abs_times.py | problems/imp/abs-times | 3 |
| kb_sumdiff.py | problems/imp/sumdiff | 3 |
| kb_mult_loop.py | problems/imp/mult-loop | 3 |
| kb_triangle_down.py | problems/imp/triangle-down | 3 |
| kb_sum_up.py | problems/imp/sum-up | 3 |
| kb_count_even.py | problems/imp/count-even | 3 |
| kb_loop_max.py | problems/imp/loop-max | 3 |
| kb_pure_nested.py | problems/imp/pure-nested | 4 |
| kb_mult_nested.py | problems/imp/mult-nested | 4 |
| kb_triangle_nested.py | problems/imp/triangle-nested | 4 |
| kb_squares_cubic.py | problems/imp/squares-cubic | 4 |
| kb_rows_sum_nested.py | problems/imp/rows-sum-nested | 4 |
| kb_nested_with_branch.py | problems/imp/nested-with-branch | 4 |
| kb_pipeline.py | problems/imp/pipeline | 5 |
| kb_stats_pipeline.py | problems/imp/stats-pipeline | 5 |
| kb_normalize_count.py | problems/imp/normalize-count | 5 |

The tier-4 nested-loop programs use the smaller magic literals 137/138 (noted per
record) so their concrete witness runs stay instant; everything else uses the
standard 31337/31338/31339.
