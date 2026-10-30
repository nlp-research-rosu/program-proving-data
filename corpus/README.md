# sample-data: machine-checked program-reasoning data for code models

Forty reasoning samples over thirty-nine tiny Python programs — each sample a
machine-generated, machine-checked record of one of the three kinds of reasoning one can
do about code:

- **how it runs** — a complete execution trace, every step labeled with the exact language
  rule that produced it;
- **how it runs on every input at once** — a symbolic execution tree: each feasible path
  through the program, the condition on the inputs that selects it, a concrete witness input
  per path, and impossibility proofs for the infeasible branches;
- **whether it is correct** — a formal spec with a machine-found proof (a loop invariant, a
  functional spec), plus one deliberately buggy program whose spec is refuted with a concrete
  counterexample run.

**Why this exists, in AI terms.** Execution traces are how recent code models learn to
*simulate* programs — the mid-training data of Meta's Code World Model
([CWM](https://arxiv.org/abs/2510.02387)) is line-level Python traces logged by an
instrumented interpreter. The records here are that shape of data with a stronger guarantee:
they are derived from a single **formal semantics** — a machine-executable rulebook for the
language, written in the [K framework](https://kframework.org) — and machine-checked end to
end. Nothing is hand-labeled; nothing came out of a model. Concretely:

- every trace step carries the semantic rule that caused it — supervision for *why* the state
  changed, not just what it changed to;
- everything is independently validated: traces replay against CPython, each symbolic path
  re-runs its witness input, every proof verdict is checked;
- the strongest tier is fully formal: the Lean package below re-verifies every theorem on any
  machine with one command — trust rests on a proof checker, not on the authors;
- the recipe is generic: programs in, records out, for anything the semantics covers.

## The two data products

- **K data** ([corpus/k/](k/)): the JSON records — execution traces annotated with the
  semantic rule behind every step, symbolic execution trees with path conditions and solver
  witnesses, and verification records: specs, a loop invariant, and a refutation tied to its
  counterexample run. Per sample: `.jsonl` (canonical) + `.md` (readable).
- **Lean data** ([corpus/lean/](lean/)): the same claims as mathematics — a package for
  [Lean 4](https://lean-lang.org) (a proof assistant: a program that mechanically checks
  proofs). The semantics is translated by klean (K's Lean backend); program properties are
  theorems over it, each with a complete machine-checked proof. `lake build` replays
  everything — no K toolchain needed.

## The samples

### The nine original samples (a1–c3)

| program | K data | Lean theorems |
|---|---|---|
| [sum_to_n](../programs/sum_to_n.py) | [concrete trace](k/concrete/a1_sum_to_n.md) | [224-step execution, proved](lean/KMiniPy/Concrete/A1SumToN.lean) · [Gauss form ∀ n ≥ 0, derived in reachability logic](lean/KMiniPy/Verification/C1SumToN.lean) |
| [gcd](../programs/gcd.py) | [concrete trace](k/concrete/a2_gcd.md) | [138-step execution, proved](lean/KMiniPy/Concrete/A2Gcd.lean) |
| [collatz_steps](../programs/collatz_steps.py) | [concrete trace](k/concrete/a3_collatz_steps.md) | [491-step execution, proved](lean/KMiniPy/Concrete/A3CollatzSteps.lean) |
| [half_of_even](../programs/half_of_even.py) | [concrete trace to assert-fail](k/concrete/a4_half_of_even.md) | [29-step execution to assert-failure, proved](lean/KMiniPy/Concrete/A4HalfOfEven.lean) |
| [abs_val](../programs/abs_val.py) | [symbolic tree](k/symbolic/b1_abs_val.md) · [spec, proved](k/verification/c2_abs_val.md) | [per-path ∀ theorems, proved](lean/KMiniPy/Symbolic/B1AbsVal.lean) · [functional spec, derived in reachability logic](lean/KMiniPy/Verification/C2AbsVal.lean) |
| [classify_triangle](../programs/classify_triangle.py) | [symbolic tree, 5 paths + 3 infeasible](k/symbolic/b2_classify_triangle.md) | [5 path theorems ∀ a b c, proved](lean/KMiniPy/Symbolic/B2ClassifyTriangle.lean) |
| [buggy_abs](../programs/buggy_abs.py) | [spec refuted + counterexample](k/verification/c3_buggy_abs.md) | [46-step trace at x = 0, proved](lean/KMiniPy/Verification/C3BuggyAbsAt0.lean) · [refutation ∃ x, proved](lean/KMiniPy/Verification/C3Refutation.lean) |
| range_loop (vendored) | [loop invariant, proved](k/verification/c1_range_loop.md) | — |

### The KleverBench port (samples c4–c34)

All 31 problems of the [KleverBench](https://github.com/nlp-research-rosu/KleverBench) IMP
seed set — upstream pin and translation rules in
[programs/PROVENANCE.md](../programs/PROVENANCE.md) — each proved TWICE. On the K side,
kprove proves a full-characterization reachability claim: the ENTIRE final state pinned as
closed forms of the symbolic inputs, loops handled by circularity claims (one invariant
per loop level). On the Lean side, the same claim is derived in reachability logic over
generated parametric execution legs: the loop-free tier as ∀-quantified path theorems
entering through Axiom (with Case Analysis over branches), every loop program as a
machine-checked **Circularity** derivation (invariants in omega-friendly additive form;
piecewise `min`/`max` posts split by Case Analysis), and the nested-loop tier with the
outer invariant as the Circularity mirror while the inner loop enters as a ∀-quantified
execution lemma proved by fuel induction. Every cell below is machine-checked — kprove
verdict on the K side, `lake build` plus the 85-theorem axiom audit on the Lean side.

| tier | program | K data | Lean theorems |
|---|---|---|---|
| 1 · straight-line | [kb_assign](../programs/kb_assign.py) | [c4](k/verification/c4_kb_assign.md) | [C4KbAssign](lean/KMiniPy/Verification/C4KbAssign.lean) |
| | [kb_swap](../programs/kb_swap.py) | [c5](k/verification/c5_kb_swap.md) | [C5KbSwap](lean/KMiniPy/Verification/C5KbSwap.lean) |
| | [kb_chain](../programs/kb_chain.py) | [c6](k/verification/c6_kb_chain.md) | [C6KbChain](lean/KMiniPy/Verification/C6KbChain.lean) |
| | [kb_double_half](../programs/kb_double_half.py) | [c7](k/verification/c7_kb_double_half.md) | [C7KbDoubleHalf](lean/KMiniPy/Verification/C7KbDoubleHalf.lean) |
| | [kb_arith_mix](../programs/kb_arith_mix.py) | [c8](k/verification/c8_kb_arith_mix.md) | [C8KbArithMix](lean/KMiniPy/Verification/C8KbArithMix.lean) |
| 2 · single branch or loop | [kb_abs](../programs/kb_abs.py) | [c9](k/verification/c9_kb_abs.md) | [C9KbAbs](lean/KMiniPy/Verification/C9KbAbs.lean) |
| | [kb_max](../programs/kb_max.py) | [c10](k/verification/c10_kb_max.md) | [C10KbMax](lean/KMiniPy/Verification/C10KbMax.lean) |
| | [kb_min](../programs/kb_min.py) | [c11](k/verification/c11_kb_min.md) | [C11KbMin](lean/KMiniPy/Verification/C11KbMin.lean) |
| | [kb_countdown](../programs/kb_countdown.py) | [c12](k/verification/c12_kb_countdown.md) | [C12KbCountdown](lean/KMiniPy/Verification/C12KbCountdown.lean) |
| | [kb_countup](../programs/kb_countup.py) | [c13](k/verification/c13_kb_countup.md) | [C13KbCountup](lean/KMiniPy/Verification/C13KbCountup.lean) |
| | [kb_sum](../programs/kb_sum.py) | [c14](k/verification/c14_kb_sum.md) | [C14KbSum](lean/KMiniPy/Verification/C14KbSum.lean) |
| | [kb_add_loop](../programs/kb_add_loop.py) | [c15](k/verification/c15_kb_add_loop.md) | [C15KbAddLoop](lean/KMiniPy/Verification/C15KbAddLoop.lean) |
| | [kb_sub_loop](../programs/kb_sub_loop.py) | [c16](k/verification/c16_kb_sub_loop.md) | [C16KbSubLoop](lean/KMiniPy/Verification/C16KbSubLoop.lean) |
| 3 · mixed control | [kb_max3](../programs/kb_max3.py) | [c17](k/verification/c17_kb_max3.md) | [C17KbMax3](lean/KMiniPy/Verification/C17KbMax3.lean) |
| | [kb_clamp](../programs/kb_clamp.py) | [c18](k/verification/c18_kb_clamp.md) | [C18KbClamp](lean/KMiniPy/Verification/C18KbClamp.lean) |
| | [kb_abs_times](../programs/kb_abs_times.py) | [c19](k/verification/c19_kb_abs_times.md) | [C19KbAbsTimes](lean/KMiniPy/Verification/C19KbAbsTimes.lean) |
| | [kb_sumdiff](../programs/kb_sumdiff.py) | [c20](k/verification/c20_kb_sumdiff.md) | [C20KbSumdiff](lean/KMiniPy/Verification/C20KbSumdiff.lean) |
| | [kb_mult_loop](../programs/kb_mult_loop.py) | [c21](k/verification/c21_kb_mult_loop.md) | [C21KbMultLoop](lean/KMiniPy/Verification/C21KbMultLoop.lean) |
| | [kb_triangle_down](../programs/kb_triangle_down.py) | [c22](k/verification/c22_kb_triangle_down.md) | [C22KbTriangleDown](lean/KMiniPy/Verification/C22KbTriangleDown.lean) |
| | [kb_sum_up](../programs/kb_sum_up.py) | [c23](k/verification/c23_kb_sum_up.md) | [C23KbSumUp](lean/KMiniPy/Verification/C23KbSumUp.lean) |
| | [kb_count_even](../programs/kb_count_even.py) | [c24](k/verification/c24_kb_count_even.md) | [C24KbCountEven](lean/KMiniPy/Verification/C24KbCountEven.lean) |
| | [kb_loop_max](../programs/kb_loop_max.py) | [c25](k/verification/c25_kb_loop_max.md) | [C25KbLoopMax](lean/KMiniPy/Verification/C25KbLoopMax.lean) |
| 4 · nested loops | [kb_pure_nested](../programs/kb_pure_nested.py) | [c26](k/verification/c26_kb_pure_nested.md) | [C26KbPureNested](lean/KMiniPy/Verification/C26KbPureNested.lean) |
| | [kb_mult_nested](../programs/kb_mult_nested.py) | [c27](k/verification/c27_kb_mult_nested.md) | [C27KbMultNested](lean/KMiniPy/Verification/C27KbMultNested.lean) |
| | [kb_triangle_nested](../programs/kb_triangle_nested.py) | [c28](k/verification/c28_kb_triangle_nested.md) | [C28KbTriangleNested](lean/KMiniPy/Verification/C28KbTriangleNested.lean) |
| | [kb_squares_cubic](../programs/kb_squares_cubic.py) | [c29](k/verification/c29_kb_squares_cubic.md) | [C29KbSquaresCubic](lean/KMiniPy/Verification/C29KbSquaresCubic.lean) |
| | [kb_rows_sum_nested](../programs/kb_rows_sum_nested.py) | [c30](k/verification/c30_kb_rows_sum_nested.md) | [C30KbRowsSumNested](lean/KMiniPy/Verification/C30KbRowsSumNested.lean) |
| | [kb_nested_with_branch](../programs/kb_nested_with_branch.py) | [c31](k/verification/c31_kb_nested_with_branch.md) | [C31KbNestedWithBranch](lean/KMiniPy/Verification/C31KbNestedWithBranch.lean) |
| 5 · pipelines | [kb_pipeline](../programs/kb_pipeline.py) | [c32](k/verification/c32_kb_pipeline.md) | [C32KbPipeline](lean/KMiniPy/Verification/C32KbPipeline.lean) |
| | [kb_stats_pipeline](../programs/kb_stats_pipeline.py) | [c33](k/verification/c33_kb_stats_pipeline.md) | [C33KbStatsPipeline](lean/KMiniPy/Verification/C33KbStatsPipeline.lean) |
| | [kb_normalize_count](../programs/kb_normalize_count.py) | [c34](k/verification/c34_kb_normalize_count.md) | [C34KbNormalizeCount](lean/KMiniPy/Verification/C34KbNormalizeCount.lean) |

Every Lean counterpart is proved — the package has no `sorry` (Lean's proof-omitted marker);
[AxiomAudit.lean](lean/KMiniPy/AxiomAudit.lean) prints the axioms under every theorem
(Lean's core axioms plus two documented String-hook declarations, nothing else — a stub
anywhere would surface there as `sorryAx`). Executions are proved as step-by-step rewrite
theorems; specs are derived in reachability logic, the proof calculus of K's own verifier,
encoded in [RL.lean](lean/KMiniPy/RL.lean). The deliberate asymmetries (which program
carries the Lean loop invariant; one-path vs all-path claims) and the full correspondence
table are in [corpus/lean/README.md](lean/README.md).

## Layout

```
corpus/k/          the K dataset: concrete/, symbolic/, verification/
corpus/lean/       the Lean 4 package (lakefile at this root; library KMiniPy)
programs/        the Python subjects
semantics/       mpy-traced/ (klever's MiniPython "MPY" + trace overlay) and minipy-lean.k (klean-ready)
specs/           K claim modules: c2/c3 plus kb-*/ for the 31 ported KleverBench problems
                 (c1's spec ships inside vendor/klever)
scripts/         py2mpy_traced.py frontend; k/ and lean/ generation + validation
docs/            historical plans and the klean feasibility experiment
vendor/klever/   pinned upstream semantics (never modified; sha in VENDOR.md)
build/           (gitignored) kompiled definitions and other derived artifacts
```

## Quickstart

```
make k-validate              # re-check all committed K data against CPython + expectations
cd corpus/lean && lake build   # replay every Lean proof (toolchain pinned; installs via elan)
```

Both run on a fresh clone: `k-validate` needs only `python3`, and `lake build` installs its
pinned Lean via [elan](https://github.com/leanprover/elan). Regenerating the K data needs
K v7.1.337 + pyk + z3 (`make check-env` checks; [REPORT.md](../REPORT.md) has install pointers).

[REPORT.md](../REPORT.md) documents both data families in detail: what each record contains, why
it can be trusted, how it is generated and validated, and the full regeneration recipe.
