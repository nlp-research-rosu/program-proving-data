# Program proving data

Concrete execution traces, symbolic paths, and checked proofs for small Python programs.

This repository contains 40 JSON records for 39 small Python programs, a Lean proof corpus,
and 87 Harbor task samples. The records pair source code with execution states, branch
conditions, loop invariants, and formal claims about the result.

Use these samples to study a model's predictions at each step, its reasoning about symbolic
inputs, or its proof construction. The collection supports training experiments and evaluation design.

## Find data for your work

| If you work on | Start with | What the samples contain |
|---|---|---|
| Models that predict program execution | [Concrete traces](corpus/k/concrete/a1_sum_to_n.md) | Source lines, local variables, calls, returns, assertion failures, and the semantic rules behind each event. |
| Models that reason about many inputs | [Symbolic execution trees](corpus/k/symbolic/b2_classify_triangle.md) | Symbolic states, path conditions, witness inputs, and evidence that some paths are impossible. |
| Mathematical and formal proof reasoning | [Sum of squares](corpus/k/verification/c29_kb_squares_cubic.md) and its [Lean proof](corpus/lean/KMiniPy/Verification/C29KbSquaresCubic.lean) | Quantified arithmetic claims, induction, case analysis, and invariants for nested loops. |
| RL frameworks and evaluation environments | [Harbor task samples](tasks/) and the [dataset registry](registry.json) | Programs, instructions, reference answers, verifier contracts, and binary rewards. |
| Formal methods research or teaching | [The corpus guide](corpus/README.md) and [a refuted specification](corpus/k/verification/c3_buggy_abs.md) | Worked examples from concrete runs to proofs, including a bug and its counterexample. |

## What is in the collection

| Data | Count | Format and contents |
|---|---:|---|
| Concrete traces | 4 records | Line, call, return, and exception events with local variables and K rule annotations. |
| Symbolic traces | 2 trees | Seven feasible paths and three infeasible paths, with conditions, symbolic states, and solver evidence. |
| Verification records | 34 records | 33 proved specifications and one refutation, with claims, invariants, verdicts, and concrete witnesses. |
| Lean proofs | 85 audited headline theorems | Execution proofs, symbolic path proofs, specification proofs, and a refutation. |
| Harbor task samples | 87 tasks | Four families that reuse the corpus programs and proofs. |

The [K records](corpus/k/README.md) use one JSON object per `.jsonl` file.
Each record has a readable `.md` companion. Records include source code and provenance.
The [record schemas](REPORT.md#record-schemas-jsonl-one-record-per-file) describe the fields.
The [Lean corpus](corpus/lean/README.md) contains `.lean` files in a buildable package.

The subjects include 31 problems from the
[KleverBench](https://github.com/nlp-research-rosu/KleverBench) IMP seed set and the original
execution, symbolic, and verification examples. The problems range from straight-line
assignments to nested loops and multi-stage pipelines.
[Provenance notes](programs/PROVENANCE.md) give the upstream revision and translation rules.

## Read a trace, a symbolic path, or a proof

In [the `sum_to_n` trace](corpus/k/concrete/a1_sum_to_n.jsonl), line 5 executes
`acc = acc + i`. The event records `acc = 0`, `i = 1`, and `n = 5` before that line.
Its `k_rules` field names the rules for variable lookup, arithmetic, and assignment.
The [rule index](semantics/mpy-traced/rules.yaml) gives their locations and meanings.
This provides supervision for both the state and the rule that changes it.

The [triangle classification tree](corpus/k/symbolic/b2_classify_triangle.jsonl) describes
five feasible paths over symbolic inputs. Each path has a condition and a concrete witness.
Three further paths are infeasible, including `a == b and b == c and not (a == c)`.
The record includes solver evidence for their exclusion.

[The sum-of-squares sample](corpus/k/verification/c29_kb_squares_cubic.md) states
`res = n*(n+1)*(2*n+1)/6` for every integer `n >= 1` after a short nested loop.
Its final state also fixes both loop counters at zero.
The K claims and [Lean derivation](corpus/lean/KMiniPy/Verification/C29KbSquaresCubic.lean)
show how loop invariants support the polynomial result.
Other samples cover Gauss sums, absolute value, piecewise results, and several stages of computation.

The [buggy absolute-value sample](corpus/k/verification/c3_buggy_abs.md) refutes the specification
with the input `x = 0` and a concrete run that returns `None`.
Its [Lean refutation](corpus/lean/KMiniPy/Verification/C3Refutation.lean) includes a checked witness.

## Harbor task samples for RL and evaluation

The [Harbor](https://docs.harborframework.com/tasks/overview) samples turn corpus problems
into tasks with a reward of 1 or 0. Each task includes instructions, a container definition,
a reference solution, and a verifier. The reference solution is the oracle.

| Dataset | Tasks | The agent completes |
|---|---:|---|
| `k-proved-specs` | 33 | The full final-state specification and any loop circularity claims needed to prove it. |
| `k-loop-invariants` | 21 | The loop circularity claims for a frozen entry claim. |
| `lean-proved-specs` | 12 | A reachability-logic derivation of a frozen specification over proved execution paths. |
| `lean-loop-invariants` | 21 | A loop invariant and Circularity derivation over proved execution steps. |

A circularity claim states the invariant that the prover uses when reasoning about a loop.
Reachability logic is the proof calculus used for the specification claims.
K specification tasks ask the agent to write the specification.
Lean specification tasks give the specification and ask the agent to prove it.

The registry also includes `proved-specs`, `loop-invariants`, and `all`.
Task metadata records the family, toolchain, structural tier, loop count, and loop depth.
Difficulty labels are heuristic. Structural tiers describe the programs.
The collection includes no model calibration results.

```
harbor run --repo nlp-research-rosu/program-proving-data -d loop-invariants -a <agent> -m <model>
harbor run --repo nlp-research-rosu/program-proving-data -p tasks -i 'k-spec-*' -a <agent> -m <model>
harbor run -p tasks -a oracle          # local clone: every task scores 1
harbor run -p tasks -a nop             # local clone: every task scores 0
```

The agent runs as a non-root user with no network access.
A separate verifier checks the submitted files against its own source files and compiled artifacts.
The public repository contains the reference answers, so the network restriction matters for evaluation.

<details>
<summary>Verifier contracts</summary>

K submissions contain claims in a restricted grammar.
The verifier requires the frozen regions of the entry claim to remain unchanged.
It rejects extra imports, rules, syntax, or trusted attributes.
For specification tasks, every final variable must have a value over the symbolic inputs.
Each existential integer must have exactly one equality that determines its value.
The verifier compares those values with CPython on sampled inputs, including precondition boundaries.
It then requires `kprove` to print `#Top` within the limit stated in the task instructions.
Invariant tasks also require an unchanged entry claim and at least one additional claim.

The [claim checker](scripts/harbor/kclaims.py) defines the accepted expressions and integer semantics.
The `abs_val` task uses the equivalent target `?R ==Int absInt(X)`.
The nested-branch task expresses the triangular number of `minInt(A, B)` with `#if A <=Int B`.
This follows the circularities' branch split and avoids an ambiguous nonlinear simplification.
The triangle-down tasks express `minInt(X, 0)` as `X -Int maxInt(X, 0)` in the entry
and circularity claims, avoiding a conditional `minInt` simplification that can return SMT `unknown`.
The corpus claims stay unchanged. CI proves the generated targets again.

The Lean verifier assembles its own package and admits the proof files that the agent imports.
It restricts imports, options, and language constructs that could bypass the proof checker.
A verifier-owned Spec module fixes the claim. `Check.lean` applies the agent's theorem to that claim.
The package must build without `sorry`, Lean's omitted-proof marker.
The axiom audit permits only `propext`, `Classical.choice`, `Quot.sound`, and the two documented String-hook declarations.
Those declarations are `eqStringHook` and `«_==String__STRING-COMMON_Bool_String_String»`.

</details>

<details>
<summary>Task file layout</summary>

```
tasks/k-inv-kb-sum/
├── instruction.md            what the agent is told (program, files, grading rules, a K primer)
├── task.toml                 Harbor config + metadata; separate verifier; no network; artifacts
├── environment/
│   ├── Dockerfile            K 7.1.337 image → kompile the semantics (shared layer) → /app
│   ├── klever/               the vendored klever MPY semantics + MPY-VERIFICATION module
│   └── app/                  program.py, verification.k, spec.k (the skeleton)
├── tests/
│   ├── test.sh → grade.py    the grader (stdlib Python, `python3 -I`, pristine verification.k)
│   ├── kclaims.py            claim parser / whitelist / closed-form evaluator
│   └── reference.json        frozen regions, inputs, precondition, program text
└── solution/
    ├── solve.sh              copies the reference spec.k into /app
    └── spec.k                the corpus claim module (kprove #Top)

tasks/lean-inv-kb-sum/
├── environment/
│   ├── Dockerfile            ubuntu → elan + Lean v4.30.0 → base package built (shared layer) → task files
│   ├── base/                 lakefile, toolchain, KMiniPy/{Prelude,Sorts,Inj,Func,Rewrite,Relations,RL}.lean
│   └── task/                 KMiniPy.lean (root), Verification/C14KbSumLegs.lean (proved legs), Verification/C14KbSum.lean (stub)
├── tests/
│   ├── test.sh → grade.py    restores verifier-owned files + pristine build dir, lake build, Check.lean, axiom audit
│   ├── Check.lean            the frozen statement over verifier-owned init/final, closed by the agent's theorem
│   └── pristine/             every verifier-owned source file
└── solution/C14KbSum.lean    the corpus derivation (proved; core axioms + two String-hook axioms)
```

</details>

## Data checks

The K records use Python semantics written in the [K framework](https://kframework.org),
which makes language rules executable. K's [klean backend](corpus/lean/README.md) translates
a related semantics variant into [Lean 4](https://lean-lang.org).

- Concrete events match fresh CPython traces, including local variables and values.
- Symbolic paths include witnesses that reproduce their results. Solver checks establish that pruned paths are infeasible.
- K verification records contain reachability claims, loop circularities, and prover verdicts.
- Lean checks the proof terms. The [axiom audit](corpus/lean/KMiniPy/AxiomAudit.lean) reports dependencies for each headline theorem.
- CI checks that the task samples match the corpus and templates. Every oracle must score 1, and every untouched task must score 0.

The samples cover a Python subset. Verification claims use reachability logic and do not
by themselves establish termination. The Lean package encodes that calculus without a proof of its soundness.
Read the [Lean correspondence and trust notes](corpus/lean/README.md) for the semantics differences and axiom assumptions.
[REPORT.md](REPORT.md) documents the checks, record formats, and reproduction steps.

## Use the data for training or evaluation

Use `corpus/` for trace and proof data. Keep the benchmark files under `tasks/` out of training corpora.
Those files contain training-exclusion canaries.

The corpus and tasks share programs, claims, and reference proofs across both toolchains.
For held-out evaluation, split by the underlying program or problem across the whole repository.
Training on a corpus proof exposes answers to related task samples, even if their task files stay excluded.

## Check or reproduce the samples

Read the JSON and Markdown records without installing a prover.
`make k-validate` checks the committed K records with Python 3.
`make lean-build` checks the Lean corpus with the pinned toolchain and [elan](https://github.com/leanprover/elan).
Running Harbor tasks requires Harbor and Docker.

```
make harbor-tasks        # regenerate tasks/ + registry.json from corpus/ (idempotent)
make harbor-check        # drift check, shape, offline K graders, leaks, harbor lint
make harbor-oracle-lean  # Docker: harbor run -a oracle / -a nop on the Lean tasks
make harbor-oracle-k     # Docker: the same on the K tasks (kompile once, ~5 min)
```

Before repeating an oracle check, move previous `jobs/oracle-*` and `jobs/nop-*` results aside.
The reward checker rejects duplicate task results.
Pass one timestamped job directory to `scripts/harbor/ci_rewards.py` to inspect an existing run.

The [CI workflow](.github/workflows/harbor.yml) runs on pull requests and pushes to `main`.
The [task builder](scripts/harbor/build_tasks.py) reads the corpus and
[templates](scripts/harbor/templates/) to create `tasks/` and `registry.json`.
Edit those sources and regenerate the tasks. CI rejects any difference from the generated files.

## Repository layout

```
tasks/           87 Harbor tasks (generated; implicit dataset for `harbor run -p tasks`)
registry.json    named datasets over tasks/ for `harbor run --repo ... -d <name>`
corpus/          the canonical, machine-checked source: k/ (records), lean/ (package), specs/ (K claims)
programs/        the Python subjects
semantics/       mpy-traced/ (klever MPY + trace overlay) and minipy-lean.k (klean-ready)
scripts/         harbor/ (generator, graders, checks), k/ and lean/ (corpus pipelines), py2mpy_traced.py
vendor/klever/   pinned upstream semantics (never modified)
docs/            historical plans and the klean feasibility experiment
```
