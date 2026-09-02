# Execution traces, symbolic states, and machine-checked invariants from one formal semantics

Code models learn mostly from static text: source files, diffs, documentation. A consistent
finding in the literature, from Learning to Execute (Zaremba and Sutskever, 2014) through
Scratchpads (Nye et al., 2021), NExT (Ni et al., 2024), and most recently Meta's Code World
Model, which mid-trained on interpreter traces at the scale of a hundred million functions, is
that models reason about code better when they also see how code runs: what values the locals
hold at each line, which branch fires, what a call returns.

The problem is supply. Line-level runtime state barely exists on the internet. And the two kinds
of data with the most to say about program behavior are rarer still:

- Symbolic states. "After this branch, `x` is any negative int and the function returns
  `0 - x`." One trace that covers a whole class of inputs, with the path condition spelled out.
- Invariants and proofs. "This loop maintains `total == i*(i-1)/2`, so `f(n) == n*(n-1)//2`
  for every `n >= 0`." Checked by a prover, together with the refutation and the counterexample
  when the code is wrong. Whether models can infer invariants is an active research question
  (Pei et al., ICML 2023); data to teach it is scarce because producing it normally takes a
  verification engineer driving a prover, one program at a time.

This repository demonstrates that both, plus ordinary concrete traces, fall out of a single
artifact: an executable formal semantics of Python written in the
[K framework](https://kframework.org). Once the language rules exist, concrete tracing, symbolic
execution, and deductive proof are the same rule base driven three ways. We generated nine
samples and validated every one mechanically.

The semantics is not a toy built for this demo. We reuse the klever reference semantics of
Python: about 2,100 lines of modern K whose concrete behavior passes a 39-program suite against
a CPython oracle, and over which 62 HumanEval problems already have machine-checked proofs. Our
additions are one trace cell, three rule patches totaling eight lines, and the extraction and
validation scripts.

## What is in data/k/

| family | samples | each record contains | ground truth |
|---|---|---|---|
| concrete traces | [a1 sum_to_n](data/k/concrete/a1_sum_to_n.md) · [a2 gcd](data/k/concrete/a2_gcd.md) · [a3 collatz](data/k/concrete/a3_collatz_steps.md) · [a4 assert-fail](data/k/concrete/a4_half_of_even.md) | line/call/return/exception events with locals, and for each event the sequence of K rewrite rules that produced it | every event matches a fresh `sys.settrace` run exactly |
| symbolic traces | [b1 abs_val](data/k/symbolic/b1_abs_val.md) · [b2 classify_triangle](data/k/symbolic/b2_classify_triangle.md) | the execution tree over all inputs: per path, line-tagged symbolic locals, the path condition, a z3 witness, and the infeasible paths the solver pruned | every witness replays through CPython and through the K build with the same line path and result |
| verification traces | [c1 range-loop](data/k/verification/c1_range_loop.md) · [c2 abs_val](data/k/verification/c2_abs_val.md) · [c3 buggy_abs](data/k/verification/c3_buggy_abs.md) · c4–c34: the [31-problem KleverBench port](programs/PROVENANCE.md) | the spec, the loop invariant where there is one, the prover verdict, and on refutation the counterexample and its failing run | `kprove` reachability proofs (K Haskell backend with z3); counterexamples replayed concretely |

The c4–c34 block ports the complete seed set of
[KleverBench](https://github.com/nlp-research-rosu/KleverBench), a benchmark of
auto-formalization problems (an IMP program plus a reference reachability claim pinning
its exact final state). Each problem is translated to a module-level MiniPy program
(inputs as magic literals) and respecced over the untouched vendor MPY semantics in
KleverBench's own strength discipline: the claim characterizes the ENTIRE final scope —
every binding pinned to a closed form of the symbolic inputs, `requires` exactly the
problem's stated precondition, `[all-path]`. The five structural tiers are all covered:
straight-line dataflow (c4–c8), single branches/loops with hook closed forms and
`#while`-anchored circularity claims (c9–c16), mixed branch-and-loop programs (c17–c25),
nested loops with one circularity per loop level (c26–c31, including the sum-of-squares
cubic c29 and the branch-guarded c31), and multi-stage pipelines whose intermediates stay
symbolic across stages (c32–c34). All 31 prove `#Top` in 7–22 s each; every record's
`provenance.upstream` names the source problem and quotes the original IMP text, and its
`concrete_witness` is re-executed in CPython by `make k-validate`.

## What an interpreter cannot record

Instrumented interpreters report what one concrete run did. That is where most execution data
comes from, and it is also its ceiling. A semantics answers more questions, because running a
program and reasoning about it use the same rules:

| capability | interpreter hook (`sys.settrace`) | K semantics (this repo) |
|---|---|---|
| faithful line and locals traces | yes | yes, validated event for event against `sys.settrace` |
| why each step happened, as named semantic rules | no | yes, `k_rules` on every event |
| one trace for a class of inputs, with path conditions | no | yes, via symbolic execution |
| evidence that a path is impossible | no | yes, solver-pruned paths with unsat proofs |
| loop invariants and functional specs as checked artifacts | no | yes, K reachability claims |
| refutations tied to a concrete failing run | no | yes, stuck state to z3 model to replayed trace |
| other languages | one interpreter per language | any language with a K semantics (EVM, Wasm, C, ...) |

## Four excerpts

### A trace step that explains itself

For `acc = acc + i` at line 5 of `sum_to_n`, the record
holds the observation, locals `{"acc": 0, "i": 1, "n": 5}`, and the rules that execute the line:

```
seq.step → strict.assign-rhs → strict.binop → name.lookup-begin → name.lookup-hit
→ strict.binop ×2 → name.lookup-begin → name.lookup-hit → strict.binop
→ op.binop-dispatch → strict.assign-rhs → assign.store → seq.step
```

Each name maps to a rule in [`semantics/mpy-traced/rules.yaml`](semantics/mpy-traced/rules.yaml) with its source
location and a one-line meaning. The record shows why `acc` became 1, at the granularity of
individual semantic steps, and the 969 annotations across the four concrete samples were checked
against the event stream by count, per segment.

### All executions of a function at once

`classify_triangle(a, b, c)` with all three arguments
symbolic yields five feasible paths and three impossible ones. Each feasible leaf carries
line-tagged symbolic locals, its path condition, and a witness that replays: `{a: 2, b: 2, c: 2}`
reaches `"equilateral"`. The three impossible combinations, such as
`a == b and b == c and not (a == c)`, are in the record too, each with a z3 unsat proof. A
symbolic trace reads like a concrete one with terms in the value slots, so the two families
teach the same format at two levels of abstraction.

### An invariant, checked for unbounded input

For `f(n)` summing `range(n)` with `n` symbolic
and `n >= 0`, `kprove` discharges an entry claim and a loop-invariant circularity and returns
`#Top` in 19 seconds. The record quotes both claims verbatim next to the Python source. A
concrete tracer cannot state this property at all: it quantifies over every `n`.

### A bug as one connected record

`buggy_abs` drops the `x == 0` case. Under the same spec that
proves for `abs_val`, the prover gets stuck; the stuck state's path condition,
`not (x < 0) and not (x > 0)`, hands z3 the model `x = 0`; replaying `x = 0` produces the failing
trace where `result` is `None`. Spec, failed proof, counterexample, and failing execution sit in
one record, which is the shape a model needs to connect "what the code promises" to "where it
breaks".

## Why the numbers can be trusted

1. Concrete traces are compared event for event with a fresh `sys.settrace` run: kind, line,
   every local, every value. The three normalizations applied are documented at the end of
   this report. Generation fails on any mismatch; nothing ships unvalidated.
2. Rule annotations come from the LLVM backend's proof-hint stream. Segment counts must equal
   event counts, so misalignment is an error rather than a quietly wrong label.
3. All seven symbolic leaves replay their z3 witness through CPython and through the K build,
   and both must reproduce the leaf's line path and result. The pruned paths are re-proved unsat
   with standalone z3.
4. `#Top` from `kprove` is a machine-checked reachability proof over the same rules the concrete
   traces ran on. The klever project keeps proofs and execution on one semantics by design, and
   its own test suites back that semantics.
5. `make k-data` regenerates everything from source; `make k-validate` re-checks the committed
   data; `make vendor-diff` prints the complete delta against the pinned upstream semantics.

## The same claims in Lean

Everything above is checked by the K toolchain. A second deliverable in [data/lean/](data/lean/) removes
even that dependency from verification: `klean`, K's Lean 4 backend, translates a
constructor-based variant of the semantics into a Lean package, and generated theorem files
state the dataset's claims over it. Anyone with Lean can replay every proof with `lake build`,
no K installation involved — and for the Lean community this is sample data of a kind that
barely exists: program executions and program specs as checkable theorems, produced mechanically
from a language semantics.

- Five complete executions are theorems: `sum_to_n(5) = 15` in 224 rewrite steps,
  `gcd(48, 18) = 6` in 138, `buggy_abs(0) = None` in 46, `collatz_steps(6) = 8` in 491, and
  `half_of_even(7)` halting at its failed assertion in 29 — an execution-to-failure theorem.
  Each step is a named lemma applying one semantic rule to an explicit machine configuration;
  transitivity folds them into `Rewrites init final`.
- The refutation is a theorem: some input drives `buggy_abs` to a `None` result, witnessed by
  the 46-step `x = 0` execution — the spec violation and its counterexample run live in one
  proof term.
- All seven symbolic path theorems are proved, ∀-quantified: `abs_val`'s two paths (for every
  `x < 0` the program rewrites to `-x`; for every `0 <= x`, to `x`) and `classify_triangle`'s
  five feasible paths over three integers — each generated at a witness input and discharged
  with its path condition.
- The ENTIRE KleverBench port (c4–c34) is mirrored one Lean file per problem. The
  loop-free tier: generated ∀-quantified path theorems (up to four paths with two
  condition hypotheses each) topped by a reachability-logic `spec` restating the K
  claim's full final-scope characterization. Every loop program: generated parametric
  execution legs (a table-driven engine handles multiple loop variables, branch
  prologues, branches in the body, post-loop epilogues, and witness-seeded
  initializers) composed by a hand-written Circularity derivation — the Gauss pair
  carries `2s + i(i+1) = 2sum + n(n+1)`-style additive invariants whose products stay
  single-variable, the no-precondition family splits loop-runs/no-op by Case Analysis
  with `min`/`max` posts, and the pipelines freeze their branch-computed intermediates
  as invariant parameters. The nested tier (c26–c31, sum-of-squares cubic and
  branch-guarded triangle included) keeps the Circularity mirror for the outer
  invariant while the inner loop enters as a ∀-quantified execution lemma proved by
  fuel induction on the inner counter — leg gluing in the NilStack-drain style, the one
  documented structural deviation from the K records' two-circularity proofs.
- The package also encodes **reachability logic** — the proof system K's verifier implements
  (OOPSLA 2016, Figure 4) — as an inductive derivability judgment adding zero axioms, and both
  verification specs are proved in it: `sum_to_n`'s Gauss closed form for every `n >= 0` is a
  machine-checked derivation using Circularity on the loop invariant — the same proof shape
  `kprove` ran on the K side, there on the vendored `range_loop` — built from generated
  execution legs; the abs functional spec is derived by Case Analysis over the two proved
  symbolic paths. Both are one-path (`⇒∃`) derivations, where the K records' claims are
  all-path; the two coincide for this deterministic semantics, an equivalence left informal.
  Nothing in the package is staged or stubbed: every theorem is proved.
- `KMiniPy/AxiomAudit.lean` prints the axioms under every theorem. Every theorem rests on
  Lean's three core axioms plus two String-equality declarations — klean's signature-only hook
  symbol and a one-line axiom interpreting it as String equality — nothing else; a stub
  anywhere would surface as `sorryAx`, and none does. (klean's stock prelude also declares 41
  collection-hook axioms for Map/Set/List operations this semantics never uses; they are
  unreachable, and the audit output shows no theorem touches them.)

klean's generated relation is one-or-more-step rewriting; the package adds many-step rewriting,
divergence, and one-path reachability (reach the target or diverge), which is the right notion
for pre/post specs and invariants without assuming determinism. The whole package builds in
about a minute cold. Architecture and regeneration commands are in [data/lean/README.md](data/lean/README.md).

## Cost

Measured on an 8-core VPS. Definitions kompile in 2 to 5 minutes, once. After that, a concrete
trace with rule annotations takes a few seconds per program, a symbolic tree takes one to two
minutes, and the original three proof runs took 19, 17, and 69 seconds; the 31 ported
KleverBench proofs each kompile their spec module once (~3 min) and prove in 7–22 seconds,
nested loops and pipelines included. The program files are the only sample-specific inputs;
the frontend is CPython's own `ast` module, and the instrumentation and extractors are
generic. The same recipe applies to any corpus the semantics covers, and to any other
K-defined language — the KleverBench port exercised exactly this: 31 new programs went from
IMP source to proved, validated records with no changes to the semantics or the extractors.

## Repository layout

```
data/k/          the K dataset (concrete/, symbolic/, verification/): *.jsonl canonical, *.md readable
data/lean/       the Lean 4 package: klean translation + theorem files (lakefile at this root)
programs/        the Python subjects (self-contained: defs + entry call)
semantics/       mpy-traced/ = vendor MPY + trace overlay (trace.k, patched/{core,call,functions}.k,
                 rules.yaml rule annotations); minipy-lean.k = the klean-translatable semantics
specs/           abs-val and buggy-abs K claim modules (c2, c3; c1 reuses the vendored
                 range-loop spec) + kb-*/ claim modules for the 31 ported KleverBench problems
scripts/         py2mpy_traced.py (vendored py2mpy + --linemarks); k/ = generation + validation
                 pipeline for data/k; lean/ = theorem generators for data/lean
docs/            the approved plans (historical record) and the klean feasibility experiment
vendor/klever/   pinned upstream (sha in VENDOR.md; never modified — `make vendor-diff`)
build/           gitignored: kompiled definitions, mpy files, proof hints (build/k, build/lean)
```

## Reproducing

```
make check-env    # K v7.1.337, pyk, z3
make k-data       # regenerate the K dataset (first run kompiles ~6 min of definitions)
make k-validate   # standalone re-checks of the committed K data
make vendor-diff  # the entire semantics delta vs the pinned upstream
```

Regeneration prerequisites (the committed data needs none of this): K v7.1.337
([release builds](https://github.com/runtimeverification/k/releases) or `kup install k`),
pyk from the `kframework` PyPI package — `python3 -m venv .venv && .venv/bin/pip install
kframework==7.1.337`; the Makefile uses `.venv/bin/python` when present and falls back to
`python3`, which suffices for `make k-validate` — and `z3` on `PATH`.

Every K invocation runs under `timeout` (kompile 600 s, krun 120 s, kprove 900 s plus an 8 GB
memory cap). These programs are tiny, so anything slower than minutes is treated as stuck and
investigated rather than waited on.

The Lean package rebuilds with `make lean-build` (or `lake build` in `data/lean/`; no K
toolchain needed). `make lean-gen` regenerates the theorem files from the semantics: it
kompiles `build/lean/minipy-lean{,-hints}`, rebuilds the `.mpy` inputs, and runs the three
generators in `scripts/lean/`, whose output is idempotent against the committed package. The
klean base modules (`Prelude/Sorts/Inj/Func/Rewrite`) are regenerated manually when the
semantics changes: run `python -m pyk.klean` in a scratch directory and copy the five modules
over (klean emits a whole package skeleton, and its `Inj`/`Func` declaration order varies from
run to run).

## Record schemas (JSONL, one record per file)

Every record carries `kind` (its family, below) and a stable `id`.

**concrete_trace** (`data/k/concrete/`): `source{file, code, entry, args}`, `result`,
`exception`, `trace[]` of events
`{event: line|call|return|exception, line, locals, [func], [value], [exc], k_rules[]}`,
where `k_rules[]` is `{rule: "<file>:<line>", name, kind: semantic|structural|instrumentation,
desc, [count]}` (consecutive repeats collapsed), plus `k_prelude_rules[]` (program-load steps
before the first event) and `provenance` (generator, K version, klever sha, validation status).

**symbolic_trace** (`data/k/symbolic/`): `source` (args are `?x:int` style), `tree{n_nodes,
edges[{from, to, condition}]}`, `leaves[]` of
`{node, value (symbolic term or literal), path_condition[], trace[{event, line,
locals(symbolic)}], witness, witness_validated, witness_replay, terminal_reason}`, and
`pruned_infeasible[]` of `{path_condition, verdict, proof}`. Variables equal on a path print
under one representative symbol: a leaf whose locals read `a: c, b: c, c: c` had `a = b = c`
forced by its path condition.

**proof_trace** (`data/k/verification/`): `source`, `spec{requires, ensures, invariants[],
claim_k (verbatim spec.k)}`, `result: proved|refuted`, `prover{tool, wall_seconds,
verdict_marker, memory_cap}`, `note`, `provenance{definition, spec_module}`, and
`counterexample` (null when proved) of `{stuck_path_condition, model, model_source,
failing_trace{input, result, code, trace, violates, why}}`. Ported KleverBench records
additionally carry `provenance.upstream{repo, sha, problem, program_imp}` (the source
problem and its verbatim IMP text) and `concrete_witness{finals}` (the module bindings
after running the program at its magic literals — re-executed and compared by
validate.py), and their `source.file` names the program file.

## How each family is generated

- **Concrete**: `py2mpy_traced --linemarks` interleaves `LineMark(lineno)` statements, plus a
  loop-header re-log marker at each loop body end so the header line reappears once per
  iteration, the same cadence `sys.settrace` produces. The traced LLVM build logs
  `lineEvt(line, scope-map, heap)` immediately before each statement executes, and
  `callEvt`/`retEvt` at the two frame rules; `scripts/k/kastjson.py` and `scripts/k/tracelib.py`
  render values Python-style. The `k_rules` come from a second run on the
  proof-hint-instrumented build: `kore-proof-trace` lists every applied rule with its source
  location, and the top-level rewrite steps are segmented at the instrumentation boundaries and
  attached to their event. Segment and event counts must be equal or generation fails.
- **Symbolic**: the same program with magic-literal arguments; the ground `--depth 0`
  configuration has those literals replaced by sorted KORE variables; `kore-rpc` (via pyk)
  executes on `MPY-TRACED-SYM`, which is MPY plus the trace overlay and without `MPY-CONCRETE`,
  whose concrete-only rules narrow abstract values. The explorer forks at every
  `BranchingResult`; leaves are decoded with `kore-print --output json`; witnesses come from
  the server-side `get-model` (z3).
- **Verification**: each case's `verification.k` imports the untouched vendor `MPY`;
  `kprove spec.k` runs under a systemd-run memory cap. c1 is the vendored klever `range-loop`
  proof re-run verbatim. For c3 the stuck claim state's constraints on `X` are parsed, solved
  with z3, and the model is replayed through the concrete pipeline into the embedded failing
  trace.

## Differential-validation normalizations (concrete family)

- **N1** CPython's module-frame `call`/`return` events are dropped; the K module scope has no
  frame.
- **N2** function and builtin values render as `"<function NAME>"`; dunder globals are dropped.
- **N3** after the first `exception` event, CPython's unwind returns and per-frame exception
  duplicates are dropped; the K semantics halts at the raise.

Everything else must match exactly: event kinds, order, line numbers, every local's value,
return values. A mismatch fails generation.

## Attribution

The Python semantics, py2mpy frontend, lemma layer, and the range-loop proof are the
[klever](vendor/klever/VENDOR.md) project's reference semantics, vendored at
`2a90fec7cf82a37633465ee7beeca0f6a6512b31` (2026-07-14). This repo adds the trace overlay, the
extraction and validation pipeline, the klean-compatible `minipy-lean.k` semantics, and both
datasets. K framework v7.1.337; klean from the same pinned pyk.

The c4–c34 verification samples and the `kb_*` programs derive from
[KleverBench](https://github.com/nlp-research-rosu/KleverBench) at
`b5eced33b16d13b28b9998f05e7b7e945f2fb482` (2026-08-27): its 31 IMP seed problems are
translated (not vendored — no upstream file is copied) per the rules in
[programs/PROVENANCE.md](programs/PROVENANCE.md), and every derived record names its
source problem and quotes the original IMP text in `provenance.upstream`.
