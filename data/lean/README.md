# KMiniPy — program executions and specs as Lean 4 theorems

A self-contained lake package generated from the K semantics
[`semantics/minipy-lean.k`](../../semantics/minipy-lean.k) by klean (`pyk.klean`, kframework
7.1.337). `KMiniPy/{Prelude,Sorts,Inj,Func,Rewrite}.lean` are the translation, consumed
untouched: `Rewrites` is one-or-more-step rewriting with one constructor per semantic rule.
Layered on top, mirroring `data/k/{concrete,symbolic,verification}`:

- `KMiniPy/Relations.lean` — `MultiStep` (⇒*), `Diverges`, and `Reaches` (one-path
  reachability: diverge or reach in finitely many steps — the right notion for pre/post specs
  and invariants on any system), plus the one interpretation axiom `eqStringHook` for klean's
  signature-only String-equality hook.
- `KMiniPy/Concrete/` — complete concrete executions as theorems, fully proved:
  sum_to_n(5)=15 (224 steps), gcd(48,18)=6 (138), collatz_steps(6)=8 (491), and
  half_of_even(7) halting at its failed assertion (29 steps — the final configuration is the
  terminal `assertFailed` marker with the frame state at the raise). One named theorem per
  rewrite step, folded by transitivity into `trace : Rewrites init final`.
- `KMiniPy/Symbolic/` — ∀-quantified per-path theorems, all PROVED: abs_val (2 paths over x)
  and classify_triangle (5 feasible paths over a b c; the 3 solver-pruned contradictory branch
  combinations have no theorem, as in the K record). Each path is generated at a witness
  input, every configuration parameterized, hypotheses discharged by simp with the semantics'
  function equations then omega on the path condition; paths with equal-on-path variables are
  proved as reduced lemmas over one variable per equivalence class, the public theorems
  derived by substitution.
- `KMiniPy/RL.lean` — **reachability logic**, the proof system K's `kprove` implements
  (OOPSLA'16 Figure 4, one-path and all-path), encoded as an inductive derivability judgment:
  the constructors are the eight proof rules, postulated as trust base (no soundness proof,
  zero new axioms by construction). Statement taxonomy: execution claims use `Rewrites`;
  verification claims use reachability; `Rewrites` implies reachability (a proved leg enters
  a derivation through Axiom — `SRew`), never conversely without termination.
- `KMiniPy/Verification/` — `C1SumToN.gauss` — **proved**: the Gauss closed form of sum_to_n
  for every n ≥ 0, as a reachability-logic derivation with the same shape as kprove's K-side
  c1 proof, which ran on `range_loop` (Circularity on the ∃-packed loop invariant, Axiom on
  the flushed circularity for the back edge, guard case split, Consequence carrying the
  arithmetic), over the generated
  execution legs of `C1Legs.lean`; `C2AbsVal.spec` — **proved**: the abs_val functional spec
  (result exists, is non-negative, is x or −x — the `?r` result as ∃ inside the right
  pattern), derived by Case Analysis over the two proved B1 path legs; and the
  refutation `C3Refutation.spec_refuted` (**proved**: ∃ x whose run ends with `result = None`
  — the spec-violating final state, the same reading as the K record's stuck-state
  counterexample) together
  with its witness `C3BuggyAbsAt0.lean`, a proved 46-step concrete trace of buggy_abs(0). The
  witness sits here rather than under `Concrete/` for the same reason data/k embeds the
  failing run inside the c3 record: it exists to refute the spec.
- `KMiniPy/Verification/C4KbAssign.lean` … `C11KbMin.lean` — the loop-free tier of the
  [KleverBench port](../../programs/PROVENANCE.md) (K records c4–c11), one generated file
  per problem, all PROVED: `init`/`final` configurations parameterized over every integer
  input, one ∀-quantified path theorem per feasible path (witness generalization, the B1/B2
  machinery, over the MODULE-LEVEL programs), and a reachability-logic `spec` theorem
  mirroring the K claim's full final-scope characterization — straight-line programs derive
  by a single `Rewrites` leg entering as an Axiom over `SRew`; branching programs (abs,
  max, min) by Case Analysis over their two paths, exactly the C2 shape. C7 (double-half)
  carries Python `//` symbolically: its steps discharge through the floorDiv/floorMod
  equations, the `intEmodEq`/`intEdivEq` notation-restoring lemmas of `Relations.lean`,
  and a `Int.tdiv_eq_ediv_of_dvd` bridge in the uniform tactic. `C12KbCountdown.lean`
  (over generated `C12KbCountdownLegs.lean`) extends the port into the loop tier: the
  countdown loop's drain-to-zero claim as a Circularity derivation in the C1 shape —
  parametric prologue/body/exit/epilogue legs, a NilStack of while-residue frames, the
  back edge as Axiom on the flushed circularity — simpler than C1 (module-level, no call
  frame, no accumulator algebra) and a template for the remaining loop problems.
- `KMiniPy/AxiomAudit.lean` — `#print axioms` per headline theorem. Every theorem shows Lean
  core (`propext`, `Classical.choice`, `Quot.sound`) plus the two String-hook axioms, nothing
  else — the package is sorry-free; any stub would surface as `sorryAx` here. (One caveat for
  grep-auditors: klean's stock `Prelude.lean` also declares 41 collection-hook axioms —
  Map/Set/List operations this semantics never uses. They are unreachable from every rule and
  theorem; the audit output is the proof.)

## Correspondence with data/k/

| K sample | Lean counterpart | status |
|---|---|---|
| a1 sum_to_n (concrete) | `Concrete/A1SumToN.lean` — 224-step trace | proved |
| a2 gcd (concrete) | `Concrete/A2Gcd.lean` — 138-step trace | proved |
| a3 collatz_steps (concrete) | `Concrete/A3CollatzSteps.lean` — 491-step trace | proved |
| a4 half_of_even (concrete, assert-fail) | `Concrete/A4HalfOfEven.lean` — 29-step trace to `assertFailed` | proved |
| b1 abs_val (symbolic) | `Symbolic/B1AbsVal.lean` — `path_neg`, `path_nonneg` | proved |
| b2 classify_triangle (symbolic) | `Symbolic/B2ClassifyTriangle.lean` — 5 path theorems | proved |
| c1 range_loop (invariant proof) | `Verification/C1SumToN.lean` — Gauss form ∀ n ≥ 0, RL derivation | proved |
| c2 abs_val (spec proof) | `Verification/C2AbsVal.lean` — spec ∃?r, RL derivation | proved |
| c3 buggy_abs (refutation) | `Verification/C3Refutation.lean` + witness `C3BuggyAbsAt0.lean` | proved |
| c4 kb_assign … c8 kb_arith_mix (KleverBench, straight-line) | `Verification/C4KbAssign.lean` … `C8KbArithMix.lean` — path theorem + RL `spec` (single-leg) | proved |
| c9 kb_abs, c10 kb_max, c11 kb_min (KleverBench, branching) | `Verification/C9KbAbs.lean` … `C11KbMin.lean` — 2 path theorems + RL `spec` (Case Analysis) | proved |
| c12–c16, c20–c25 (KleverBench single loops) | `Verification/C12KbCountdown.lean` … `C25KbLoopMax.lean`, each over its generated `*Legs.lean` — RL Circularity derivations (table-driven legs engine `scripts/lean/gen_lean_kb_loops.py`) | proved |
| c17 max3, c18 clamp, c19 abs-times (KleverBench, multi-path) | `Verification/C17KbMax3.lean` … `C19KbAbsTimes.lean` — 4/3/2 path theorems + RL `spec` (nested Case Analysis) | proved |
| c26–c31 (KleverBench nested loops) | `Verification/C26KbPureNested.lean` … `C31KbNestedWithBranch.lean` over generated legs — outer-loop Circularity; the inner loop enters as a ∀-quantified execution lemma proved by fuel induction | proved |
| c32–c34 (KleverBench pipelines) | `Verification/C32KbPipeline.lean` … `C34KbNormalizeCount.lean` — branch-prologue Case Analysis feeding one loop Circularity, epilogue in the exit leg | proved |

One asymmetry is deliberate: c1's `range_loop` program and spec live in the vendored klever
suite and use `range`/`for`, outside the `minipy-lean.k` subset — `C1SumToN.lean` states the
same loop-invariant property class on `sum_to_n` instead. A second, smaller one: the K records
state their claims all-path (`[all-path]`, kprove's default), while the Lean derivations are
one-path (`RLOne`, ⇒∃) — for this deterministic semantics the two coincide, but the
equivalence is left informal (see the notes in `RL.lean`). The subset models int/bool/string/
None values and `assert` as halt-at-the-raise (no general exceptions), which is exactly what
the samples need. A third, structural asymmetry lives in the nested-loop mirrors
(C26–C31): where the K records prove one circularity per loop level, the Lean derivations
keep the Circularity mirror for the OUTER invariant and let the inner loop enter as a
∀-quantified `Rewrites` lemma proved by fuel induction on the inner counter — execution-leg
gluing exactly like the NilStack drain, documented in each file's docstring. Every one of
the 31 ported problems has a proved Lean counterpart — all forty samples of this package
are proved; `AxiomAudit.lean` machine-checks it.

Build: `lake build` (Lean pinned by `lean-toolchain`, installed via
[elan](https://github.com/leanprover/elan); ~1 min cold, no
dependencies, no K toolchain). Regeneration from the semantics: see the repo-root
[REPORT.md](../../REPORT.md).
