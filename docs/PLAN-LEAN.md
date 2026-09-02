> Historical planning document (July 2026): kept as the record of what was proposed and
> approved. Paths refer to the pre-reorganization layout; see the repo-root README.md for the
> current one. §7's "Execution outcome" is likewise a snapshot (2026-07-14): the staged
> statements it mentions have all since been proved, and the planned `lean-*` Makefile
> targets now exist.

# K-to-Lean program-reasoning samples — Plan v3 (approved for execution)

## v3 revisions (final review round)

1. **Reachability framing corrected (reviewer).** No determinism assumption is needed at all:
   `Reaches a b := Diverges a ∨ MultiStep a b` *is* one-path reachability, which is the right
   semantics for pre/post conditions and loop invariants on any system, deterministic or not.
   The prose in `Relations.lean` and the docs says exactly that; all v2 determinism talk is
   dropped.
2. **Statements first, proofs gated (reviewer's main concern: Lean proofs may be too hard).**
   Execution now has two stages. Stage A delivers the complete package with every theorem
   *statement* elaborating under `lake build` and proofs stubbed by `sorry` — the statements
   themselves are validated (config terms, quantifiers, types all check), and `AxiomAudit.lean`
   doubles as a progress tracker (`sorryAx` visible per theorem). Stage B attempts exactly one
   proof as a difficulty probe: LA1, the first concrete execution trace. Branch policy agreed in
   advance: if LA1 proves smoothly within its timebox, the *mechanically identical* class (LA2,
   LC3's chain) may also be proved by the same generator flag; the creative classes (LB1/LB2,
   LC1, LC2) stay `sorry` for the next review either way. If LA1 is hard, stop and report — the
   remaining proofs move to an interactive session.

---
# (v2 content below, amended in place)

**Goal:** Use `klean` (K's Lean 4 generator) to publish machine-checked Lean sample data about
program reasoning over a K-defined Python subset: concrete execution theorems, symbolic execution
theorems, and verification theorems (functional specs, a loop invariant proved by induction, a
refutation with counterexample) — every theorem shipped **with its Lean proof**, `lake build` as
the checker, zero `sorry`.

## Changes from v1 (feedback merge)

| # | Feedback | Change |
|---|---|---|
| 1 | `Rewrites` (transitive, ≥1 step) is fine as-is; execution theorems are just `Rewrites s1 sn` | Accepted. The strip-`tran` patch is **dropped**; the generated relation is used untouched. Every sample execution takes ≥1 step, so `Rewrites` states them directly; `⇒*` is recovered as a plain definition (`a = b ∨ Rewrites a b`), no new inductive. One consequence flagged in §2.2. |
| 2 | Reachability = `Diverges ∨ rewriting`, assuming determinism | Accepted, and verified definable: `Diverges` can be written over `Rewrites` alone (§2.2), so the layer needs nothing klean doesn't give us. Determinism becomes a **documented assumption** (it is unstatable over a transitive relation anyway — see §2.2), which also deletes v1's riskiest handwritten proof (the n² determinism case analysis). |
| 3 | Rewriting K to bypass missing hooks is fine | Kept: `minipy-lean.k`, same MPY AST constructors, constructor-based env/frames (§2.3). |
| 4 | Nothing should run long; be suspicious | Reaffirmed and extended to Lean: per-file `lake` compile expected in seconds, investigated past ~2 min; whole package < 10 min; same kill-and-diagnose rule as the K side. |
| 5 | Investigate how hard the Lean **proofs** are — they are what make the theorems credible | New §2.5 (proof-cost assessment: what is already proved, what remains risky) + tasks reordered proof-risk-first (chain-length probe in L2, the invariant induction opens L4) + a new `AxiomAudit.lean` artifact running `#print axioms` on every shipped theorem so consumers can see exactly what each proof depends on. |

---

## 1. Investigation findings (all verified by execution; unchanged from v1 except §1.2's conclusion)

### 1.1 What klean is

- Ships inside pyk (`kframework==7.1.337`) as `python -m pyk.klean DEFN_DIR PKG_NAME`; reads any
  kompiled `definition.kore`; generates a Lean 4 lake package pinned to `lean4:v4.30.0`
  (`Prelude → Sorts → Inj → Func → Rewrite`). Verified: package `lake build`s green on this
  machine (Lean 4.30.0 via elan).
- Cells → structures; constructor sorts → inductives; subsorting → an `Inj` typeclass; K
  functions with rules → **computable** Option-valued `def`s; Int/Bool hooks implemented
  concretely in the Prelude (`«_+Int_» x y = some (x + y)`), so arithmetic side conditions
  evaluate by `rfl`/`decide`.
- Each rewrite rule → a constructor of `inductive Rewrites : Cfg → Cfg → Prop`, with binders for
  free variables, hypotheses `defn_Valᵢ : f args = some v`, and `req : cond = true`; plus a
  built-in `tran : Rewrites s1 s2 → Rewrites s2 s3 → Rewrites s1 s3`. So `Rewrites` is exactly
  **one-or-more-step rewriting** (transitive, not reflexive). No `⇒*`, no divergence, no
  reachability anywhere in the output — we add those (§2.2).
- Known public use: RV's evm-equivalence (klean-generated KEVM vs the EvmYul model, per-opcode
  equivalence theorems). No closure/reachability layer there; whole-program execution and
  invariant theorems of the kind we propose don't exist yet as public samples.

### 1.2 Consequences of the baked-in `tran` (revised)

Per review feedback, `Rewrites` is used as-is:

- Execution theorems are stated directly as `Rewrites init final` (your
  "`tran(Rewrites)(s1, sn)`"). The proof term is a `tran`-fold of single rule applications, so
  **the full trace remains visible in the proof**, and we additionally emit each link as its own
  named lemma (`a1_step_0 : Rewrites c₀ c₁`, …), so the trace is also visible at
  statement granularity.
- One nuance, flagged for the record: determinism cannot even be *stated* about a transitive
  relation (from `s`, both the next state and every later state are `Rewrites`-successors, so
  "unique successor" is false as stated). Since the review says to **assume** determinism rather
  than prove it, this costs nothing: the assumption lives in prose (README + a comment in
  `Relations.lean`), justified by the rule guards being pairwise exclusive in `minipy-lean.k` —
  the same rule base the trace dataset validated against CPython. If a machine-checked
  determinism theorem is ever wanted, the one-line tranless regeneration remains available as a
  future option; it is out of scope now.

### 1.3 Feasibility experiment (already proved, vendored at `lean/experiments/smoke2-lean`)

Against klean output for a 2-rule counter semantics, one added file compiles under
`lake build` containing: closure definitions; a concrete execution theorem
(`run 8` to `done 10`, steps discharged by `rfl` + `by decide`); and a symbolic theorem
(`∀ i, i < 10 → Rewrites (run i) (run (i+1))`, side condition via `decide_eq_true h`).
(The experiment used a v1-era `Star`; v2 replaces it with the definitions in §2.2 — a
mechanical simplification, since the concrete chains become `tran`-folds.)

### 1.4 The hard constraint: hooked collections do not translate

`klean` on the full MPY semantics fails (reproduced): the only hooked sorts accepted are
Bool/Bytes/Id/Int/String/StringBuffer(+Endianness/Signedness). `Map`, `List`, `Set`, `Float`
have no sort translation, and the Prelude's Map/List/Set hooks are uninterpreted axioms with no
behavioral rules. MPY's configuration is Maps and Lists throughout, hence §2.3 (approved
feedback #3).

---

## 2. Design (v2)

### 2.1 One generated relation, used untouched

`Rewrites : Cfg → Cfg → Prop` exactly as klean emits it. No post-generation patching of the
`Rewrite` module at all — the generated theory is consumed verbatim, which is the strongest
form of "utilize klean as much as we can".

### 2.2 `Relations.lean`: the thin layer we add (all definable over `Rewrites` alone)

```lean
-- ⇒* as a definition, not a new inductive (zero-step case never occurs in our
-- samples, but this keeps the pre/post semantics mathematically standard)
def MultiStep (a b : Cfg) : Prop := a = b ∨ Rewrites a b

-- Divergence over a transitive relation: every state reachable from `a`
-- (including `a` itself) can take at least one further step. For a
-- deterministic, finitely-branching system this coincides with the existence
-- of an infinite run: the unique run from `a` can never get stuck.
def Diverges (a : Cfg) : Prop := ∀ b, MultiStep a b → ∃ c, Rewrites b c

-- Pre/post-condition reachability: ONE-PATH reachability (either `a` diverges
-- or it rewrites to `b` in finitely many steps). This is the correct semantics
-- for pre/post conditions and loop invariants on any system — no determinism
-- assumption needed.
def Reaches (a b : Cfg) : Prop := Diverges a ∨ MultiStep a b
```

Stage A keeps this file to definitions only; convenience lemmas are added later with the proofs.

### 2.3 `minipy-lean.k`: klean-compatible K semantics, same AST, collection-free configuration

Unchanged from v1 (approved): ~30 rules; **same AST constructors as MPY-SYNTAX** for the used
subset (`Module`, `FuncDef`, `Params`, `Assign`, `If`, `While`, `Return`, `Call`, `Name`, `Int`,
`Bool`, `BinOp`, `UnaryOp`, `Compare`, `CmpOp`), so the vendored `py2mpy` frontend transliterates
the very same program files unchanged; constructor-based environment
(`syntax Env ::= ".Env" | bind(String, Val, Env)` with K-function `lookup`/`update` → computable
Lean defs, so environment reads discharge by `rfl`); constructor-based frames
`frame(K, Env, Frames)` for calls/recursion; values Int/Bool/None; floored `//`/`%` as K
functions. Golden-tested against CPython results for the four programs before any Lean work.

### 2.4 Generated trace theorems

`gen_lean_traces.py` (reusing existing pipeline pieces: `krun --depth` sweep for configurations,
the T2 proof-hints pipeline for which rule fired, and `pyk.klean`'s own pattern printer for Lean
term text) emits per program:

- named step lemmas `theorem a1_step_k : Rewrites c_k c_{k+1} := Rewrites.<rule> rfl … (by decide)`
- the headline theorem `theorem a1 : Rewrites (init …) (final 15)` as a `tran`-fold of the steps
- for c3, the same at the counterexample input.

`lake build` is the validator: a wrong term, rule name, or hypothesis fails compilation.

### 2.5 Proof-production cost (feedback #5): what is proved, what is left, what could bite

The reason to ship proofs is credibility; here is the honest cost map.

| proof kind | mechanism | status | residual risk / probe |
|---|---|---|---|
| single concrete step | rule ctor + `rfl` + `by decide` | **proved today** (§1.3) | none |
| concrete chain (~40–400 steps, fat configs) | `tran`-fold of step lemmas | 3-step chain proved | **elaboration time is the open question** → measured early on `sum_to_n(3)` (L2 probe); mitigations: per-line chunk lemmas (trace line events give natural boundaries), `maxHeartbeats` already 10M in the template, shrink inputs as last resort |
| symbolic step / path | ctor + `decide_eq_true h` | **proved today** (§1.3) | env-lookup normalization may need a tiny `simp` set over `lookup`/`update` — expected minor |
| loop-invariant induction (LC1) | Lean induction on the loop measure, using the symbolic step lemma; the invariant *is* the induction hypothesis | not yet attempted | **the one genuinely creative proof** → opens L4 with a 2 h timebox; cut-line: ship bounded `n ∈ [0..5]` by computation (still real theorems) and mark the inductive version in-progress |
| refutation (LC3) | concrete chain at `x = 0` + `¬ spec None` by `simp`/`decide` | follows from the above | none |
| axiom transparency | `#print axioms <thm>` for every shipped theorem (`AxiomAudit.lean`) | trivial | none — expected result: only Lean core axioms (`propext`, …); klean's unused Map/Set/List hook axioms must NOT appear, and the audit proves that to any reader |

Per feedback #4, Lean gets the same watchdog discipline as K: any single file compiling
longer than ~2 min is treated as a design problem (chunk it), not something to wait on.

### 2.6 Theorem inventory (the Lean sample data)

| id | statement (informal) | proof |
|---|---|---|
| LA1 | `Rewrites (init sum_to_n(5)) (final 15)` + named step lemmas | generated |
| LA2 | `Rewrites (init gcd(48,18)) (final 6)` (recursion through frames) | generated |
| LB1 | `∀ x, x < 0 → Rewrites (init abs_val(x)) (ret (-x))`; `∀ x, 0 ≤ x → … (ret x)` | handwritten |
| LB2 | symbolic loop iteration: `i < n → Rewrites (loop i acc) (loop (i+1) (acc+i))` | handwritten; the invariant step |
| LC1 | `∀ n ≥ 0, Rewrites (init sum_to_n(n)) (final (n*(n+1)/2))` + `Reaches` corollary | induction via LB2 |
| LC2 | `∀ x, ∃ r, Rewrites (init abs_val(x)) (ret r) ∧ r ≥ 0 ∧ (r = x ∨ r = -x)` | from LB1 |
| LC3 | `Rewrites (init buggy_abs(0)) (ret None)` + `¬ spec None`, packaged as `∃ x, …` refutation | generated chain + `simp` |
| LX | `AxiomAudit.lean`: `#print axioms` for every theorem above | trivial |

Everything stated with `Rewrites`/`Reaches` per §2.1–2.2; no `sorry` anywhere; package has no
mathlib dependency (closures, `omega`, `decide` are core Lean).

---

## 3. Tasks (v3 staged execution; commit + push per task)

**Stage A — everything as statements, zero proofs (`sorry` stubs):**

- **S0 (15 min) scaffold.** `lean/` tree (experiment already vendored), Makefile targets
  (`lean-gen`, `lean-build`, `lean-all`).
- **S1 (90 min) `minipy-lean.k`.** Semantics per §2.3; kompile LLVM; golden tests vs CPython for
  the four programs (`sum_to_n`, `gcd`, `abs_val`, `buggy_abs`). First action: 5-rule probe that
  `frame(K, Env, Frames)` (K-sorted constructor argument) survives kompile + klean; fallback: a
  dedicated `Cont` constructor sort.
- **S2 (45 min) klean → package + `Relations.lean` (definitions only).** `lake build` green.
- **S3 (90 min) statement generation.** `gen_lean_traces.py` in statement mode: LA1/LA2/LC3
  headline theorems + per-step lemma statements (configs from `krun --depth` sweeps, printed with
  pyk.klean's own pattern printer), all `:= sorry`; handwritten statement files for LB1, LB2,
  LC1, LC2; `AxiomAudit.lean` (tracks `sorryAx` per theorem). `lake build` green = every
  statement elaborates.

**Stage B — the difficulty probe (reviewer-gated):**

- **S4 (90 min timebox) prove LA1 only.** Generator `--prove` flag emits
  `Rewrites.<rule> rfl … (by decide)` per step + the `tran`-fold. Measure compile time and
  fragility. Branch policy (pre-agreed): smooth ⇒ also flip LA2 + LC3-chain (same mechanical
  class) and stop; hard ⇒ stop immediately and report for an interactive session. LB/LC1/LC2
  remain `sorry` either way.
- **S5 (30 min) docs + report.** README-Lean section (one-path reachability note, package usage,
  proof status per theorem), REPORT addendum, `make lean-all` from clean checkout, final push +
  difficulty report to reviewer.

Total ≈ 6 h worst case. Watchdogs: kompile ≤ 600 s, krun ≤ 120 s, klean ≤ 300 s, `lake build`
≤ 600 s per invocation, single Lean file ~2 min investigation threshold.

## 4. Risks

| risk | level | handling |
|---|---|---|
| K continuations in constructor frames upset kompile/klean | medium | probed first in L1; `Cont`-sort fallback designed |
| step-chain elaboration time | medium | measured in L2 before scaling; chunking by trace line events; input shrink as last resort |
| LC1 induction fiddliness (Int measure, config equalities) | medium | `omega`/`simp` discipline; bounded-`n` cut-line keeps a shippable artifact |
| `pyk.klean` private printer API drift | low | version pinned; printer output is plain text we can vendor if needed |
| ~~determinism case blow-up~~ | — | removed: determinism is assumed per review, not proved |

## 5. Decision points (defaults reflect the review)

1. `minipy-lean.k` with constructor env/frames instead of extending klean's Map support —
   **approved** (#3); klean feedback still worth filing upstream.
2. Same repo, under `lean/` — default yes.
3. Use `Rewrites` untouched; `⇒*`/`Diverges`/`Reaches` as definitions on top — **per review**
   (#1, #2); tranless regeneration noted only as a future option if proved determinism is ever
   wanted.
4. Determinism: assumed and documented, not proved in Lean — **per review** (#2).
5. No mathlib dependency — default yes.
6. Inventory per §2.6 (v1's determinism metatheory module replaced by the axiom audit) — trims
   or additions welcome.

## 6. Sources

- klean: `pyk.klean` in [kframework 7.1.337](https://pypi.org/project/kframework/)
  ([source](https://github.com/runtimeverification/k/tree/master/pyk))
- Prior art: [runtimeverification/evm-equivalence](https://github.com/runtimeverification/evm-equivalence)
- Local evidence: `lean/experiments/smoke2-lean` (builds green; §1.3), klean-on-MPY failure (§1.4)

---

## 7. Execution outcome (2026-07-14)

- **S0–S3 delivered.** The planned Makefile `lean-*` targets were folded into documented
  script entry points instead (`lean/README.md` + repo `CLAUDE.md`); everything else as
  specified, `lake build` green at the statement stage.
- **S4 probe: smooth branch taken, and further.** LA1 proved; per the pre-agreed policy the
  mechanical class followed — LA2, the LC3 chain, the LC3 refutation with witness
  `⟨0, trace⟩` — plus LA3 (collatz_steps, 491 steps), added beyond the plan's minimum. The
  §2.5 "elaboration time" risk materialized only as recursion depth: the `tran`-fold
  overflows the elaborator's default `maxRecDepth` past ~250 steps, so the generator emits
  `set_option maxRecDepth (16×steps)`. Discharging step hypotheses took three mechanisms
  beyond `rfl` (simp with equation lemmas for `@[irreducible]` WF-recursive functions, one
  interpretation axiom for the String-equality hook, explicit `HOLE`/`K0` arguments on cool
  constructors); all recorded in the repo `CLAUDE.md`.
- **Audit (LX).** The five proved theorems depend on `propext`, `Classical.choice`,
  `Quot.sound`, the String-hook symbol, and `eqStringHook` — nothing else. `sorryAx` is
  confined to the four staged statements (LB1's two paths, LC1, LC2); LB2's loop-step lemma
  enters with LC1's induction. Those remain for the interactive session, as agreed.
- **Measured costs.** Config sweep ≈ 2.8 s/step (dominant; the 491-step sweep ≈ 23 min);
  proof checking ≈ 60 ms/step; whole package ≈ 40 s. A from-scratch `--prove` regeneration
  reproduced the previously committed trace files byte for byte.
