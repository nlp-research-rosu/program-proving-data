# CLAUDE.md — sample-data (K-generated trace data + K-to-Lean theorems)

Two deliverables live here, both under `data/`: `data/k/` (execution/symbolic/verification
traces from the klever MPY semantics) and `data/lean/` (a Lean 4 package: klean-generated
theorems over `semantics/minipy-lean.k`, with proofs). See README.md (map) + REPORT.md
(details); historical plans in `docs/`. The `kb_*` programs / `specs/kb-*` /
`c4+` verification records are ported KleverBench problems (upstream pin + port
conventions in programs/PROVENANCE.md; nothing vendored): module-level MiniPy, inputs as
magic literals replaced by symbolic ints in the claim, the ENTIRE final scope pinned
([all-path]), requires exactly the upstream intent's precondition, loop proofs as
`#while`-anchored circularity claims (one per loop level, inner first). Sources: programs in `programs/`, both K semantics in
`semantics/`, claims in `specs/`, all scripts in `scripts/{k,lean}/` + the shared
`scripts/py2mpy_traced.py` frontend. Vendored upstream in `vendor/klever/` is never modified.
Commit small and push often. Every K/Lean invocation runs
under `timeout` sized ~2x expected; these programs are tiny, so anything running longer than
minutes is stuck or looping — kill it and diagnose, never wait blindly or just raise the limit.
Subagents: run bounded commands (generators, builds — everything here is minutes) in the
FOREGROUND under `timeout`; if something must run in the background, wait for it with ONE
blocking until-loop — never spin no-op Bash calls ("idle await"): each spin is a full API
round-trip every few seconds against your whole context. (Recurred twice, 2026-07.)

## Writing K semantics that klean can translate (hard-won, 2026-07)

- klean (`python -m pyk.klean DEFN_DIR PKG -l LIB`) rejects hooked collection sorts: no
  Map/List/Set/Float anywhere reachable from rules. Use constructor sorts (assoc-list `Env`,
  `Frames`, `Vals`) with K-function lookup/update: those become computable Lean `def`s.
- Never subsort primitive values (`syntax Val ::= Int | Bool` breaks Lean unification: KORE
  collapses injections, rule patterns inject through `Val`). Wrap: `intV(Int) | boolV(Bool)`.
- Branch results of statement sort must go through a KItem wrapper (`execStmts(Stmts)` +
  unpack rule). A bare `If(true, T, _) => T` with `T:Stmts` makes the rule parser wrap the LHS
  in a singleton statement list that never matches runtime bare-`Stmt` items.
- Avoid `==K` in requires (needs explicit `imports K-EQUAL`); prefer tiny Bool discriminator
  functions (`isBound(OptVal)`), which stay first-order in Lean.
- Label every rule: labels become the `Rewrites` constructor names (unlabeled rules get
  `_<uid7>` hash names; heat/cool rules get auto-labels escaped as `«...»`).

## Proving execution theorems in Lean 4 against klean output

- klean's `Rewrites` is one-or-more-step rewriting (a `tran` constructor is baked in; there is
  no refl/⇒*/divergence/reachability — `data/lean/KMiniPy/Relations.lean` adds `MultiStep`,
  `Diverges`, `Reaches` = one-path reachability, all definable over `Rewrites` alone).
- Proof architecture that works: one named theorem per rewrite step with EXPLICIT configs
  (`step_k : Rewrites c_k c_{k+1}`, configs from a `krun --depth` sweep, rule names from
  `krun --proof-hint` + `kore-proof-trace` depth-0 stream, terms printed with pyk.klean's own
  `_transform_pattern`), folded by `tran`. A single chain with implicit intermediate configs
  stalls elaboration wherever unification must invert a function.
- The tran-fold nests one application per step: past ~250 steps the elaborator's default
  `maxRecDepth` (512) overflows on the proof term — the generator emits
  `set_option maxRecDepth (16×steps) in` before `trace` (491-step collatz needed this).
- Hypothesis discharge is ONE uniform tactic (see `TACTIC` in `scripts/lean/gen_lean_traces.py`):
  `first | rfl | (simp [<WF-mutual fn defs + rule-branch defs>, eqStringHook, guard] <;> rfl)`.
  Recursive K functions compile to well-founded-recursion defs (no literal attribute, but
  behaviorally irreducible) — `rfl`/`decide` can never reduce them; `simp` with their equation
  lemmas is required. Non-recursive defs close by `rfl`.
- klean emits String-equality as a signature-only axiom: add one interpretation axiom
  (`eqStringHook : «_==String_…» s t = some (s == t)`, in Relations.lean) or every
  skip-an-entry lookup/update and non-empty flookup is a stuck term no tactic closes.
- `*_cool` constructors need their `SortExpr`-typed implicits passed EXPLICITLY
  (`(HOLE := …)`, `(K0 := …)`): the `Inj SortExpr SortKItem` instance is a normalizing match,
  so `inj ?HOLE` never unifies with the collapsed `SortKItem.inj_SortVal v`. The generator
  recovers values by structurally matching the rule's kore LHS against the step's source config
  (`match_lhs`; heat/cool redex heads hide under `\and` alias nodes).
- ∀-quantified path theorems (B-category) generate like traces (`scripts/lean/gen_lean_paths.py`):
  run the path at a witness input, parameterize every printed config by full-template text
  substitution (longest-first; assert no witness literal survives), add `(x h)` binders to each
  step theorem, extend TACTIC's simp set with the applyCmp/applyBin branch defs + Int hooks and
  the closer to `<;> first | rfl | omega` — omega reads the path condition from the binders.
- Equal-on-path variables (classify_triangle): witness values collide, making textual
  parameterization ambiguous — prove an internal reduced lemma over one variable per
  equivalence class, then derive the frozen public theorem by `subst`.
- omega over the `SortInt` abbrev is orientation-sensitive: from `h : b ≠ c` it closes
  `¬b = c` but not `¬c = b` — step theorems carry both orientations, folds pass `h (Ne.symm h)`.
- omega REFUSES a goal whose head is `@Eq SortInt` ("no usable constraints") even though
  SortInt is a reducible abbrev of Int — comparisons (`<`, `≤`) at SortInt are fine, value
  equalities are not. The path TACTIC retypes with `(try show @Eq Int _ _)` before omega
  (verified: with the retype, SortInt-headed `+`/`-` inside the goal are read fine).
- klean's Prelude applies `Int.emod`/`Int.ediv`/`Int.tdiv` as RAW constants; omega only
  reads the `%`/`/` notation heads. Relations.lean's `intEmodEq`/`intEdivEq` rfl-lemmas
  (in the paths simp set) restore notation; K's `_/Int_` is `Int.tdiv`, which omega never
  reads — the TACTIC closer bridges it via `rw [Int.tdiv_eq_ediv_of_dvd (by omega)]`
  (the divisibility side goal is omega-provable once notation is restored). Symbolic `//`
  and `%` also need floorDiv/floorMod (+ inner uids) in the simp set — see SIMP_NAMES.
- Credibility: `KMiniPy/AxiomAudit.lean` runs `#print axioms` per theorem — proved traces must
  show only core axioms + the two String-hook axioms: klean's signature-only `«_==String_…»`
  symbol and `eqStringHook` interpreting it (jointly consistent: model `fun s t => some (s == t)`).
  `sorryAx` means a stub is still in. klean's stock Prelude also declares 41 unreachable
  collection-hook axioms — the guarantee is the per-theorem audit output, not a package-wide
  `grep axiom`.
- Costs (8-core VPS): kompile 2–5 min; klean seconds; config sweep ≈ 1 krun/step (the dominant
  cost, ~10 min for a 224-step program); lake ≈ 60 ms/step, whole package ~15 s.
- `grep -c` exits 1 on zero matches — don't use it as a success check in command chains.
- In chained background commands, gate `git commit && git push` on `lake build` with `&&`,
  never `;` — and `lake build | tail` launders the exit code (pipeline status is tail's).
  A red build got pushed this way once.

## Reachability logic (verification claims) — data/lean/KMiniPy/RL.lean

- Statement taxonomy: execution claims (traces, symbolic paths) use `Rewrites`; VERIFICATION
  claims use reachability — the RL derivability judgment. Never state a verification claim
  with `Rewrites`: that silently adds a termination obligation (this mistake was made once).
- RL is OOPSLA'16 Figure 4 as an inductive: constructors = the eight rules, trust base, no
  soundness proof, zero axioms added. `SRew` = every proved `Rewrites` leg is a semantic
  axiom (the rewrites ⇒ reachability direction). One-path derivations step via `axm`; `step`
  is ∀-only and unused here (deterministic language; per-rule S is the documented refinement).
- Derivation recipe (see C1SumToN.lean): Transitivity(prologue leg, Circularity(∃-packed
  invariant claim) → Consequence-reshape → Abstraction over a witness structure (constraints
  become hypotheses) → guard `if` split → back edge = Axiom on the flushed circularity
  (membership is nested Or over the unfolded ClaimSet unions); exit branch = one composed
  Rewrites leg. Loop residue: whileUnfold leaves one nil statement-list frame per iteration —
  legs carry the continuation (`loopCfg n i acc rest`), the invariant carries a `NilStack`
  predicate, and the exit drains it by NilStack induction at the Rewrites level (leg gluing,
  not termination).
- Gauss-style arithmetic in Consequence: normalize (`Int.mul_add`, `Int.sub_mul`,
  `Int.add_sub_cancel`), then `generalize i * i = m` (core omega rejects var*var but handles
  division by literal constants), then omega. Core omega also cannot read comparisons typed
  at the `SortInt` abbrev constant — declare helper binders as `Int` (defeq; keep frozen
  public signatures at `SortInt`).

## Regeneration entry points

- Trace dataset: `make k-data && make k-validate` (see Makefile; normalizations in REPORT.md).
- Lean: `make lean-gen` (kompiles `build/lean/minipy-lean{,-hints}`, regenerates mpy + theorem
  files; idempotent vs the committed package) then `make lean-build` (PATH needs
  `$HOME/.elan/bin`). klean base modules are regenerated manually in a scratch dir — klean
  emits a whole package skeleton and its Inj/Func declaration order is nondeterministic. Stale
  `build/lean/hints-header.bin` after a rekompile segfaults `kore-proof-trace` — the hints
  kompile target deletes the derived hints artifacts.
