import KMiniPy.Rewrite

/-! # Reachability Logic — the K verifier's proof system, as trust base

Transcription of the proof system of Ştefănescu, Park, Yuwen, Li, Roşu,
"Semantics-Based Program Verifiers for All Languages", OOPSLA 2016, Figure 4
(both one-path `⇒∃` and all-path `⇒∀` reachability, index `PathQ`).

This is the proof system that K's `kprove` implements. It is encoded as an
inductive **derivability** judgment: the constructors ARE the proof rules,
postulated as the trust base — nothing here is derived from `Rewrites`, and no
soundness theorem is formalized (that is the paper's Theorem 1, trusted on
paper). Being an inductive, the encoding adds **zero axioms**: `#print axioms`
on theorems proved with it shows nothing new, and consistency is free.

Statement taxonomy for this package: **execution claims** (concrete traces,
symbolic paths) use `Rewrites` — finite, terminating runs. **Verification
claims** (pre/post specs, invariants) use reachability — this judgment.
`Rewrites` implies reachability (a proved leg enters a derivation through
`axm`; semantically, `Reaches.of_rewrites`); the converse would require a
termination proof, which partial-correctness verification deliberately omits.

Shallow encoding, with four documented adaptations from the paper's notation:
1. Claims are CLOSED pairs of patterns. Free variables of the paper's open
   rules become Lean binders outside the judgment: LHS variables (universally
   quantified) are theorem parameters or set-comprehension indices; variables
   occurring only on the RHS (K's `?`-variables, existentially quantified) are
   `∃` inside the right pattern. Instantiating a claim family from `A`/`C` is
   plain membership — this realizes the Axiom+Substitution combination of the
   predecessor systems (LICS'13, RTA'14), which Figure 4 omits but its own
   worked example uses.
2. `abstr` (the paper's Abstraction, `∃X φ ⇒ φ'`) is infinitary: one premise
   per instance, as a Lean `∀`-premise. The freshness side condition
   `X ∩ FreeVars(φ') = ∅` is enforced by types (`φ'` does not depend on `v`).
3. The implication premises of `step`/`conseq` are propositional inclusions of
   patterns — validity in the fixed configuration model, per the paper's
   implementation reading.
4. `step` concludes only `⇒∀` claims, as in the paper; the `⇒∃` system takes
   execution steps through `axm` with rules from `S`.

The "at least one step before circularities unlock" discipline is structural,
exactly as in the paper: `refl` requires the circularity set empty, `trans`
gives its second premise `A ∪ C` with an emptied circularity set, and `axm`
reads only `S ∪ A`. -/

namespace RLogic

/-- A pattern: a set of configurations (matching-logic pattern, shallowly). -/
abbrev Pat : Type := SortGeneratedTopCell → Prop

/-- A (closed) reachability claim `φ ⇒ φ'`. -/
abbrev Claim : Type := Pat × Pat

/-- Sets of claims, as predicates (no library dependency). -/
abbrev ClaimSet : Type := Claim → Prop

def ClaimSet.empty : ClaimSet := fun _ => False
def ClaimSet.union (A B : ClaimSet) : ClaimSet := fun c => A c ∨ B c
def ClaimSet.insert (c : Claim) (C : ClaimSet) : ClaimSet := fun c' => c' = c ∨ C c'

/-- The path quantifier: `⇒∃` (one-path) or `⇒∀` (all-path). -/
inductive PathQ | one | all

/-- The singleton pattern of one configuration. -/
def pat (a : SortGeneratedTopCell) : Pat := fun γ => γ = a

/-- Reachability-logic derivability: `RL S A C q (φ, φ')` encodes the sequent
`S, A ⊢_C φ ⇒Q φ'` of OOPSLA'16 Figure 4. `S` is the semantics (a set of
claims), `A` the axioms, `C` the not-yet-unlocked circularities. -/
inductive RL (S : ClaimSet) : ClaimSet → ClaimSet → PathQ → Claim → Prop where
  /-- Step (all-path only): every configuration matching `φ` matches the LHS
  of some rule of `S` (progress), and for every rule of `S`, every successor
  of a `φ`-configuration by that rule matches `φ'`. -/
  | step {A C : ClaimSet} {φ φ' : Pat}
      (progress : ∀ γ, φ γ → ∃ c, S c ∧ c.1 γ)
      (coverage : ∀ c, S c → (∃ γ₀, φ γ₀ ∧ c.1 γ₀) → ∀ γ', c.2 γ' → φ' γ') :
      RL S A C .all (φ, φ')
  /-- Axiom: apply a trusted rule of `S ∪ A`, with an optional logical frame
  `ψ` conjoined to both sides. -/
  | axm {A C : ClaimSet} {q : PathQ} {c : Claim} (ψ : Prop)
      (mem : S c ∨ A c) :
      RL S A C q (fun γ => c.1 γ ∧ ψ, fun γ => c.2 γ ∧ ψ)
  /-- Reflexivity — only with an empty circularity set (progress discipline). -/
  | refl {A : ClaimSet} {q : PathQ} {φ : Pat} :
      RL S A ClaimSet.empty q (φ, φ)
  /-- Transitivity; the second leg gains the circularities as axioms. -/
  | trans {A C : ClaimSet} {q : PathQ} {φ₁ φ₂ φ₃ : Pat}
      (leg₁ : RL S A C q (φ₁, φ₂))
      (leg₂ : RL S (ClaimSet.union A C) ClaimSet.empty q (φ₂, φ₃)) :
      RL S A C q (φ₁, φ₃)
  /-- Consequence: strengthen the LHS, weaken the RHS. -/
  | conseq {A C : ClaimSet} {q : PathQ} {φ₁ φ₁' φ₂' φ₂ : Pat}
      (pre : ∀ γ, φ₁ γ → φ₁' γ)
      (main : RL S A C q (φ₁', φ₂'))
      (post : ∀ γ, φ₂' γ → φ₂ γ) :
      RL S A C q (φ₁, φ₂)
  /-- Case analysis on the LHS. -/
  | caseA {A C : ClaimSet} {q : PathQ} {φ₁ φ₂ φ' : Pat}
      (left : RL S A C q (φ₁, φ'))
      (right : RL S A C q (φ₂, φ')) :
      RL S A C q (fun γ => φ₁ γ ∨ φ₂ γ, φ')
  /-- Abstraction: `∃`-abstract LHS-only variables (infinitary form). -/
  | abstr {α : Type} {A C : ClaimSet} {q : PathQ} {φ : α → Pat} {φ' : Pat}
      (inst : ∀ v : α, RL S A C q (φ v, φ')) :
      RL S A C q (fun γ => ∃ v, φ v γ, φ')
  /-- Circularity: postulate the goal, prove it with itself available (after
  progress) as an axiom. The coinductive rule. -/
  | circ {A C : ClaimSet} {q : PathQ} {c : Claim}
      (body : RL S A (ClaimSet.insert c C) q c) :
      RL S A C q c

/-! ## The semantics instantiation: machine-checked execution legs

`SRew` declares every proved `Rewrites` leg a semantic axiom. This is the
`rewrites ⇒ reachability` direction, stated once: it is admissible for the
per-rule semantics (fold Axiom over the individual rule applications with
Transitivity), and every leg is a valid one-path rule outright. The finer
per-rule instantiation of `S` (one claim family per K rule, steps via `step`)
is a drop-in refinement left for the all-path track. -/

def SRew : ClaimSet := fun c => ∃ a b, Rewrites a b ∧ c = (pat a, pat b)

/-- One-path reachability claims derivable in the calculus over `SRew` —
the form of this package's verification theorems. -/
abbrev RLOne (φ φ' : Pat) : Prop :=
  RL SRew ClaimSet.empty ClaimSet.empty .one (φ, φ')

/-- All-path counterpart (derivations would go through `step`; see `SRew`
notes). -/
abbrev RLAll (φ φ' : Pat) : Prop :=
  RL SRew ClaimSet.empty ClaimSet.empty .all (φ, φ')

/-! ## Derived conveniences (theorems, not trust base) -/

/-- A machine-checked execution leg, as a derivation step. -/
theorem RL.rw_leg {A C : ClaimSet} {q : PathQ} {a b : SortGeneratedTopCell}
    (h : Rewrites a b) : RL SRew A C q (pat a, pat b) :=
  .conseq (fun _ hγ => ⟨hγ, trivial⟩)
    (.axm True (Or.inl ⟨a, b, h, rfl⟩))
    (fun _ hγ => hγ.1)

/-- Frame-free Axiom. -/
theorem RL.axm' {S A C : ClaimSet} {q : PathQ} {c : Claim}
    (mem : S c ∨ A c) : RL S A C q c :=
  .conseq (fun _ hγ => ⟨hγ, trivial⟩)
    (.axm True mem)
    (fun _ hγ => hγ.1)

end RLogic
