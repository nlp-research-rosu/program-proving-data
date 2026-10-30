import KMiniPy.Verification.C9KbAbsPaths
import KMiniPy.RL

/-! # C9KbAbs: reachability-logic derivation over `KMiniPy.Verification.C9KbAbsPaths`
(the proved path theorems; split out of the corpus file for this task). -/

open RLogic

namespace C9KbAbs

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a : Int) : Pat := fun γ =>
  ∃ r : Int, γ = final a (iV r) ∧ 0 ≤ r ∧ (r = a ∨ r = 0 - a)

/-- Branch under `a < 0`, total in the inputs: on the branch the proved
path enters as an Axiom over `SRew`; on its infeasible side the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem branch_neg (a : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pat (init a) γ ∧ a < 0, post a) :=
  if h : a < 0 then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg (path_neg a h))
      (fun _γ hγ => ⟨0 - a, hγ, by omega, Or.inr rfl⟩)
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Branch under `0 ≤ a`, total in the inputs: on the branch the proved
path enters as an Axiom over `SRew`; on its infeasible side the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem branch_nonneg (a : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pat (init a) γ ∧ 0 ≤ a, post a) :=
  if h : 0 ≤ a then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg (path_nonneg a h))
      (fun _γ hγ => ⟨a, hγ, h, Or.inl rfl⟩)
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Every pre-state satisfies one of the two branch patterns. -/
theorem split (a : Int) : ∀ γ, pat (init a) γ →
    (pat (init a) γ ∧ a < 0) ∨ (pat (init a) γ ∧ 0 ≤ a) :=
  fun _γ hγ => if h : a < 0 then Or.inl ⟨hγ, h⟩ else Or.inr ⟨hγ, by omega⟩

/-- C9KbAbs K-claim mirror (c9_kb_abs): res ends as |a|; a unchanged.
Case Analysis over the two machine-checked paths, C2 style. -/
theorem spec (a : SortInt) :
    RLOne (pat (init a)) (post a) :=
  .conseq (split a) (.caseA (branch_neg a)
    (branch_nonneg a)) (fun _ h => h)

end C9KbAbs
