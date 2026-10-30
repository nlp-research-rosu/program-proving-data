import KMiniPy.Verification.C19KbAbsTimesPaths
import KMiniPy.RL

/-! # C19KbAbsTimes: reachability-logic derivation over `KMiniPy.Verification.C19KbAbsTimesPaths`
(the proved path theorems; split out of the corpus file for this task). -/

open RLogic

namespace C19KbAbsTimes

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a b : Int) : Pat := fun γ =>
  ∃ t r : Int, γ = final a b (iV t) (iV r) ∧ 0 ≤ t ∧ (t = a ∨ t = 0 - a) ∧ r = t * b

/-- Branch under `a < 0`, total in the inputs: on the branch the proved
path enters as an Axiom over `SRew`; on its infeasible side the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem branch_neg (a b : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pat (init a b) γ ∧ a < 0, post a b) :=
  if h : a < 0 then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg (path_neg a b h))
      (fun _γ hγ => ⟨0 - a, (0 - a) * b, hγ, by omega, Or.inr rfl, rfl⟩)
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Branch under `0 ≤ a`, total in the inputs: on the branch the proved
path enters as an Axiom over `SRew`; on its infeasible side the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem branch_nonneg (a b : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pat (init a b) γ ∧ 0 ≤ a, post a b) :=
  if h : 0 ≤ a then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg (path_nonneg a b h))
      (fun _γ hγ => ⟨a, a * b, hγ, h, Or.inl rfl, rfl⟩)
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Every pre-state satisfies one of the two branch patterns. -/
theorem split (a b : Int) : ∀ γ, pat (init a b) γ →
    (pat (init a b) γ ∧ a < 0) ∨ (pat (init a b) γ ∧ 0 ≤ a) :=
  fun _γ hγ => if h : a < 0 then Or.inl ⟨hγ, h⟩ else Or.inr ⟨hγ, by omega⟩

/-- C19KbAbsTimes K-claim mirror (c19_kb_abs_times): t ends as |a| and res as |a| * b; a and b unchanged.
Case Analysis over the two machine-checked paths, C2 style. -/
theorem spec (a b : SortInt) :
    RLOne (pat (init a b)) (post a b) :=
  .conseq (split a b) (.caseA (branch_neg a b)
    (branch_nonneg a b)) (fun _ h => h)

end C19KbAbsTimes
