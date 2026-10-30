import KMiniPy.Verification.C10KbMaxPaths
import KMiniPy.RL

/-! # C10KbMax: reachability-logic derivation over `KMiniPy.Verification.C10KbMaxPaths`
(the proved path theorems; split out of the corpus file for this task). -/

open RLogic

namespace C10KbMax

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a b : Int) : Pat := fun γ =>
  ∃ m : Int, γ = final a b (iV m) ∧ a ≤ m ∧ b ≤ m ∧ (m = a ∨ m = b)

/-- Branch under `a ≤ b`, total in the inputs: on the branch the proved
path enters as an Axiom over `SRew`; on its infeasible side the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem branch_le (a b : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pat (init a b) γ ∧ a ≤ b, post a b) :=
  if h : a ≤ b then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg (path_le a b h))
      (fun _γ hγ => ⟨b, hγ, h, by omega, Or.inr rfl⟩)
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Branch under `b < a`, total in the inputs: on the branch the proved
path enters as an Axiom over `SRew`; on its infeasible side the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem branch_gt (a b : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pat (init a b) γ ∧ b < a, post a b) :=
  if h : b < a then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg (path_gt a b h))
      (fun _γ hγ => ⟨a, hγ, by omega, by omega, Or.inl rfl⟩)
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Every pre-state satisfies one of the two branch patterns. -/
theorem split (a b : Int) : ∀ γ, pat (init a b) γ →
    (pat (init a b) γ ∧ a ≤ b) ∨ (pat (init a b) γ ∧ b < a) :=
  fun _γ hγ => if h : a ≤ b then Or.inl ⟨hγ, h⟩ else Or.inr ⟨hγ, by omega⟩

/-- C10KbMax K-claim mirror (c10_kb_max): max ends as the maximum of a and b; a and b unchanged.
Case Analysis over the two machine-checked paths, C2 style. -/
theorem spec (a b : SortInt) :
    RLOne (pat (init a b)) (post a b) :=
  .conseq (split a b) (.caseA (branch_le a b)
    (branch_gt a b)) (fun _ h => h)

end C10KbMax
