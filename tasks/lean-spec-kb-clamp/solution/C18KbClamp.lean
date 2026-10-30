import KMiniPy.Verification.C18KbClampPaths
import KMiniPy.RL

/-! # C18KbClamp: reachability-logic derivation over `KMiniPy.Verification.C18KbClampPaths`
(the proved path theorems; split out of the corpus file for this task). -/

open RLogic

namespace C18KbClamp

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a : Int) : Pat := fun γ =>
  ∃ r : Int, γ = final a (iV r) ∧ r = min (max a 0) 10

/-- Branch under `a < 0`, total in the inputs: on the branch the proved
path enters as an Axiom over `SRew`; on its infeasible side the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem branch_neg (a : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pat (init a) γ ∧ a < 0, post a) :=
  if h : a < 0 then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg (path_neg a h))
      (fun _γ hγ => ⟨0, hγ, by omega⟩)
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Branch under `0 ≤ a ∧ 10 < a`, total in the inputs: on the branch the proved
path enters as an Axiom over `SRew`; on its infeasible side the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem branch_hi (a : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pat (init a) γ ∧ 0 ≤ a ∧ 10 < a, post a) :=
  if h1 : 0 ≤ a then
    if h2 : 10 < a then
      .conseq (fun _ hp => hp.1)
        (RL.rw_leg (path_hi a h1 h2))
        (fun _γ hγ => ⟨10, hγ, by omega⟩)
    else
      .conseq (fun _ hp => absurd hp.2.2 h2)
        (.refl (φ := fun _ => False))
        (fun _ f => f.elim)
  else
    .conseq (fun _ hp => absurd hp.2.1 h1)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Branch under `0 ≤ a ∧ a ≤ 10`, total in the inputs: on the branch the proved
path enters as an Axiom over `SRew`; on its infeasible side the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem branch_mid (a : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pat (init a) γ ∧ 0 ≤ a ∧ a ≤ 10, post a) :=
  if h1 : 0 ≤ a then
    if h2 : a ≤ 10 then
      .conseq (fun _ hp => hp.1)
        (RL.rw_leg (path_mid a h1 h2))
        (fun _γ hγ => ⟨a, hγ, by omega⟩)
    else
      .conseq (fun _ hp => absurd hp.2.2 h2)
        (.refl (φ := fun _ => False))
        (fun _ f => f.elim)
  else
    .conseq (fun _ hp => absurd hp.2.1 h1)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Every pre-state satisfies one of the three branch patterns. -/
theorem split (a : Int) : ∀ γ, pat (init a) γ →
    (pat (init a) γ ∧ a < 0) ∨ ((pat (init a) γ ∧ 0 ≤ a ∧ 10 < a) ∨ (pat (init a) γ ∧ 0 ≤ a ∧ a ≤ 10)) :=
  fun _γ hγ =>
    if h : a < 0 then Or.inl ⟨hγ, h⟩
    else if h2 : 10 < a then Or.inr (Or.inl ⟨hγ, by omega, h2⟩)
    else Or.inr (Or.inr ⟨hγ, by omega, by omega⟩)

/-- C18KbClamp K-claim mirror (c18_kb_clamp): res ends as min(max(a, 0), 10); a unchanged.
Case Analysis over the three machine-checked paths, C2 style. -/
theorem spec (a : SortInt) :
    RLOne (pat (init a)) (post a) :=
  .conseq (split a) (.caseA (branch_neg a)
    (.caseA (branch_hi a) (branch_mid a))) (fun _ h => h)

end C18KbClamp
