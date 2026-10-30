import KMiniPy.Verification.C17KbMax3Paths
import KMiniPy.RL

/-! # C17KbMax3: reachability-logic derivation over `KMiniPy.Verification.C17KbMax3Paths`
(the proved path theorems; split out of the corpus file for this task). -/

open RLogic

namespace C17KbMax3

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a b n : Int) : Pat := fun γ =>
  ∃ m : Int, γ = final a b n (iV m) ∧ a ≤ m ∧ b ≤ m ∧ n ≤ m ∧ (m = a ∨ m = b ∨ m = n)

/-- Branch under `a ≤ b ∧ b ≤ n`, total in the inputs: on the branch the proved
path enters as an Axiom over `SRew`; on its infeasible side the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem branch_le_le (a b n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pat (init a b n) γ ∧ a ≤ b ∧ b ≤ n, post a b n) :=
  if h1 : a ≤ b then
    if h2 : b ≤ n then
      .conseq (fun _ hp => hp.1)
        (RL.rw_leg (path_le_le a b n h1 h2))
        (fun _γ hγ => ⟨n, hγ, by omega, h2, by omega, Or.inr (Or.inr rfl)⟩)
    else
      .conseq (fun _ hp => absurd hp.2.2 h2)
        (.refl (φ := fun _ => False))
        (fun _ f => f.elim)
  else
    .conseq (fun _ hp => absurd hp.2.1 h1)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Branch under `a ≤ b ∧ n < b`, total in the inputs: on the branch the proved
path enters as an Axiom over `SRew`; on its infeasible side the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem branch_le_gt (a b n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pat (init a b n) γ ∧ a ≤ b ∧ n < b, post a b n) :=
  if h1 : a ≤ b then
    if h2 : n < b then
      .conseq (fun _ hp => hp.1)
        (RL.rw_leg (path_le_gt a b n h1 h2))
        (fun _γ hγ => ⟨b, hγ, h1, by omega, by omega, Or.inr (Or.inl rfl)⟩)
    else
      .conseq (fun _ hp => absurd hp.2.2 h2)
        (.refl (φ := fun _ => False))
        (fun _ f => f.elim)
  else
    .conseq (fun _ hp => absurd hp.2.1 h1)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Branch under `b < a ∧ a ≤ n`, total in the inputs: on the branch the proved
path enters as an Axiom over `SRew`; on its infeasible side the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem branch_gt_le (a b n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pat (init a b n) γ ∧ b < a ∧ a ≤ n, post a b n) :=
  if h1 : b < a then
    if h2 : a ≤ n then
      .conseq (fun _ hp => hp.1)
        (RL.rw_leg (path_gt_le a b n h1 h2))
        (fun _γ hγ => ⟨n, hγ, h2, by omega, by omega, Or.inr (Or.inr rfl)⟩)
    else
      .conseq (fun _ hp => absurd hp.2.2 h2)
        (.refl (φ := fun _ => False))
        (fun _ f => f.elim)
  else
    .conseq (fun _ hp => absurd hp.2.1 h1)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Branch under `b < a ∧ n < a`, total in the inputs: on the branch the proved
path enters as an Axiom over `SRew`; on its infeasible side the left
pattern is empty and Reflexivity closes it vacuously. -/
theorem branch_gt_gt (a b n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pat (init a b n) γ ∧ b < a ∧ n < a, post a b n) :=
  if h1 : b < a then
    if h2 : n < a then
      .conseq (fun _ hp => hp.1)
        (RL.rw_leg (path_gt_gt a b n h1 h2))
        (fun _γ hγ => ⟨a, hγ, by omega, by omega, by omega, Or.inl rfl⟩)
    else
      .conseq (fun _ hp => absurd hp.2.2 h2)
        (.refl (φ := fun _ => False))
        (fun _ f => f.elim)
  else
    .conseq (fun _ hp => absurd hp.2.1 h1)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Every pre-state satisfies one of the four branch patterns. -/
theorem split (a b n : Int) : ∀ γ, pat (init a b n) γ →
    ((pat (init a b n) γ ∧ a ≤ b ∧ b ≤ n) ∨ (pat (init a b n) γ ∧ a ≤ b ∧ n < b)) ∨ ((pat (init a b n) γ ∧ b < a ∧ a ≤ n) ∨ (pat (init a b n) γ ∧ b < a ∧ n < a)) :=
  fun _γ hγ =>
    if h1 : a ≤ b then
      if h2 : b ≤ n then Or.inl (Or.inl ⟨hγ, h1, h2⟩)
      else Or.inl (Or.inr ⟨hγ, h1, by omega⟩)
    else
      if h2 : a ≤ n then Or.inr (Or.inl ⟨hγ, by omega, h2⟩)
      else Or.inr (Or.inr ⟨hγ, by omega, by omega⟩)

/-- C17KbMax3 K-claim mirror (c17_kb_max3): max ends as the maximum of a, b and n; a, b and n unchanged.
Case Analysis over the four machine-checked paths, C2 style. -/
theorem spec (a b n : SortInt) :
    RLOne (pat (init a b n)) (post a b n) :=
  .conseq (split a b n) (.caseA (.caseA (branch_le_le a b n) (branch_le_gt a b n))
    (.caseA (branch_gt_le a b n) (branch_gt_gt a b n))) (fun _ h => h)

end C17KbMax3
