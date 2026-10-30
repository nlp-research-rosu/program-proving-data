import KMiniPy.Verification.C17KbMax3Paths
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_max3` (C17KbMax3). `statement` is
what `C17KbMax3.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C17KbMax3Spec

open C17KbMax3

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a b n : Int) : Pat := fun γ =>
  ∃ m : Int, γ = final a b n (iV m) ∧ a ≤ m ∧ b ≤ m ∧ n ≤ m ∧ (m = a ∨ m = b ∨ m = n)

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a b n : SortInt), RLOne (pat (init a b n)) (post a b n)

end C17KbMax3Spec
