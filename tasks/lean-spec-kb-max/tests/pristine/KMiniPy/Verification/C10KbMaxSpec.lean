import KMiniPy.Verification.C10KbMaxPaths
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_max` (C10KbMax). `statement` is
what `C10KbMax.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C10KbMaxSpec

open C10KbMax

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a b : Int) : Pat := fun γ =>
  ∃ m : Int, γ = final a b (iV m) ∧ a ≤ m ∧ b ≤ m ∧ (m = a ∨ m = b)

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a b : SortInt), RLOne (pat (init a b)) (post a b)

end C10KbMaxSpec
