import KMiniPy.Verification.C11KbMinPaths
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_min` (C11KbMin). `statement` is
what `C11KbMin.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C11KbMinSpec

open C11KbMin

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a b : Int) : Pat := fun γ =>
  ∃ m : Int, γ = final a b (iV m) ∧ m ≤ a ∧ m ≤ b ∧ (m = a ∨ m = b)

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a b : SortInt), RLOne (pat (init a b)) (post a b)

end C11KbMinSpec
