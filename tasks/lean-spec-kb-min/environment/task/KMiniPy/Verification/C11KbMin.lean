import KMiniPy.Verification.C11KbMinPaths
import KMiniPy.RL

/-! # C11KbMin: `kb_min` — the functional spec, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C11KbMinPaths`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement (and
`post`) are frozen. -/

open RLogic

namespace C11KbMin

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a b : Int) : Pat := fun γ =>
  ∃ m : Int, γ = final a b (iV m) ∧ m ≤ a ∧ m ≤ b ∧ (m = a ∨ m = b)

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) :
    RLOne (pat (init a b)) (post a b) := by
  sorry

end C11KbMin
