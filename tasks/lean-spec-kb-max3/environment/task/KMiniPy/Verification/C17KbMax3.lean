import KMiniPy.Verification.C17KbMax3Paths
import KMiniPy.RL

/-! # C17KbMax3: `kb_max3` — the functional spec, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C17KbMax3Paths`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement (and
`post`) are frozen. -/

open RLogic

namespace C17KbMax3

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a b n : Int) : Pat := fun γ =>
  ∃ m : Int, γ = final a b n (iV m) ∧ a ≤ m ∧ b ≤ m ∧ n ≤ m ∧ (m = a ∨ m = b ∨ m = n)

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b n : SortInt) :
    RLOne (pat (init a b n)) (post a b n) := by
  sorry

end C17KbMax3
