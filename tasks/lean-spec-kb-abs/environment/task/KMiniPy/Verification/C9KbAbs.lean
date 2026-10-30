import KMiniPy.Verification.C9KbAbsPaths
import KMiniPy.RL

/-! # C9KbAbs: `kb_abs` — the functional spec, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C9KbAbsPaths`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement (and
`post`) are frozen. -/

open RLogic

namespace C9KbAbs

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a : Int) : Pat := fun γ =>
  ∃ r : Int, γ = final a (iV r) ∧ 0 ≤ r ∧ (r = a ∨ r = 0 - a)

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a : SortInt) :
    RLOne (pat (init a)) (post a) := by
  sorry

end C9KbAbs
