import KMiniPy.Verification.C19KbAbsTimesPaths
import KMiniPy.RL

/-! # C19KbAbsTimes: `kb_abs_times` — the functional spec, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C19KbAbsTimesPaths`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement (and
`post`) are frozen. -/

open RLogic

namespace C19KbAbsTimes

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a b : Int) : Pat := fun γ =>
  ∃ t r : Int, γ = final a b (iV t) (iV r) ∧ 0 ≤ t ∧ (t = a ∨ t = 0 - a) ∧ r = t * b

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) :
    RLOne (pat (init a b)) (post a b) := by
  sorry

end C19KbAbsTimes
