import KMiniPy.Verification.C18KbClampPaths
import KMiniPy.RL

/-! # C18KbClamp: `kb_clamp` — the functional spec, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C18KbClampPaths`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement (and
`post`) are frozen. -/

open RLogic

namespace C18KbClamp

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a : Int) : Pat := fun γ =>
  ∃ r : Int, γ = final a (iV r) ∧ r = min (max a 0) 10

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a : SortInt) :
    RLOne (pat (init a)) (post a) := by
  sorry

end C18KbClamp
