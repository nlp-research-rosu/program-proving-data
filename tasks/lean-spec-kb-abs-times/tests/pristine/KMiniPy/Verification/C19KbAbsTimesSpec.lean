import KMiniPy.Verification.C19KbAbsTimesPaths
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_abs_times` (C19KbAbsTimes). `statement` is
what `C19KbAbsTimes.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C19KbAbsTimesSpec

open C19KbAbsTimes

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a b : Int) : Pat := fun γ =>
  ∃ t r : Int, γ = final a b (iV t) (iV r) ∧ 0 ≤ t ∧ (t = a ∨ t = 0 - a) ∧ r = t * b

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a b : SortInt), RLOne (pat (init a b)) (post a b)

end C19KbAbsTimesSpec
