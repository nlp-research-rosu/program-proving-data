import KMiniPy.Verification.C9KbAbsPaths
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_abs` (C9KbAbs). `statement` is
what `C9KbAbs.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C9KbAbsSpec

open C9KbAbs

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a : Int) : Pat := fun γ =>
  ∃ r : Int, γ = final a (iV r) ∧ 0 ≤ r ∧ (r = a ∨ r = 0 - a)

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a : SortInt), RLOne (pat (init a)) (post a)

end C9KbAbsSpec
