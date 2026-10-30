import KMiniPy.Verification.C18KbClampPaths
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_clamp` (C18KbClamp). `statement` is
what `C18KbClamp.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C18KbClampSpec

open C18KbClamp

/-- Postcondition: terminated with the full final scope pinned — the
result slot holds an integer satisfying the spec (K's `?`-variable,
existential inside the pattern). -/
def post (a : Int) : Pat := fun γ =>
  ∃ r : Int, γ = final a (iV r) ∧ r = min (max a 0) 10

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a : SortInt), RLOne (pat (init a)) (post a)

end C18KbClampSpec
