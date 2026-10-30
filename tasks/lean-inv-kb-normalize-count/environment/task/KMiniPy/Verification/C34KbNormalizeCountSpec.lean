import KMiniPy.Verification.C34KbNormalizeCountLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_normalize_count` (C34KbNormalizeCount). `statement` is
what `C34KbNormalizeCount.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C34KbNormalizeCountSpec

open C34KbNormalizeCountLegs

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (a b n : Int) : Pat := pat (init a b n)

/-- Postcondition: terminated with `a`, `b` unchanged, `n ↦ 0`,
`count ↦ max n (0 - n)` (= `|n|`) and `res ↦ (max n (0 - n)) * a + b`. -/
def post (a b n : Int) : Pat := pat (final a b (max n (0 - n)) ((max n (0 - n)) * a + b))

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a b n : SortInt), RLOne (pre a b n) (post a b n)

end C34KbNormalizeCountSpec
