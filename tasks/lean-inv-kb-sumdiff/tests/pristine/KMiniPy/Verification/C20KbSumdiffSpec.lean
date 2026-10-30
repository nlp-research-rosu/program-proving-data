import KMiniPy.Verification.C20KbSumdiffLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_sumdiff` (C20KbSumdiff). `statement` is
what `C20KbSumdiff.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C20KbSumdiffSpec

open C20KbSumdiffLegs

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (a b : Int) : Pat := pat (init a b)

/-- Postcondition: terminated with `a`, `b` unchanged, `t ↦ 0` and
`res ↦ 2 * max (a - b) (b - a)` — twice the absolute difference. -/
def post (a b : Int) : Pat := pat (final a b 0 (2 * max (a - b) (b - a)))

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a b : SortInt), RLOne (pre a b) (post a b)

end C20KbSumdiffSpec
