import KMiniPy.Verification.C34KbNormalizeCountLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C34KbNormalizeCount: `kb_normalize_count` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C34KbNormalizeCountLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C34KbNormalizeCount

open C34KbNormalizeCountLegs

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (a b n : Int) : Pat := pat (init a b n)

/-- Postcondition: terminated with `a`, `b` unchanged, `n ↦ 0`,
`count ↦ max n (0 - n)` (= `|n|`) and `res ↦ (max n (0 - n)) * a + b`. -/
def post (a b n : Int) : Pat := pat (final a b (max n (0 - n)) ((max n (0 - n)) * a + b))

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b n : SortInt) : RLOne (pre a b n) (post a b n) := by
  sorry

end C34KbNormalizeCount
