import KMiniPy.Verification.C20KbSumdiffLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C20KbSumdiff: `kb_sumdiff` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C20KbSumdiffLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C20KbSumdiff

open C20KbSumdiffLegs

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (a b : Int) : Pat := pat (init a b)

/-- Postcondition: terminated with `a`, `b` unchanged, `t ↦ 0` and
`res ↦ 2 * max (a - b) (b - a)` — twice the absolute difference. -/
def post (a b : Int) : Pat := pat (final a b 0 (2 * max (a - b) (b - a)))

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) := by
  sorry

end C20KbSumdiff
