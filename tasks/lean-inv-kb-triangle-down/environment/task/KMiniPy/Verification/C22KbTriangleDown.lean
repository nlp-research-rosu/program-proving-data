import KMiniPy.Verification.C22KbTriangleDownLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C22KbTriangleDown: `kb_triangle_down` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C22KbTriangleDownLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C22KbTriangleDown

open C22KbTriangleDownLegs

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (n : Int) : Pat := pat (init n)

/-- Postcondition: terminated with `n ↦ min n 0` and the descending
triangle sum `sum ↦ (max n 0 * (max n 0 + 1)) / 2`. -/
def post (n : Int) : Pat := pat (final (min n 0) ((max n 0 * (max n 0 + 1)) / 2))

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) := by
  sorry

end C22KbTriangleDown
