import KMiniPy.Verification.C21KbMultLoopLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C21KbMultLoop: `kb_mult_loop` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C21KbMultLoopLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C21KbMultLoop

open C21KbMultLoopLegs

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (n a : Int) : Pat := pat (init n a)

/-- Postcondition: terminated with `n ↦ min n 0`, `a` unchanged, and
`res ↦ a * max n 0` — the piecewise closed form of the counting loop. -/
def post (n a : Int) : Pat := pat (final (min n 0) a (a * max n 0))

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n a : SortInt) : RLOne (pre n a) (post n a) := by
  sorry

end C21KbMultLoop
