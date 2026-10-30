import KMiniPy.Verification.C25KbLoopMaxLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C25KbLoopMax: `kb_loop_max` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C25KbLoopMaxLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C25KbLoopMax

open C25KbLoopMaxLegs

/-- Precondition: at program start, with `1 ≤ n` as a logical constraint. -/
def pre (a n : Int) : Pat := fun γ => γ = init a n ∧ 1 ≤ n

/-- Postcondition: terminated with `m ↦ max a (n - 1)` and `i ↦ n`. -/
def post (a n : Int) : Pat := pat (final a n (max a (n - 1)) n)

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a n : SortInt) : RLOne (pre a n) (post a n) := by
  sorry

end C25KbLoopMax
