import KMiniPy.Verification.C29KbSquaresCubicLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C29KbSquaresCubic: `kb_squares_cubic` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C29KbSquaresCubicLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C29KbSquaresCubic

open C29KbSquaresCubicLegs

/-- Precondition: at program start, with the K claim's `N >=Int 1`. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 1 ≤ n

/-- Postcondition: terminated with `res ↦ n*(n+1)*(2*n+1)/6` (the K claim's
square-pyramidal ensures), both counters at `0`, `n` unchanged. -/
def post (n : Int) : Pat := pat (final n ((n * (n + 1) * (2 * n + 1)) / 6) 0 0)

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) := by
  sorry

end C29KbSquaresCubic
