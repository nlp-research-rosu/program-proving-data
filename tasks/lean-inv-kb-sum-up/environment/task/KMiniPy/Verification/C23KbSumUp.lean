import KMiniPy.Verification.C23KbSumUpLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C23KbSumUp: `kb_sum_up` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C23KbSumUpLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C23KbSumUp

open C23KbSumUpLegs

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 0 ≤ n

/-- Postcondition: terminated, with `sum ↦ n*(n+1)/2` (the K claim's Gauss
closed form) and `i ↦ n + 1`. -/
def post (n : Int) : Pat := pat (final n ((n * (n + 1)) / 2) (n + 1))

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) := by
  sorry

end C23KbSumUp
