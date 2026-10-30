import KMiniPy.Verification.C1Legs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C1SumToN: `sum_to_n` — the loop claim, to be derived

`gauss` states the one-path reachability claim of this program over
the proved execution legs of `C1Legs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C1SumToN

open C1Legs

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 0 ≤ n

/-- Postcondition: terminated, with `result ↦ n·(n+1)/2`. -/
def post (n : Int) : Pat := pat (final (iV (n * (n + 1) / 2)))

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem gauss (n : SortInt) : RLOne (pre n) (post n) := by
  sorry

end C1SumToN
