import KMiniPy.Verification.C14KbSumLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C14KbSum: `kb_sum` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C14KbSumLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C14KbSum

open C14KbSumLegs

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (n sum : Int) : Pat := fun γ => γ = init n sum ∧ 0 ≤ n

/-- Postcondition: terminated with `n ↦ 0` and the Gauss closed form
`sum ↦ sum + n*(n+1)/2` (the K claim's ensures; `/` is Int ediv, exact here
because `n*(n+1)` is even). -/
def post (n sum : Int) : Pat := pat (final 0 (sum + (n * (n + 1)) / 2))

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n sum : SortInt) : RLOne (pre n sum) (post n sum) := by
  sorry

end C14KbSum
