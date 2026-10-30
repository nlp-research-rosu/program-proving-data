import KMiniPy.Verification.C12KbCountdownLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C12KbCountdown: `kb_countdown` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C12KbCountdownLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C12KbCountdown

open C12KbCountdownLegs

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 0 ≤ n

/-- Postcondition: terminated, with `n ↦ 0` (the K claim's `?F ==Int 0`). -/
def post (n : Int) : Pat := pat (final 0)

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) := by
  sorry

end C12KbCountdown
