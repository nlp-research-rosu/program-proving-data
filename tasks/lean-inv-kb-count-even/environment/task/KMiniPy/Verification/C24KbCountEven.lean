import KMiniPy.Verification.C24KbCountEvenLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C24KbCountEven: `kb_count_even` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C24KbCountEvenLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C24KbCountEven

open C24KbCountEvenLegs

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 0 ≤ n

/-- Postcondition: terminated with `count ↦ (n + 1) / 2` — the number of
even integers in `[0, n)` — and `i ↦ n`. -/
def post (n : Int) : Pat := pat (final n ((n + 1) / 2) n)

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) := by
  sorry

end C24KbCountEven
