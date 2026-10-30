import KMiniPy.Verification.C30KbRowsSumNestedLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C30KbRowsSumNested: `kb_rows_sum_nested` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C30KbRowsSumNestedLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C30KbRowsSumNested

open C30KbRowsSumNestedLegs

/-- Precondition: at program start, with the K claim's `A >=Int 1`. -/
def pre (a b : Int) : Pat := fun γ => γ = init a b ∧ 1 ≤ a

/-- Postcondition: terminated with `sum ↦ (max b 0 * (max b 0 + 1)) / 2 * a`
(each of the `a` rows contributes the Gauss row sum; equivalent to the K
claim's `2*sum = a * maxInt(b,0) * (maxInt(b,0)+1)` by evenness of the
consecutive product), `i ↦ 0`, `j ↦ min b 0`, `a` and `b` unchanged. -/
def post (a b : Int) : Pat :=
  pat (final a b ((max b 0 * (max b 0 + 1)) / 2 * a) 0 (min b 0))

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) := by
  sorry

end C30KbRowsSumNested
