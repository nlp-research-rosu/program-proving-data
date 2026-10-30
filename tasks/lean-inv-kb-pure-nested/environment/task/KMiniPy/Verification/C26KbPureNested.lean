import KMiniPy.Verification.C26KbPureNestedLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C26KbPureNested: `kb_pure_nested` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C26KbPureNestedLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C26KbPureNested

open C26KbPureNestedLegs

/-- Precondition: at program start, with the K claim's `A >=Int 1`. -/
def pre (a b : Int) : Pat := fun γ => γ = init a b ∧ 1 ≤ a

/-- Postcondition: terminated with `i ↦ 0`, `j ↦ min b 0` (the K claim's
`?I2 = 0 ∧ ?J2 = minInt(B, 0)`), `a` and `b` unchanged. -/
def post (a b : Int) : Pat := pat (final a b 0 (min b 0))

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) := by
  sorry

end C26KbPureNested
