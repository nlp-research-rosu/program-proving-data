import KMiniPy.Verification.C27KbMultNestedLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C27KbMultNested: `kb_mult_nested` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C27KbMultNestedLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C27KbMultNested

open C27KbMultNestedLegs

/-- Precondition: at program start, with the K claim's `A >=Int 1`. -/
def pre (a b : Int) : Pat := fun γ => γ = init a b ∧ 1 ≤ a

/-- Postcondition: terminated with `res ↦ max b 0 * a` (the K claim's
`?RES = A *Int maxInt(B, 0)`, omega-equal orientation), `i ↦ 0`,
`j ↦ min b 0`, `a` and `b` unchanged. -/
def post (a b : Int) : Pat := pat (final a b (max b 0 * a) 0 (min b 0))

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) := by
  sorry

end C27KbMultNested
