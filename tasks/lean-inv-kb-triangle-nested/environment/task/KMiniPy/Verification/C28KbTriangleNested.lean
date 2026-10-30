import KMiniPy.Verification.C28KbTriangleNestedLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C28KbTriangleNested: `kb_triangle_nested` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C28KbTriangleNestedLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C28KbTriangleNested

open C28KbTriangleNestedLegs

/-- Precondition: at program start, with the K claim's `N >=Int 1`. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 1 ≤ n

/-- Postcondition: terminated with the Gauss count `count ↦ (n*(n+1))/2`
and both loop counters drained (`i ↦ 0`, `j ↦ 0`), `n` unchanged. -/
def post (n : Int) : Pat := pat (final n ((n * (n + 1)) / 2) 0 0)

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) := by
  sorry

end C28KbTriangleNested
