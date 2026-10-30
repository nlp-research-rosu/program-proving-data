import KMiniPy.Verification.C31KbNestedWithBranchLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C31KbNestedWithBranch: `kb_nested_with_branch` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C31KbNestedWithBranchLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C31KbNestedWithBranch

open C31KbNestedWithBranchLegs

/-- Precondition: at program start, with the K claim's `A >=Int 1 ∧ B >=Int 1`. -/
def pre (a b : Int) : Pat := fun γ => γ = init a b ∧ 1 ≤ a ∧ 1 ≤ b

/-- Postcondition: terminated with the Gauss count of admitted iterations
`res ↦ (min a b * (min a b + 1)) / 2`, `i ↦ 0`, `j ↦ 0`. -/
def post (a b : Int) : Pat := pat (final a b ((min a b * (min a b + 1)) / 2) 0 0)

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) := by
  sorry

end C31KbNestedWithBranch
