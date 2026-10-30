import KMiniPy.Verification.C31KbNestedWithBranchLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_nested_with_branch` (C31KbNestedWithBranch). `statement` is
what `C31KbNestedWithBranch.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C31KbNestedWithBranchSpec

open C31KbNestedWithBranchLegs

/-- Precondition: at program start, with the K claim's `A >=Int 1 ∧ B >=Int 1`. -/
def pre (a b : Int) : Pat := fun γ => γ = init a b ∧ 1 ≤ a ∧ 1 ≤ b

/-- Postcondition: terminated with the Gauss count of admitted iterations
`res ↦ (min a b * (min a b + 1)) / 2`, `i ↦ 0`, `j ↦ 0`. -/
def post (a b : Int) : Pat := pat (final a b ((min a b * (min a b + 1)) / 2) 0 0)

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a b : SortInt), RLOne (pre a b) (post a b)

end C31KbNestedWithBranchSpec
