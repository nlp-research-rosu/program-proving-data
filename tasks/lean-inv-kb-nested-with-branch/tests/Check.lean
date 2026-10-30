import KMiniPy.Verification.C31KbNestedWithBranch

open RLogic

namespace HarborCheck

def refPre (a b : Int) : Pat := fun γ => γ = C31KbNestedWithBranchLegs.init a b ∧ 1 ≤ a ∧ 1 ≤ b

def refPost (a b : Int) : Pat := pat (C31KbNestedWithBranchLegs.final a b ((min a b * (min a b + 1)) / 2) 0 0)

theorem check (a b : SortInt) : RLOne (refPre a b) (refPost a b) :=
  C31KbNestedWithBranch.spec a b

end HarborCheck

#print axioms HarborCheck.check
