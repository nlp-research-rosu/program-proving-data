import KMiniPy.Verification.C1SumToN

open RLogic

namespace HarborCheck

def refPre (n : Int) : Pat := fun γ => γ = C1Legs.init n ∧ 0 ≤ n

def refPost (n : Int) : Pat := pat (C1Legs.final (iV (n * (n + 1) / 2)))

theorem check (n : SortInt) : RLOne (refPre n) (refPost n) :=
  C1SumToN.gauss n

end HarborCheck

#print axioms HarborCheck.check
