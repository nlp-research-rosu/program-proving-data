import KMiniPy.Verification.C28KbTriangleNested

open RLogic

namespace HarborCheck

def refPre (n : Int) : Pat := fun γ => γ = C28KbTriangleNestedLegs.init n ∧ 1 ≤ n

def refPost (n : Int) : Pat := pat (C28KbTriangleNestedLegs.final n ((n * (n + 1)) / 2) 0 0)

theorem check (n : SortInt) : RLOne (refPre n) (refPost n) :=
  C28KbTriangleNested.spec n

end HarborCheck

#print axioms HarborCheck.check
