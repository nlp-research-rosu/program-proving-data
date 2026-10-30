import KMiniPy.Verification.C30KbRowsSumNested

open RLogic

namespace HarborCheck

def refPre (a b : Int) : Pat := fun γ => γ = C30KbRowsSumNestedLegs.init a b ∧ 1 ≤ a

def refPost (a b : Int) : Pat :=
  pat (C30KbRowsSumNestedLegs.final a b ((max b 0 * (max b 0 + 1)) / 2 * a) 0 (min b 0))

theorem check (a b : SortInt) : RLOne (refPre a b) (refPost a b) :=
  C30KbRowsSumNested.spec a b

end HarborCheck

#print axioms HarborCheck.check
