import KMiniPy.Verification.C27KbMultNested

open RLogic

namespace HarborCheck

def refPre (a b : Int) : Pat := fun γ => γ = C27KbMultNestedLegs.init a b ∧ 1 ≤ a

def refPost (a b : Int) : Pat := pat (C27KbMultNestedLegs.final a b (max b 0 * a) 0 (min b 0))

theorem check (a b : SortInt) : RLOne (refPre a b) (refPost a b) :=
  C27KbMultNested.spec a b

end HarborCheck

#print axioms HarborCheck.check
