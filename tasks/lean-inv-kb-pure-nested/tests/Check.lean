import KMiniPy.Verification.C26KbPureNested

open RLogic

namespace HarborCheck

def refPre (a b : Int) : Pat := fun γ => γ = C26KbPureNestedLegs.init a b ∧ 1 ≤ a

def refPost (a b : Int) : Pat := pat (C26KbPureNestedLegs.final a b 0 (min b 0))

theorem check (a b : SortInt) : RLOne (refPre a b) (refPost a b) :=
  C26KbPureNested.spec a b

end HarborCheck

#print axioms HarborCheck.check
