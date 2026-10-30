import KMiniPy.Verification.C20KbSumdiff

open RLogic

namespace HarborCheck

def refPre (a b : Int) : Pat := pat (C20KbSumdiffLegs.init a b)

def refPost (a b : Int) : Pat := pat (C20KbSumdiffLegs.final a b 0 (2 * max (a - b) (b - a)))

theorem check (a b : SortInt) : RLOne (refPre a b) (refPost a b) :=
  C20KbSumdiff.spec a b

end HarborCheck

#print axioms HarborCheck.check
