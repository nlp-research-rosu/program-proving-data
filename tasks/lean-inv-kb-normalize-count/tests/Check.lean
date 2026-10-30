import KMiniPy.Verification.C34KbNormalizeCount

open RLogic

namespace HarborCheck

def refPre (a b n : Int) : Pat := pat (C34KbNormalizeCountLegs.init a b n)

def refPost (a b n : Int) : Pat := pat (C34KbNormalizeCountLegs.final a b (max n (0 - n)) ((max n (0 - n)) * a + b))

theorem check (a b n : SortInt) : RLOne (refPre a b n) (refPost a b n) :=
  C34KbNormalizeCount.spec a b n

end HarborCheck

#print axioms HarborCheck.check
