import KMiniPy.Verification.C13KbCountup

open RLogic

namespace HarborCheck

def refPre (n r : Int) : Pat := pat (C13KbCountupLegs.init n r)

def refPost (n r : Int) : Pat := pat (C13KbCountupLegs.final n (max n r))

theorem check (n r : SortInt) : RLOne (refPre n r) (refPost n r) :=
  C13KbCountup.spec n r

end HarborCheck

#print axioms HarborCheck.check
