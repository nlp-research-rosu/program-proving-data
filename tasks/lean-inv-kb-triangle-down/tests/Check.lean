import KMiniPy.Verification.C22KbTriangleDown

open RLogic

namespace HarborCheck

def refPre (n : Int) : Pat := pat (C22KbTriangleDownLegs.init n)

def refPost (n : Int) : Pat := pat (C22KbTriangleDownLegs.final (min n 0) ((max n 0 * (max n 0 + 1)) / 2))

theorem check (n : SortInt) : RLOne (refPre n) (refPost n) :=
  C22KbTriangleDown.spec n

end HarborCheck

#print axioms HarborCheck.check
