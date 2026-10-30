import KMiniPy.Verification.C21KbMultLoop

open RLogic

namespace HarborCheck

def refPre (n a : Int) : Pat := pat (C21KbMultLoopLegs.init n a)

def refPost (n a : Int) : Pat := pat (C21KbMultLoopLegs.final (min n 0) a (a * max n 0))

theorem check (n a : SortInt) : RLOne (refPre n a) (refPost n a) :=
  C21KbMultLoop.spec n a

end HarborCheck

#print axioms HarborCheck.check
