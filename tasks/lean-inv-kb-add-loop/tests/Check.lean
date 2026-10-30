import KMiniPy.Verification.C15KbAddLoop

open RLogic

namespace HarborCheck

def refPre (n res a : Int) : Pat := pat (C15KbAddLoopLegs.init n res a)

def refPost (n res a : Int) : Pat := pat (C15KbAddLoopLegs.final (min n 0) (res + a * max n 0) a)

theorem check (n res a : SortInt) : RLOne (refPre n res a) (refPost n res a) :=
  C15KbAddLoop.spec n res a

end HarborCheck

#print axioms HarborCheck.check
