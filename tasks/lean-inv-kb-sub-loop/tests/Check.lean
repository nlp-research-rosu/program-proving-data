import KMiniPy.Verification.C16KbSubLoop

open RLogic

namespace HarborCheck

def refPre (a b : Int) : Pat := pat (C16KbSubLoopLegs.init a b)

def refPost (a b : Int) : Pat := pat (C16KbSubLoopLegs.final (a - max b 0) (min b 0))

theorem check (a b : SortInt) : RLOne (refPre a b) (refPost a b) :=
  C16KbSubLoop.spec a b

end HarborCheck

#print axioms HarborCheck.check
