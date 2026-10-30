import KMiniPy.Verification.C7KbDoubleHalf

open RLogic

namespace HarborCheck

theorem check (a : SortInt) :
    RLOne (pat (C7KbDoubleHalf.init a)) (pat (C7KbDoubleHalf.final a)) :=
  C7KbDoubleHalf.spec a

end HarborCheck

#print axioms HarborCheck.check
