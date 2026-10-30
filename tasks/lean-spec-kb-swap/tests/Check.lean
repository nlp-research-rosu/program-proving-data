import KMiniPy.Verification.C5KbSwap

open RLogic

namespace HarborCheck

theorem check (a b : SortInt) :
    RLOne (pat (C5KbSwap.init a b)) (pat (C5KbSwap.final a b)) :=
  C5KbSwap.spec a b

end HarborCheck

#print axioms HarborCheck.check
