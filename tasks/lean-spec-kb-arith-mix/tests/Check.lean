import KMiniPy.Verification.C8KbArithMix

open RLogic

namespace HarborCheck

theorem check (a b : SortInt) :
    RLOne (pat (C8KbArithMix.init a b)) (pat (C8KbArithMix.final a b)) :=
  C8KbArithMix.spec a b

end HarborCheck

#print axioms HarborCheck.check
