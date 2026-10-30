import KMiniPy.Verification.C4KbAssign

open RLogic

namespace HarborCheck

theorem check (a : SortInt) :
    RLOne (pat (C4KbAssign.init a)) (pat (C4KbAssign.final a)) :=
  C4KbAssign.spec a

end HarborCheck

#print axioms HarborCheck.check
