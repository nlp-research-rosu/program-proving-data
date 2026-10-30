import KMiniPy.Verification.C6KbChain

open RLogic

namespace HarborCheck

theorem check (a : SortInt) :
    RLOne (pat (C6KbChain.init a)) (pat (C6KbChain.final a)) :=
  C6KbChain.spec a

end HarborCheck

#print axioms HarborCheck.check
