import KMiniPy.Verification.C25KbLoopMax

open RLogic

namespace HarborCheck

def refPre (a n : Int) : Pat := fun γ => γ = C25KbLoopMaxLegs.init a n ∧ 1 ≤ n

def refPost (a n : Int) : Pat := pat (C25KbLoopMaxLegs.final a n (max a (n - 1)) n)

theorem check (a n : SortInt) : RLOne (refPre a n) (refPost a n) :=
  C25KbLoopMax.spec a n

end HarborCheck

#print axioms HarborCheck.check
