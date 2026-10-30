import KMiniPy.Verification.C23KbSumUp

open RLogic

namespace HarborCheck

def refPre (n : Int) : Pat := fun γ => γ = C23KbSumUpLegs.init n ∧ 0 ≤ n

def refPost (n : Int) : Pat := pat (C23KbSumUpLegs.final n ((n * (n + 1)) / 2) (n + 1))

theorem check (n : SortInt) : RLOne (refPre n) (refPost n) :=
  C23KbSumUp.spec n

end HarborCheck

#print axioms HarborCheck.check
