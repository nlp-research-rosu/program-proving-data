import KMiniPy.Verification.C24KbCountEven

open RLogic

namespace HarborCheck

def refPre (n : Int) : Pat := fun γ => γ = C24KbCountEvenLegs.init n ∧ 0 ≤ n

def refPost (n : Int) : Pat := pat (C24KbCountEvenLegs.final n ((n + 1) / 2) n)

theorem check (n : SortInt) : RLOne (refPre n) (refPost n) :=
  C24KbCountEven.spec n

end HarborCheck

#print axioms HarborCheck.check
