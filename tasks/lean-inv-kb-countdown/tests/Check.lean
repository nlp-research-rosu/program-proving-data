import KMiniPy.Verification.C12KbCountdown

open RLogic

namespace HarborCheck

def refPre (n : Int) : Pat := fun γ => γ = C12KbCountdownLegs.init n ∧ 0 ≤ n

def refPost (n : Int) : Pat := pat (C12KbCountdownLegs.final 0)

theorem check (n : SortInt) : RLOne (refPre n) (refPost n) :=
  C12KbCountdown.spec n

end HarborCheck

#print axioms HarborCheck.check
