import KMiniPy.Verification.C29KbSquaresCubic

open RLogic

namespace HarborCheck

def refPre (n : Int) : Pat := fun γ => γ = C29KbSquaresCubicLegs.init n ∧ 1 ≤ n

def refPost (n : Int) : Pat := pat (C29KbSquaresCubicLegs.final n ((n * (n + 1) * (2 * n + 1)) / 6) 0 0)

theorem check (n : SortInt) : RLOne (refPre n) (refPost n) :=
  C29KbSquaresCubic.spec n

end HarborCheck

#print axioms HarborCheck.check
