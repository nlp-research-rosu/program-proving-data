import KMiniPy.Verification.C14KbSum

open RLogic

namespace HarborCheck

def refPre (n sum : Int) : Pat := fun γ => γ = C14KbSumLegs.init n sum ∧ 0 ≤ n

def refPost (n sum : Int) : Pat := pat (C14KbSumLegs.final 0 (sum + (n * (n + 1)) / 2))

theorem check (n sum : SortInt) : RLOne (refPre n sum) (refPost n sum) :=
  C14KbSum.spec n sum

end HarborCheck

#print axioms HarborCheck.check
