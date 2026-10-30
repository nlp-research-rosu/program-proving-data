import KMiniPy.Verification.C33KbStatsPipeline

open RLogic

namespace HarborCheck

def refPre (a b n : Int) : Pat := fun γ => γ = C33KbStatsPipelineLegs.init a b n ∧ 0 ≤ n

def refPost (a b n : Int) : Pat :=
  pat (C33KbStatsPipelineLegs.final a b n (min a b) (max a b) (max a b - min a b)
    ((max a b - min a b) * n + min a b) n)

theorem check (a b n : SortInt) : RLOne (refPre a b n) (refPost a b n) :=
  C33KbStatsPipeline.spec a b n

end HarborCheck

#print axioms HarborCheck.check
