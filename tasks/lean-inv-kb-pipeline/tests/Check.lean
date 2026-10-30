import KMiniPy.Verification.C32KbPipeline

open RLogic

namespace HarborCheck

def refPre (a b n : Int) : Pat := fun γ => γ = C32KbPipelineLegs.init a b n ∧ 0 ≤ n

def refPost (a b n : Int) : Pat :=
  pat (C32KbPipelineLegs.final a b n (max (a * b) (0 - a * b))
    ((max (a * b) (0 - a * b)) * n + a) n)

theorem check (a b n : SortInt) : RLOne (refPre a b n) (refPost a b n) :=
  C32KbPipeline.spec a b n

end HarborCheck

#print axioms HarborCheck.check
