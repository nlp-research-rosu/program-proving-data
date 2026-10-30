import KMiniPy.Verification.C18KbClamp

open RLogic

namespace HarborCheck

def refPost (a : Int) : Pat := fun γ =>
  ∃ r : Int, γ = C18KbClamp.final a (iV r) ∧ r = min (max a 0) 10

theorem check (a : SortInt) :
    RLOne (pat (C18KbClamp.init a)) (refPost a) :=
  C18KbClamp.spec a

end HarborCheck

#print axioms HarborCheck.check
