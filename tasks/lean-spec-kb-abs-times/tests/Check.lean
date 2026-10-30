import KMiniPy.Verification.C19KbAbsTimes

open RLogic

namespace HarborCheck

def refPost (a b : Int) : Pat := fun γ =>
  ∃ t r : Int, γ = C19KbAbsTimes.final a b (iV t) (iV r) ∧ 0 ≤ t ∧ (t = a ∨ t = 0 - a) ∧ r = t * b

theorem check (a b : SortInt) :
    RLOne (pat (C19KbAbsTimes.init a b)) (refPost a b) :=
  C19KbAbsTimes.spec a b

end HarborCheck

#print axioms HarborCheck.check
