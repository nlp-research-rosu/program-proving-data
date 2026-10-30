import KMiniPy.Verification.C9KbAbs

open RLogic

namespace HarborCheck

def refPost (a : Int) : Pat := fun γ =>
  ∃ r : Int, γ = C9KbAbs.final a (iV r) ∧ 0 ≤ r ∧ (r = a ∨ r = 0 - a)

theorem check (a : SortInt) :
    RLOne (pat (C9KbAbs.init a)) (refPost a) :=
  C9KbAbs.spec a

end HarborCheck

#print axioms HarborCheck.check
