import KMiniPy.Verification.C11KbMin

open RLogic

namespace HarborCheck

def refPost (a b : Int) : Pat := fun γ =>
  ∃ m : Int, γ = C11KbMin.final a b (iV m) ∧ m ≤ a ∧ m ≤ b ∧ (m = a ∨ m = b)

theorem check (a b : SortInt) :
    RLOne (pat (C11KbMin.init a b)) (refPost a b) :=
  C11KbMin.spec a b

end HarborCheck

#print axioms HarborCheck.check
