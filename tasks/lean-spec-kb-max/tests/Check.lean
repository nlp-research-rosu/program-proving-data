import KMiniPy.Verification.C10KbMax

open RLogic

namespace HarborCheck

def refPost (a b : Int) : Pat := fun γ =>
  ∃ m : Int, γ = C10KbMax.final a b (iV m) ∧ a ≤ m ∧ b ≤ m ∧ (m = a ∨ m = b)

theorem check (a b : SortInt) :
    RLOne (pat (C10KbMax.init a b)) (refPost a b) :=
  C10KbMax.spec a b

end HarborCheck

#print axioms HarborCheck.check
