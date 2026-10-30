import KMiniPy.Verification.C17KbMax3

open RLogic

namespace HarborCheck

def refPost (a b n : Int) : Pat := fun γ =>
  ∃ m : Int, γ = C17KbMax3.final a b n (iV m) ∧ a ≤ m ∧ b ≤ m ∧ n ≤ m ∧ (m = a ∨ m = b ∨ m = n)

theorem check (a b n : SortInt) :
    RLOne (pat (C17KbMax3.init a b n)) (refPost a b n) :=
  C17KbMax3.spec a b n

end HarborCheck

#print axioms HarborCheck.check
