import KMiniPy.Verification.C2AbsVal

open RLogic

namespace HarborCheck

def refPre (x : Int) : Pat := pat (B1AbsVal.init x)

def refPost (x : Int) : Pat := fun γ =>
  ∃ r : Int, γ = B1AbsVal.final (iV r) ∧ 0 ≤ r ∧ (r = x ∨ r = -x)

theorem check (x : SortInt) : RLOne (refPre x) (refPost x) :=
  C2AbsVal.spec x

end HarborCheck

#print axioms HarborCheck.check
