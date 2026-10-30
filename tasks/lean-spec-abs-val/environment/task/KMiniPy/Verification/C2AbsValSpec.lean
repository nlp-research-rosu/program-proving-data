import KMiniPy.Symbolic.B1AbsVal
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `abs_val` (C2AbsVal). `statement` is
what `C2AbsVal.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C2AbsValSpec

open B1AbsVal

/-- Precondition: at program start. The spec is total — no constraint. -/
def pre (x : Int) : Pat := pat (B1AbsVal.init x)

/-- Postcondition: terminated with an integer result `r` that is
non-negative and equals `x` or `-x` (the K `?`-variable, existential inside
the pattern). -/
def post (x : Int) : Pat := fun γ =>
  ∃ r : Int, γ = B1AbsVal.final (iV r) ∧ 0 ≤ r ∧ (r = x ∨ r = -x)

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (x : SortInt), RLOne (pre x) (post x)

end C2AbsValSpec
