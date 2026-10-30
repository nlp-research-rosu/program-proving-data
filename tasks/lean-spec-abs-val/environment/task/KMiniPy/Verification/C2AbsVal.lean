import KMiniPy.Symbolic.B1AbsVal
import KMiniPy.RL

/-! # C2AbsVal: `abs_val` — the functional spec, to be derived

`spec` states the one-path reachability claim of this program over
the proved symbolic paths of `B1AbsVal`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C2AbsVal

/-- Precondition: at program start. The spec is total — no constraint. -/
def pre (x : Int) : Pat := pat (B1AbsVal.init x)

/-- Postcondition: terminated with an integer result `r` that is
non-negative and equals `x` or `-x` (the K `?`-variable, existential inside
the pattern). -/
def post (x : Int) : Pat := fun γ =>
  ∃ r : Int, γ = B1AbsVal.final (iV r) ∧ 0 ≤ r ∧ (r = x ∨ r = -x)

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (x : SortInt) : RLOne (pre x) (post x) := by
  sorry

end C2AbsVal
