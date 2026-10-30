import KMiniPy.Verification.C7KbDoubleHalfPaths
import KMiniPy.RL

/-! # C7KbDoubleHalf: `kb_double_half` — the functional spec, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C7KbDoubleHalfPaths`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement (and
`post`) are frozen. -/

open RLogic

namespace C7KbDoubleHalf

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a : SortInt) :
    RLOne (pat (init a)) (pat (final a)) := by
  sorry

end C7KbDoubleHalf
