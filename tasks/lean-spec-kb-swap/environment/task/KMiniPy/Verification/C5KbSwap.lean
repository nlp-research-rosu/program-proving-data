import KMiniPy.Verification.C5KbSwapPaths
import KMiniPy.RL

/-! # C5KbSwap: `kb_swap` — the functional spec, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C5KbSwapPaths`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement (and
`post`) are frozen. -/

open RLogic

namespace C5KbSwap

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) :
    RLOne (pat (init a b)) (pat (final a b)) := by
  sorry

end C5KbSwap
