import KMiniPy.Verification.C8KbArithMixPaths
import KMiniPy.RL

/-! # C8KbArithMix: `kb_arith_mix` — the functional spec, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C8KbArithMixPaths`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement (and
`post`) are frozen. -/

open RLogic

namespace C8KbArithMix

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) :
    RLOne (pat (init a b)) (pat (final a b)) := by
  sorry

end C8KbArithMix
