import KMiniPy.Verification.C11KbMinSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C11KbMin: `kb_min` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C11KbMinPaths`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C11KbMinSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C11KbMin

open C11KbMinSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) :
    RLOne (pat (init a b)) (post a b) := by
  sorry

end C11KbMin
