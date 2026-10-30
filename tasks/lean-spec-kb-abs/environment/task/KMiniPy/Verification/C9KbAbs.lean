import KMiniPy.Verification.C9KbAbsSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C9KbAbs: `kb_abs` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C9KbAbsPaths`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C9KbAbsSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C9KbAbs

open C9KbAbsSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a : SortInt) :
    RLOne (pat (init a)) (post a) := by
  sorry

end C9KbAbs
