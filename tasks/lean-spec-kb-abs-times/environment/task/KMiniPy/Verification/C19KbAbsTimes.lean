import KMiniPy.Verification.C19KbAbsTimesSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C19KbAbsTimes: `kb_abs_times` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C19KbAbsTimesPaths`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C19KbAbsTimesSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C19KbAbsTimes

open C19KbAbsTimesSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) :
    RLOne (pat (init a b)) (post a b) := by
  sorry

end C19KbAbsTimes
