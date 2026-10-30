import KMiniPy.Verification.C20KbSumdiffSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C20KbSumdiff: `kb_sumdiff` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C20KbSumdiffLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C20KbSumdiffSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C20KbSumdiff

open C20KbSumdiffLegs
open C20KbSumdiffSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) := by
  sorry

end C20KbSumdiff
