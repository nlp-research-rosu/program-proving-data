import KMiniPy.Verification.C25KbLoopMaxSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C25KbLoopMax: `kb_loop_max` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C25KbLoopMaxLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C25KbLoopMaxSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C25KbLoopMax

open C25KbLoopMaxLegs
open C25KbLoopMaxSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a n : SortInt) : RLOne (pre a n) (post a n) := by
  sorry

end C25KbLoopMax
