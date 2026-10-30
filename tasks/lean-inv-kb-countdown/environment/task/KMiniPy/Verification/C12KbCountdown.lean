import KMiniPy.Verification.C12KbCountdownSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C12KbCountdown: `kb_countdown` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C12KbCountdownLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C12KbCountdownSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C12KbCountdown

open C12KbCountdownLegs
open C12KbCountdownSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) := by
  sorry

end C12KbCountdown
