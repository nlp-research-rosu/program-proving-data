import KMiniPy.Verification.C23KbSumUpSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C23KbSumUp: `kb_sum_up` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C23KbSumUpLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C23KbSumUpSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C23KbSumUp

open C23KbSumUpLegs
open C23KbSumUpSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) := by
  sorry

end C23KbSumUp
