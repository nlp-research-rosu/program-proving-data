import KMiniPy.Verification.C14KbSumSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C14KbSum: `kb_sum` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C14KbSumLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C14KbSumSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C14KbSum

open C14KbSumLegs
open C14KbSumSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n sum : SortInt) : RLOne (pre n sum) (post n sum) := by
  sorry

end C14KbSum
