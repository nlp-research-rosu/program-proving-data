import KMiniPy.Verification.C13KbCountupSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C13KbCountup: `kb_countup` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C13KbCountupLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C13KbCountupSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C13KbCountup

open C13KbCountupLegs
open C13KbCountupSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n r : SortInt) : RLOne (pre n r) (post n r) := by
  sorry

end C13KbCountup
