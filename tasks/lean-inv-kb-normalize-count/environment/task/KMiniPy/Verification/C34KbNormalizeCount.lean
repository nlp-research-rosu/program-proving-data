import KMiniPy.Verification.C34KbNormalizeCountSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C34KbNormalizeCount: `kb_normalize_count` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C34KbNormalizeCountLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C34KbNormalizeCountSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C34KbNormalizeCount

open C34KbNormalizeCountLegs
open C34KbNormalizeCountSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b n : SortInt) : RLOne (pre a b n) (post a b n) := by
  sorry

end C34KbNormalizeCount
