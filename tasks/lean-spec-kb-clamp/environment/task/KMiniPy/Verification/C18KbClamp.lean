import KMiniPy.Verification.C18KbClampSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C18KbClamp: `kb_clamp` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C18KbClampPaths`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C18KbClampSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C18KbClamp

open C18KbClampSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a : SortInt) :
    RLOne (pat (init a)) (post a) := by
  sorry

end C18KbClamp
