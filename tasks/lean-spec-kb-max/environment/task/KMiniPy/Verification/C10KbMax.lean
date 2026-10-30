import KMiniPy.Verification.C10KbMaxSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C10KbMax: `kb_max` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C10KbMaxPaths`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C10KbMaxSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C10KbMax

open C10KbMaxSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) :
    RLOne (pat (init a b)) (post a b) := by
  sorry

end C10KbMax
