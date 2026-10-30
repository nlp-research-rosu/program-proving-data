import KMiniPy.Verification.C17KbMax3Spec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C17KbMax3: `kb_max3` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C17KbMax3Paths`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C17KbMax3Spec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C17KbMax3

open C17KbMax3Spec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b n : SortInt) :
    RLOne (pat (init a b n)) (post a b n) := by
  sorry

end C17KbMax3
