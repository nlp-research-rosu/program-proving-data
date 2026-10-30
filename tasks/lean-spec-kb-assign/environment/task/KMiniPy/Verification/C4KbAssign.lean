import KMiniPy.Verification.C4KbAssignSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C4KbAssign: `kb_assign` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C4KbAssignPaths`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C4KbAssignSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C4KbAssign

open C4KbAssignSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a : SortInt) :
    RLOne (pat (init a)) (pat (final a)) := by
  sorry

end C4KbAssign
