import KMiniPy.Verification.C7KbDoubleHalfSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C7KbDoubleHalf: `kb_double_half` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C7KbDoubleHalfPaths`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C7KbDoubleHalfSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C7KbDoubleHalf

open C7KbDoubleHalfSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a : SortInt) :
    RLOne (pat (init a)) (pat (final a)) := by
  sorry

end C7KbDoubleHalf
