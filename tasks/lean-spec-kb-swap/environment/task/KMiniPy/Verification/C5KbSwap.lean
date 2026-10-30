import KMiniPy.Verification.C5KbSwapSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C5KbSwap: `kb_swap` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C5KbSwapPaths`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C5KbSwapSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C5KbSwap

open C5KbSwapSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) :
    RLOne (pat (init a b)) (pat (final a b)) := by
  sorry

end C5KbSwap
