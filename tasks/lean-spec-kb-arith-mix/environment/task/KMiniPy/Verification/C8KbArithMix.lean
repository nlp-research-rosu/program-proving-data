import KMiniPy.Verification.C8KbArithMixSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C8KbArithMix: `kb_arith_mix` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Verification.C8KbArithMixPaths`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C8KbArithMixSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C8KbArithMix

open C8KbArithMixSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) :
    RLOne (pat (init a b)) (pat (final a b)) := by
  sorry

end C8KbArithMix
