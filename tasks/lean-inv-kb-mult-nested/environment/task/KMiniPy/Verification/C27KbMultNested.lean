import KMiniPy.Verification.C27KbMultNestedSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C27KbMultNested: `kb_mult_nested` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C27KbMultNestedLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C27KbMultNestedSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C27KbMultNested

open C27KbMultNestedLegs
open C27KbMultNestedSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) := by
  sorry

end C27KbMultNested
