import KMiniPy.Verification.C26KbPureNestedSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C26KbPureNested: `kb_pure_nested` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C26KbPureNestedLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C26KbPureNestedSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C26KbPureNested

open C26KbPureNestedLegs
open C26KbPureNestedSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) := by
  sorry

end C26KbPureNested
