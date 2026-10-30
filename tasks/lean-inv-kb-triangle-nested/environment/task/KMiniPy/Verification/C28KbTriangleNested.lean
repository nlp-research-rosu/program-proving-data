import KMiniPy.Verification.C28KbTriangleNestedSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C28KbTriangleNested: `kb_triangle_nested` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C28KbTriangleNestedLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C28KbTriangleNestedSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C28KbTriangleNested

open C28KbTriangleNestedLegs
open C28KbTriangleNestedSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) := by
  sorry

end C28KbTriangleNested
