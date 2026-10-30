import KMiniPy.Verification.C30KbRowsSumNestedSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C30KbRowsSumNested: `kb_rows_sum_nested` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C30KbRowsSumNestedLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C30KbRowsSumNestedSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C30KbRowsSumNested

open C30KbRowsSumNestedLegs
open C30KbRowsSumNestedSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) := by
  sorry

end C30KbRowsSumNested
