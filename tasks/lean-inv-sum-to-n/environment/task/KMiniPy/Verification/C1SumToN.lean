import KMiniPy.Verification.C1SumToNSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C1SumToN: `sum_to_n` — the claim, to be derived

`gauss` states the one-path reachability claim of this program over
the proved execution legs of `C1SumToN`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C1SumToNSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C1SumToN

open C1SumToNSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem gauss (n : SortInt) : RLOne (pre n) (post n) := by
  sorry

end C1SumToN
