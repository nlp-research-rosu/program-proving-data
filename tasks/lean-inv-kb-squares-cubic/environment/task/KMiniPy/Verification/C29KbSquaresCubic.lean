import KMiniPy.Verification.C29KbSquaresCubicSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C29KbSquaresCubic: `kb_squares_cubic` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C29KbSquaresCubicLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C29KbSquaresCubicSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C29KbSquaresCubic

open C29KbSquaresCubicLegs
open C29KbSquaresCubicSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) := by
  sorry

end C29KbSquaresCubic
