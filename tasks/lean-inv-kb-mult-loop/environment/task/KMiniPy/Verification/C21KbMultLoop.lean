import KMiniPy.Verification.C21KbMultLoopSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C21KbMultLoop: `kb_mult_loop` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C21KbMultLoopLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C21KbMultLoopSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C21KbMultLoop

open C21KbMultLoopLegs
open C21KbMultLoopSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n a : SortInt) : RLOne (pre n a) (post n a) := by
  sorry

end C21KbMultLoop
