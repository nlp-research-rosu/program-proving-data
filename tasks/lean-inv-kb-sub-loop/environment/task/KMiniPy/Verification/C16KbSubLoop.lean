import KMiniPy.Verification.C16KbSubLoopSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C16KbSubLoop: `kb_sub_loop` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C16KbSubLoopLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C16KbSubLoopSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C16KbSubLoop

open C16KbSubLoopLegs
open C16KbSubLoopSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) := by
  sorry

end C16KbSubLoop
