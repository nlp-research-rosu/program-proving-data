import KMiniPy.Verification.C15KbAddLoopSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C15KbAddLoop: `kb_add_loop` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C15KbAddLoopLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C15KbAddLoopSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C15KbAddLoop

open C15KbAddLoopLegs
open C15KbAddLoopSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n res a : SortInt) : RLOne (pre n res a) (post n res a) := by
  sorry

end C15KbAddLoop
