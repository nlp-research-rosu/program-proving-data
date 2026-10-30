import KMiniPy.Verification.C32KbPipelineSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C32KbPipeline: `kb_pipeline` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C32KbPipelineLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C32KbPipelineSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C32KbPipeline

open C32KbPipelineLegs
open C32KbPipelineSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b n : SortInt) : RLOne (pre a b n) (post a b n) := by
  sorry

end C32KbPipeline
