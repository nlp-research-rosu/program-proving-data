import KMiniPy.Verification.C33KbStatsPipelineSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C33KbStatsPipeline: `kb_stats_pipeline` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C33KbStatsPipelineLegs`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C33KbStatsPipelineSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C33KbStatsPipeline

open C33KbStatsPipelineLegs
open C33KbStatsPipelineSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b n : SortInt) : RLOne (pre a b n) (post a b n) := by
  sorry

end C33KbStatsPipeline
