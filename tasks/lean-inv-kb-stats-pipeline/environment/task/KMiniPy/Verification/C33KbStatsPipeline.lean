import KMiniPy.Verification.C33KbStatsPipelineLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C33KbStatsPipeline: `kb_stats_pipeline` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C33KbStatsPipelineLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C33KbStatsPipeline

open C33KbStatsPipelineLegs

/-- Precondition: at program start, with `0 ≤ n`. -/
def pre (a b n : Int) : Pat := fun γ => γ = init a b n ∧ 0 ≤ n

/-- Postcondition: terminated with `a`, `b`, `n` unchanged, `m ↦ min a b`,
`x ↦ max a b`, `t ↦ max a b - min a b`,
`res ↦ (max a b - min a b) * n + min a b` and `i ↦ n`. -/
def post (a b n : Int) : Pat :=
  pat (final a b n (min a b) (max a b) (max a b - min a b)
    ((max a b - min a b) * n + min a b) n)

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b n : SortInt) : RLOne (pre a b n) (post a b n) := by
  sorry

end C33KbStatsPipeline
