import KMiniPy.Verification.C32KbPipelineLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C32KbPipeline: `kb_pipeline` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C32KbPipelineLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C32KbPipeline

open C32KbPipelineLegs

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (a b n : Int) : Pat := fun γ => γ = init a b n ∧ 0 ≤ n

/-- Postcondition: terminated with `a`, `b`, `n` unchanged,
`t ↦ max (a*b) (0 - a*b)` (= `|a*b|`), `i ↦ n` and
`res ↦ max (a*b) (0 - a*b) * n + a`. -/
def post (a b n : Int) : Pat :=
  pat (final a b n (max (a * b) (0 - a * b))
    ((max (a * b) (0 - a * b)) * n + a) n)

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b n : SortInt) : RLOne (pre a b n) (post a b n) := by
  sorry

end C32KbPipeline
