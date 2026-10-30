import KMiniPy.Verification.C32KbPipelineLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_pipeline` (C32KbPipeline). `statement` is
what `C32KbPipeline.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C32KbPipelineSpec

open C32KbPipelineLegs

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (a b n : Int) : Pat := fun γ => γ = init a b n ∧ 0 ≤ n

/-- Postcondition: terminated with `a`, `b`, `n` unchanged,
`t ↦ max (a*b) (0 - a*b)` (= `|a*b|`), `i ↦ n` and
`res ↦ max (a*b) (0 - a*b) * n + a`. -/
def post (a b n : Int) : Pat :=
  pat (final a b n (max (a * b) (0 - a * b))
    ((max (a * b) (0 - a * b)) * n + a) n)

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a b n : SortInt), RLOne (pre a b n) (post a b n)

end C32KbPipelineSpec
