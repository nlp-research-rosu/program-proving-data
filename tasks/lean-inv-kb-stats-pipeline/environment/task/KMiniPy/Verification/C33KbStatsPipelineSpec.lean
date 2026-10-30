import KMiniPy.Verification.C33KbStatsPipelineLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_stats_pipeline` (C33KbStatsPipeline). `statement` is
what `C33KbStatsPipeline.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C33KbStatsPipelineSpec

open C33KbStatsPipelineLegs

/-- Precondition: at program start, with `0 ≤ n`. -/
def pre (a b n : Int) : Pat := fun γ => γ = init a b n ∧ 0 ≤ n

/-- Postcondition: terminated with `a`, `b`, `n` unchanged, `m ↦ min a b`,
`x ↦ max a b`, `t ↦ max a b - min a b`,
`res ↦ (max a b - min a b) * n + min a b` and `i ↦ n`. -/
def post (a b n : Int) : Pat :=
  pat (final a b n (min a b) (max a b) (max a b - min a b)
    ((max a b - min a b) * n + min a b) n)

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a b n : SortInt), RLOne (pre a b n) (post a b n)

end C33KbStatsPipelineSpec
