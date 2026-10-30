import KMiniPy.Verification.C25KbLoopMaxLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_loop_max` (C25KbLoopMax). `statement` is
what `C25KbLoopMax.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C25KbLoopMaxSpec

open C25KbLoopMaxLegs

/-- Precondition: at program start, with `1 ≤ n` as a logical constraint. -/
def pre (a n : Int) : Pat := fun γ => γ = init a n ∧ 1 ≤ n

/-- Postcondition: terminated with `m ↦ max a (n - 1)` and `i ↦ n`. -/
def post (a n : Int) : Pat := pat (final a n (max a (n - 1)) n)

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a n : SortInt), RLOne (pre a n) (post a n)

end C25KbLoopMaxSpec
