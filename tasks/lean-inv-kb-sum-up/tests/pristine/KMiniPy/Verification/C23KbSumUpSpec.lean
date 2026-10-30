import KMiniPy.Verification.C23KbSumUpLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_sum_up` (C23KbSumUp). `statement` is
what `C23KbSumUp.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C23KbSumUpSpec

open C23KbSumUpLegs

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 0 ≤ n

/-- Postcondition: terminated, with `sum ↦ n*(n+1)/2` (the K claim's Gauss
closed form) and `i ↦ n + 1`. -/
def post (n : Int) : Pat := pat (final n ((n * (n + 1)) / 2) (n + 1))

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (n : SortInt), RLOne (pre n) (post n)

end C23KbSumUpSpec
