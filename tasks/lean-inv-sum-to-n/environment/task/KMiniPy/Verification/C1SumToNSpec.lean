import KMiniPy.Verification.C1Legs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `sum_to_n` (C1SumToN). `statement` is
what `C1SumToN.gauss` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C1SumToNSpec

open C1SumToN

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 0 ≤ n

/-- Postcondition: terminated, with `result ↦ n·(n+1)/2`. -/
def post (n : Int) : Pat := pat (final (iV (n * (n + 1) / 2)))

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (n : SortInt), RLOne (pre n) (post n)

end C1SumToNSpec
