import KMiniPy.Verification.C29KbSquaresCubicLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_squares_cubic` (C29KbSquaresCubic). `statement` is
what `C29KbSquaresCubic.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C29KbSquaresCubicSpec

open C29KbSquaresCubicLegs

/-- Precondition: at program start, with the K claim's `N >=Int 1`. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 1 ≤ n

/-- Postcondition: terminated with `res ↦ n*(n+1)*(2*n+1)/6` (the K claim's
square-pyramidal ensures), both counters at `0`, `n` unchanged. -/
def post (n : Int) : Pat := pat (final n ((n * (n + 1) * (2 * n + 1)) / 6) 0 0)

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (n : SortInt), RLOne (pre n) (post n)

end C29KbSquaresCubicSpec
