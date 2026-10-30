import KMiniPy.Verification.C14KbSumLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_sum` (C14KbSum). `statement` is
what `C14KbSum.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C14KbSumSpec

open C14KbSumLegs

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (n sum : Int) : Pat := fun γ => γ = init n sum ∧ 0 ≤ n

/-- Postcondition: terminated with `n ↦ 0` and the Gauss closed form
`sum ↦ sum + n*(n+1)/2` (the K claim's ensures; `/` is Int ediv, exact here
because `n*(n+1)` is even). -/
def post (n sum : Int) : Pat := pat (final 0 (sum + (n * (n + 1)) / 2))

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (n sum : SortInt), RLOne (pre n sum) (post n sum)

end C14KbSumSpec
