import KMiniPy.Verification.C30KbRowsSumNestedLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_rows_sum_nested` (C30KbRowsSumNested). `statement` is
what `C30KbRowsSumNested.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C30KbRowsSumNestedSpec

open C30KbRowsSumNestedLegs

/-- Precondition: at program start, with the K claim's `A >=Int 1`. -/
def pre (a b : Int) : Pat := fun γ => γ = init a b ∧ 1 ≤ a

/-- Postcondition: terminated with `sum ↦ (max b 0 * (max b 0 + 1)) / 2 * a`
(each of the `a` rows contributes the Gauss row sum; equivalent to the K
claim's `2*sum = a * maxInt(b,0) * (maxInt(b,0)+1)` by evenness of the
consecutive product), `i ↦ 0`, `j ↦ min b 0`, `a` and `b` unchanged. -/
def post (a b : Int) : Pat :=
  pat (final a b ((max b 0 * (max b 0 + 1)) / 2 * a) 0 (min b 0))

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a b : SortInt), RLOne (pre a b) (post a b)

end C30KbRowsSumNestedSpec
