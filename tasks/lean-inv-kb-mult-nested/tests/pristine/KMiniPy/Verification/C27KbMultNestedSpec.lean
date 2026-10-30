import KMiniPy.Verification.C27KbMultNestedLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_mult_nested` (C27KbMultNested). `statement` is
what `C27KbMultNested.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C27KbMultNestedSpec

open C27KbMultNestedLegs

/-- Precondition: at program start, with the K claim's `A >=Int 1`. -/
def pre (a b : Int) : Pat := fun γ => γ = init a b ∧ 1 ≤ a

/-- Postcondition: terminated with `res ↦ max b 0 * a` (the K claim's
`?RES = A *Int maxInt(B, 0)`, omega-equal orientation), `i ↦ 0`,
`j ↦ min b 0`, `a` and `b` unchanged. -/
def post (a b : Int) : Pat := pat (final a b (max b 0 * a) 0 (min b 0))

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a b : SortInt), RLOne (pre a b) (post a b)

end C27KbMultNestedSpec
