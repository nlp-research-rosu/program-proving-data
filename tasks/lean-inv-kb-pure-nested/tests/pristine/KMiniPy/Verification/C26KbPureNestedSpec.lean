import KMiniPy.Verification.C26KbPureNestedLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_pure_nested` (C26KbPureNested). `statement` is
what `C26KbPureNested.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C26KbPureNestedSpec

open C26KbPureNestedLegs

/-- Precondition: at program start, with the K claim's `A >=Int 1`. -/
def pre (a b : Int) : Pat := fun γ => γ = init a b ∧ 1 ≤ a

/-- Postcondition: terminated with `i ↦ 0`, `j ↦ min b 0` (the K claim's
`?I2 = 0 ∧ ?J2 = minInt(B, 0)`), `a` and `b` unchanged. -/
def post (a b : Int) : Pat := pat (final a b 0 (min b 0))

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a b : SortInt), RLOne (pre a b) (post a b)

end C26KbPureNestedSpec
