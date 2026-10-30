import KMiniPy.Verification.C28KbTriangleNestedLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_triangle_nested` (C28KbTriangleNested). `statement` is
what `C28KbTriangleNested.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C28KbTriangleNestedSpec

open C28KbTriangleNestedLegs

/-- Precondition: at program start, with the K claim's `N >=Int 1`. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 1 ≤ n

/-- Postcondition: terminated with the Gauss count `count ↦ (n*(n+1))/2`
and both loop counters drained (`i ↦ 0`, `j ↦ 0`), `n` unchanged. -/
def post (n : Int) : Pat := pat (final n ((n * (n + 1)) / 2) 0 0)

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (n : SortInt), RLOne (pre n) (post n)

end C28KbTriangleNestedSpec
