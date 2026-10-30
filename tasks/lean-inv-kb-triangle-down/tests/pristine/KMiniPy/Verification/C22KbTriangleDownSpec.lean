import KMiniPy.Verification.C22KbTriangleDownLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_triangle_down` (C22KbTriangleDown). `statement` is
what `C22KbTriangleDown.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C22KbTriangleDownSpec

open C22KbTriangleDownLegs

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (n : Int) : Pat := pat (init n)

/-- Postcondition: terminated with `n ↦ min n 0` and the descending
triangle sum `sum ↦ (max n 0 * (max n 0 + 1)) / 2`. -/
def post (n : Int) : Pat := pat (final (min n 0) ((max n 0 * (max n 0 + 1)) / 2))

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (n : SortInt), RLOne (pre n) (post n)

end C22KbTriangleDownSpec
