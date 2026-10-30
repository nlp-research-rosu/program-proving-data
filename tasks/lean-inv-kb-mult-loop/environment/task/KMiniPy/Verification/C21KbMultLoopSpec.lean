import KMiniPy.Verification.C21KbMultLoopLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_mult_loop` (C21KbMultLoop). `statement` is
what `C21KbMultLoop.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C21KbMultLoopSpec

open C21KbMultLoopLegs

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (n a : Int) : Pat := pat (init n a)

/-- Postcondition: terminated with `n ↦ min n 0`, `a` unchanged, and
`res ↦ a * max n 0` — the piecewise closed form of the counting loop. -/
def post (n a : Int) : Pat := pat (final (min n 0) a (a * max n 0))

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (n a : SortInt), RLOne (pre n a) (post n a)

end C21KbMultLoopSpec
