import KMiniPy.Verification.C16KbSubLoopLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_sub_loop` (C16KbSubLoop). `statement` is
what `C16KbSubLoop.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C16KbSubLoopSpec

open C16KbSubLoopLegs

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (a b : Int) : Pat := pat (init a b)

/-- Postcondition: terminated with `a ↦ a - max b 0` and `b ↦ min b 0`. -/
def post (a b : Int) : Pat := pat (final (a - max b 0) (min b 0))

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a b : SortInt), RLOne (pre a b) (post a b)

end C16KbSubLoopSpec
