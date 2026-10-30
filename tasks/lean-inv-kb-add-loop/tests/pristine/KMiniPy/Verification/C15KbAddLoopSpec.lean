import KMiniPy.Verification.C15KbAddLoopLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_add_loop` (C15KbAddLoop). `statement` is
what `C15KbAddLoop.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C15KbAddLoopSpec

open C15KbAddLoopLegs

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (n res a : Int) : Pat := pat (init n res a)

/-- Postcondition: terminated with `n ↦ min n 0`, `res ↦ res + a * max n 0`
and `a` unchanged. -/
def post (n res a : Int) : Pat := pat (final (min n 0) (res + a * max n 0) a)

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (n res a : SortInt), RLOne (pre n res a) (post n res a)

end C15KbAddLoopSpec
