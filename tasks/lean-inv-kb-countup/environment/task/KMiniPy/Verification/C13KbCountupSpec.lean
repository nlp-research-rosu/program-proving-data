import KMiniPy.Verification.C13KbCountupLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_countup` (C13KbCountup). `statement` is
what `C13KbCountup.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C13KbCountupSpec

open C13KbCountupLegs

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (n r : Int) : Pat := pat (init n r)

/-- Postcondition: terminated with `n` unchanged and `r ↦ max n r`. -/
def post (n r : Int) : Pat := pat (final n (max n r))

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (n r : SortInt), RLOne (pre n r) (post n r)

end C13KbCountupSpec
