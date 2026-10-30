import KMiniPy.Verification.C7KbDoubleHalfPaths
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_double_half` (C7KbDoubleHalf). `statement` is
what `C7KbDoubleHalf.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C7KbDoubleHalfSpec

open C7KbDoubleHalf

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a : SortInt), RLOne (pat (init a)) (pat (final a))

end C7KbDoubleHalfSpec
