import KMiniPy.Verification.C4KbAssignPaths
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_assign` (C4KbAssign). `statement` is
what `C4KbAssign.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C4KbAssignSpec

open C4KbAssign

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a : SortInt), RLOne (pat (init a)) (pat (final a))

end C4KbAssignSpec
