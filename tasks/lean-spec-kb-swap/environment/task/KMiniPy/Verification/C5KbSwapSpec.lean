import KMiniPy.Verification.C5KbSwapPaths
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_swap` (C5KbSwap). `statement` is
what `C5KbSwap.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C5KbSwapSpec

open C5KbSwap

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a b : SortInt), RLOne (pat (init a b)) (pat (final a b))

end C5KbSwapSpec
