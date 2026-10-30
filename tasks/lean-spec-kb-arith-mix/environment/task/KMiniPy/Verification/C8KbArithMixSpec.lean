import KMiniPy.Verification.C8KbArithMixPaths
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_arith_mix` (C8KbArithMix). `statement` is
what `C8KbArithMix.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C8KbArithMixSpec

open C8KbArithMix

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a b : SortInt), RLOne (pat (init a b)) (pat (final a b))

end C8KbArithMixSpec
