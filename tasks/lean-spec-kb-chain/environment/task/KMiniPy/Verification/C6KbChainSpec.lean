import KMiniPy.Verification.C6KbChainPaths
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_chain` (C6KbChain). `statement` is
what `C6KbChain.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C6KbChainSpec

open C6KbChain

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (a : SortInt), RLOne (pat (init a)) (pat (final a))

end C6KbChainSpec
