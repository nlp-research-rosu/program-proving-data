import KMiniPy.Verification.C12KbCountdownLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_countdown` (C12KbCountdown). `statement` is
what `C12KbCountdown.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C12KbCountdownSpec

open C12KbCountdownLegs

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 0 ≤ n

/-- Postcondition: terminated, with `n ↦ 0` (the K claim's `?F ==Int 0`). -/
def post (n : Int) : Pat := pat (final 0)

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (n : SortInt), RLOne (pre n) (post n)

end C12KbCountdownSpec
