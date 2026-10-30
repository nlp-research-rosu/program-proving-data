import KMiniPy.Verification.C24KbCountEvenLegs
import KMiniPy.RL

/-! Verifier-owned: the frozen claim of `kb_count_even` (C24KbCountEven). `statement` is
what `C24KbCountEven.spec` must prove; the verifier closes it with that theorem. -/

open RLogic

namespace C24KbCountEvenSpec

open C24KbCountEvenLegs

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 0 ≤ n

/-- Postcondition: terminated with `count ↦ (n + 1) / 2` — the number of
even integers in `[0, n)` — and `i ↦ n`. -/
def post (n : Int) : Pat := pat (final n ((n + 1) / 2) n)

/-- The frozen claim. -/
abbrev statement : Prop := ∀ (n : SortInt), RLOne (pre n) (post n)

end C24KbCountEvenSpec
