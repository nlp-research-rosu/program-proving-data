import KMiniPy.Verification.C13KbCountupLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C13KbCountup: `kb_countup` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C13KbCountupLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C13KbCountup

open C13KbCountupLegs

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (n r : Int) : Pat := pat (init n r)

/-- Postcondition: terminated with `n` unchanged and `r ↦ max n r`. -/
def post (n r : Int) : Pat := pat (final n (max n r))

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n r : SortInt) : RLOne (pre n r) (post n r) := by
  sorry

end C13KbCountup
