import KMiniPy.Verification.C16KbSubLoopLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C16KbSubLoop: `kb_sub_loop` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C16KbSubLoopLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C16KbSubLoop

open C16KbSubLoopLegs

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (a b : Int) : Pat := pat (init a b)

/-- Postcondition: terminated with `a ↦ a - max b 0` and `b ↦ min b 0`. -/
def post (a b : Int) : Pat := pat (final (a - max b 0) (min b 0))

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (a b : SortInt) : RLOne (pre a b) (post a b) := by
  sorry

end C16KbSubLoop
