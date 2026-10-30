import KMiniPy.Verification.C15KbAddLoopLegs
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C15KbAddLoop: `kb_add_loop` — the loop claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved execution legs of `C15KbAddLoopLegs`. Replace the `sorry` with a
derivation in the `RL` calculus (see instruction.md). The statement, `pre`
and `post` are frozen. -/

open RLogic

namespace C15KbAddLoop

open C15KbAddLoopLegs

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (n res a : Int) : Pat := pat (init n res a)

/-- Postcondition: terminated with `n ↦ min n 0`, `res ↦ res + a * max n 0`
and `a` unchanged. -/
def post (n res a : Int) : Pat := pat (final (min n 0) (res + a * max n 0) a)

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (n res a : SortInt) : RLOne (pre n res a) (post n res a) := by
  sorry

end C15KbAddLoop
