import KMiniPy.Verification.C2AbsValSpec
import KMiniPy.RL

set_option linter.unusedVariables false

/-! # C2AbsVal: `abs_val` — the claim, to be derived

`spec` states the one-path reachability claim of this program over
the proved path theorems of `KMiniPy.Symbolic.B1AbsVal`. `pre`/`post` and the frozen statement live in the
verifier-owned module `C2AbsValSpec`. Replace the `sorry` with a derivation in
the `RL` calculus (see instruction.md); the statement must stay as given. -/

open RLogic

namespace C2AbsVal

open B1AbsVal
open C2AbsValSpec

/-- The claim. Replace `sorry` with a complete derivation. -/
theorem spec (x : SortInt) : RLOne (pre x) (post x) := by
  sorry

end C2AbsVal
