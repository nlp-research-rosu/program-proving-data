import KMiniPy.Verification.C7KbDoubleHalfPaths
import KMiniPy.RL

/-! # C7KbDoubleHalf: reachability-logic derivation over `KMiniPy.Verification.C7KbDoubleHalfPaths`
(the proved path theorems; split out of the corpus file for this task). -/

open RLogic

namespace C7KbDoubleHalf

/-- C7KbDoubleHalf K-claim mirror (c7_kb_double_half): r ends as exactly a: doubling first makes the floor division exact.
A straight-line program: the reachability derivation is a single
machine-checked `Rewrites` leg entering as an Axiom over `SRew`. -/
theorem spec (a : SortInt) :
    RLOne (pat (init a)) (pat (final a)) :=
  RL.rw_leg (path_main a)

end C7KbDoubleHalf
