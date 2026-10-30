import KMiniPy.Verification.C4KbAssignPaths
import KMiniPy.RL

/-! # C4KbAssign: reachability-logic derivation over `KMiniPy.Verification.C4KbAssignPaths`
(the proved path theorems; split out of the corpus file for this task). -/

open RLogic

namespace C4KbAssign

/-- C4KbAssign K-claim mirror (c4_kb_assign): b ends as a + 4 and a is unchanged, for every int a.
A straight-line program: the reachability derivation is a single
machine-checked `Rewrites` leg entering as an Axiom over `SRew`. -/
theorem spec (a : SortInt) :
    RLOne (pat (init a)) (pat (final a)) :=
  RL.rw_leg (path_main a)

end C4KbAssign
