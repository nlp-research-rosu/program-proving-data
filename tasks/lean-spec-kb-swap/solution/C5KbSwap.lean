import KMiniPy.Verification.C5KbSwapPaths
import KMiniPy.RL

/-! # C5KbSwap: reachability-logic derivation over `KMiniPy.Verification.C5KbSwapPaths`
(the proved path theorems; split out of the corpus file for this task). -/

open RLogic

namespace C5KbSwap

/-- C5KbSwap K-claim mirror (c5_kb_swap): a and b are swapped via temporary r: a ends as b0, b as a0, r as a0, for arbitrary int inputs.
A straight-line program: the reachability derivation is a single
machine-checked `Rewrites` leg entering as an Axiom over `SRew`. -/
theorem spec (a b : SortInt) :
    RLOne (pat (init a b)) (pat (final a b)) :=
  RL.rw_leg (path_main a b)

end C5KbSwap
