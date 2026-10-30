import KMiniPy.Verification.C8KbArithMixPaths
import KMiniPy.RL

/-! # C8KbArithMix: reachability-logic derivation over `KMiniPy.Verification.C8KbArithMixPaths`
(the proved path theorems; split out of the corpus file for this task). -/

open RLogic

namespace C8KbArithMix

/-- C8KbArithMix K-claim mirror (c8_kb_arith_mix): res ends as a*b + a - b; a and b unchanged.
A straight-line program: the reachability derivation is a single
machine-checked `Rewrites` leg entering as an Axiom over `SRew`. -/
theorem spec (a b : SortInt) :
    RLOne (pat (init a b)) (pat (final a b)) :=
  RL.rw_leg (path_main a b)

end C8KbArithMix
