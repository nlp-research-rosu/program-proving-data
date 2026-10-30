import KMiniPy.Verification.C6KbChainPaths
import KMiniPy.RL

/-! # C6KbChain: reachability-logic derivation over `KMiniPy.Verification.C6KbChainPaths`
(the proved path theorems; split out of the corpus file for this task). -/

open RLogic

namespace C6KbChain

/-- C6KbChain K-claim mirror (c6_kb_chain): x ends as a+1, y as (a+1)*2, z as (a+1)*2 - a; a unchanged.
A straight-line program: the reachability derivation is a single
machine-checked `Rewrites` leg entering as an Axiom over `SRew`. -/
theorem spec (a : SortInt) :
    RLOne (pat (init a)) (pat (final a)) :=
  RL.rw_leg (path_main a)

end C6KbChain
