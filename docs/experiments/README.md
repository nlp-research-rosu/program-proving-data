# klean feasibility experiment (2026-07-14)

`smoke2-lean/` is the untouched output of `python -m pyk.klean` on the counter
semantics `smoke2.k` (two rules: bump/finish), PLUS one added file,
`Smoke2Lean/Theorems.lean`, which contains everything PLAN-LEAN.md builds on:

- Star / StepN / Diverges / Reaches definitions (the closure layer klean lacks)
- a concrete execution theorem: `Star Rewrites (run 8) (done 10)`
- a symbolic theorem: `forall i, i < 10 -> Rewrites (run i) (run (i+1))`

Reproduce: `cd smoke2-lean && lake build` (Lean toolchain pinned by lean-toolchain;
install via elan). Built green on Lean 4.30.0.
