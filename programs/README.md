# The subject programs

Self-contained Python files: function definitions plus one entry call assigning `result`.
Where each appears:

| program | K samples | Lean theorems |
|---|---|---|
| sum_to_n.py | a1 concrete | A1 trace (proved) · C1 Gauss form (RL derivation, proved) |
| gcd.py | a2 concrete | A2 trace (proved) |
| collatz_steps.py | a3 concrete | A3 trace (proved) |
| half_of_even.py | a4 concrete, assert-fail | A4 trace to assert-failure (proved) |
| abs_val.py | b1 symbolic · c2 verification | B1 path theorems (proved) · C2 spec (RL derivation, proved) |
| classify_triangle.py | b2 symbolic | B2 path theorems (proved) |
| buggy_abs.py | c3 refutation + counterexample | C3BuggyAbsAt0 trace + C3Refutation (proved) |

Sample c1 (range-loop invariant) uses the program and spec from the vendored klever
verification suite, not a file here.

## Ported KleverBench problems (kb_*)

The 31 `kb_` programs are module-level ports of the complete
[KleverBench](https://github.com/nlp-research-rosu/KleverBench) IMP problem set
(upstream pin and translation rules in [PROVENANCE.md](PROVENANCE.md)): inputs are
bound to magic literals first, then the IMP statements follow in idiomatic MiniPy.
Each has a proved verification record `data/k/verification/c<n>_kb_<stem>` (n = 4–34,
covering all five structural tiers: straight-line, single loop/branch, mixed,
nested loops, multi-stage pipelines) AND a proved Lean counterpart
`data/lean/KMiniPy/Verification/C<n>Kb*.lean` mirroring the K claim in reachability
logic — path theorems for the loop-free tier, Circularity derivations over generated
execution legs for every loop program.
