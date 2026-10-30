# corpus/k — the K dataset

Three families, mirroring the three kinds of reasoning; one record per sample, `.jsonl`
canonical (a single JSON object per file) with a readable `.md` rendering alongside:

- `concrete/` (a1–a4) — complete executions, every step annotated with the K semantic rule
  behind it (rule names resolve in `semantics/mpy-traced/rules.yaml`).
- `symbolic/` (b1–b2) — symbolic-execution trees: branch conditions, per-leaf path conditions
  with z3 witnesses (each replay-validated in CPython), z3 proofs for infeasible branches.
- `verification/` (c1–c34) — kprove records: the verbatim K claim modules, proved specs and
  one refutation with its counterexample run. c1–c3 are the original trio (c1 loop
  invariant, c2 functional spec, c3 refutation); c4–c34 port all 31
  [KleverBench](https://github.com/nlp-research-rosu/KleverBench) benchmark problems
  (straight-line dataflow through nested loops and multi-stage pipelines), each restated
  over the MPY semantics as a full-characterization claim — every binding the program
  creates is pinned to its exact final value — with loop invariants as circularity claims
  and `provenance.upstream` naming the source problem (see
  [programs/PROVENANCE.md](../../programs/PROVENANCE.md)).

Records are self-describing — every file carries `kind`, `id`, `source`, and `provenance` —
and the field-by-field schemas are in
[REPORT.md § Record schemas](../../REPORT.md#record-schemas-jsonl-one-record-per-file).
`make k-validate` at the repo root re-checks all of it against CPython and the expected
verdicts.
