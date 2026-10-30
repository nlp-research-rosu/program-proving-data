import KMiniPy.Verification.C23KbSumUpLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (n : Int) parameter on the claim family

/-! # C23: `kb_sum_up` — the counting-up loop reaches the Gauss closed form

`spec n : RLOne (pre n) (post n)` derives the one-path reachability claim
of C23: from `init n` with `0 ≤ n`, the program reaches the terminal state
with `sum ↦ n*(n+1)/2` and `i ↦ n + 1`. Mirrors the K record
corpus/k/verification/c23_kb_sum_up (kprove, circularity on the mid-execution
`#while` redex); upstream problem problems/imp/sum-up (see
programs/PROVENANCE.md). The program seeds `sum = 0`, `i = 1` itself, so the
loop counts UP under guard `i ≤ n` — the C12 no-split architecture
(precondition `0 ≤ n`, `spec := .trans toInv fromInv`) with the C1
accumulator arithmetic:

* **Transitivity** splits the run at the loop head: the prologue enters as an
  **Axiom** over `SRew` (the machine-checked `prologue_leg`, with logical
  frame `0 ≤ n`), weakened by **Consequence** into the ∃-packed loop
  invariant `inv` — loop counter `1 ≤ j ≤ n + 1` with the running total
  pinned by `2 * s = (j - 1) * j`.
* **Circularity** postulates `inv ⇒ post`; **Abstraction** (over the witness
  structure `Iter`) opens the ∃-pack so the invariant's constraints become
  real hypotheses; then a **case split on the guard** `j ≤ n`:
  - guard true: one loop iteration by the machine-checked `body_leg`
    (Axiom over `SRew` + Transitivity), and the back edge closes with the
    now-flushed circularity as an **Axiom** of `A ∪ C`, Consequence
    re-packing the invariant at `s + j`, `j + 1` (the accumulator equation
    is one distribute-and-`generalize j * j` omega step);
  - guard false: the composed exit path `exit_all` (Axiom over `SRew`);
    `j ≤ n + 1` and `¬(j ≤ n)` force `j = n + 1`, so `2 * s = n * (n + 1)`
    yields the closed form `s = n * (n + 1) / 2` (omega divides by the
    literal 2 after `generalize`-ing the product).

Nil-stack bookkeeping is the standard refinement: each iteration leaves one
emptied-block residue frame (`nilK`) on the k cell, the invariant carries a
`NilStack` continuation, and after loop exit the frames are drained at the
`Rewrites` level by induction on that stack (`drain`, one `nil_step` per
frame). `trans_multi`/`drain`/`exit_all` are execution-leg gluing, not
termination arguments: the claim proved is one-path reachability (partial
correctness), per the statement taxonomy of `KMiniPy.RL`.

Integer binders below are declared `Int` (definitionally `SortInt`, which is
an `abbrev`) so arithmetic side conditions elaborate at `Int` and `omega`
can read them; the frozen public `spec` stays at `SortInt`, and all
`C23KbSumUpLegs` lemmas accept the arguments unchanged. -/

open RLogic

namespace C23KbSumUp

open C23KbSumUpLegs

/-! ## The loop-head continuation shape -/

/-- One block-residue frame: the emptied statement list a `whileUnfold`ed
iteration leaves on the k cell (shape extracted from `body_leg`'s RHS). -/
def nilK (rest : SortK) : SortK :=
  SortK.kseq (SortKItem.inj_SortStmts SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») rest

/-- Continuations reachable below the While statement at the loop head: the
ground entry continuation under one `nilK` residue frame per completed
iteration. -/
inductive NilStack : SortK → Prop
  | base : NilStack loopRest
  | cons {r : SortK} : NilStack r → NilStack (nilK r)

/-- Glue an execution leg to a possibly-empty continuation: `MultiStep` is
the reflexive closure of `Rewrites`, and the left leg already took ≥ 1
step. -/
theorem trans_multi {a b c : SortGeneratedTopCell}
    (h : Rewrites a b) (h' : MultiStep b c) : Rewrites a c :=
  Or.elim h' (fun e => e ▸ h) fun r => h.tran r

/-- Drain the accumulated residue frames after loop exit: one `nil_step`
(`seqDone`) per `NilStack` layer, down to the ground continuation. -/
theorem drain (n s j : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (loopExit n s j rest) (loopExit n s j loopRest) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step n s j _) ih)

/-- The composed exit path from any invariant-shaped loop-head state with the
guard false: `exit_leg`, then the residue drain, then `epilogue_leg`. -/
theorem exit_all (n s j : Int) {rest : SortK} (h : n < j)
    (hs : NilStack rest) : Rewrites (loopCfg n s j rest) (final n s j) :=
  (trans_multi (exit_leg n s j rest h) (drain n s j hs)).tran
    (epilogue_leg n s j)

/-! ## The claim -/

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 0 ≤ n

/-- Postcondition: terminated, with `sum ↦ n*(n+1)/2` (the K claim's Gauss
closed form) and `i ↦ n + 1`. -/
def post (n : Int) : Pat := pat (final n ((n * (n + 1)) / 2) (n + 1))

/-- The ∃-packed loop invariant: at the loop head with counter
`1 ≤ j ≤ n + 1`, running total `2 * s = (j - 1) * j` (the sum
`1 + ⋯ + (j-1)`, doubled to stay division-free), and a residue-stack
continuation. -/
def inv (n : Int) : Pat := fun γ =>
  ∃ (s j : Int) (rest : SortK),
    γ = loopCfg n s j rest ∧ NilStack rest ∧ 1 ≤ j ∧ j ≤ n + 1 ∧
      2 * s = (j - 1) * j

/-! ## The circularity body, instance by instance -/

/-- The invariant's witness data, as a first-class index for Abstraction:
running total, counter, and continuation, plus the invariant's
constraints. -/
structure Iter (n : Int) : Type where
  s : Int
  j : Int
  rest : SortK
  hs : NilStack rest
  h1 : 1 ≤ j
  h2 : j ≤ n + 1
  h3 : 2 * s = (j - 1) * j

/-- The invariant instance at one witness. -/
def φIter (n : Int) (v : Iter n) : Pat := pat (loopCfg n v.s v.j v.rest)

/-- `inv` is exactly the ∃-packing of `φIter` (Consequence premise feeding
Abstraction). -/
theorem reshape (n : Int) : ∀ γ, inv n γ → ∃ v : Iter n, φIter n v γ :=
  fun _γ h => match h with
    | ⟨s, j, rest, hγ, hs, h1, h2, h3⟩ => ⟨⟨s, j, rest, hs, h1, h2, h3⟩, hγ⟩

/-- One derivation per invariant instance (the Abstraction premise), with the
guard case split. Guard true: `body_leg` (Axiom over `SRew`), then the
repacked invariant at `s + j`, `j + 1` is the flushed circularity — an Axiom
of `A ∪ C`. Guard false: `exit_all` (Axiom over `SRew`), then `j = n + 1`
forces the closed form. -/
theorem instF (n : Int) : ∀ v : Iter n,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv n, post n) ClaimSet.empty) .one
      (φIter n v, post n)
  | ⟨s, j, rest, hs, h1, h2, h3⟩ =>
    if hle : j ≤ n then
      .trans (RL.rw_leg (body_leg n s j rest hle))
        (.conseq
          (fun _γ hγ =>
            ⟨s + j, j + 1, nilK rest, hγ, hs.cons, by omega, by omega, by
              have e : j + 1 - 1 = j := by omega
              rw [e]
              rw [Int.mul_add j j 1, Int.mul_one]
              rw [Int.sub_mul, Int.one_mul] at h3
              revert h3
              generalize j * j = m
              intro h3
              omega⟩)
          (RL.axm' (c := (inv n, post n)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all n s j (by omega) hs))
        (fun _γ hγ => by
          have hj : j = n + 1 := by omega
          rw [hj] at h3
          have e : n + 1 - 1 = n := by omega
          rw [e] at h3
          have hsum : s = n * (n + 1) / 2 := by
            revert h3
            generalize n * (n + 1) = m
            intro h3
            omega
          show _γ = final n ((n * (n + 1)) / 2) (n + 1)
          rw [hγ, hsum, hj])

/-! ## The derivation -/

/-- `pre ⇒ inv`: the prologue leg as an Axiom over `SRew` with logical frame
`0 ≤ n`, weakened by Consequence into the invariant at `s = 0`, `j = 1`,
ground continuation. -/
theorem toInv (n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one (pre n, inv n) :=
  .conseq (fun _ h => h)
    (RL.axm (c := (pat (init n), pat (loopCfg n 0 1 loopRest))) (0 ≤ n)
      (Or.inl ⟨init n, loopCfg n 0 1 loopRest, prologue_leg n, rfl⟩))
    (fun _γ h => match h with
      | ⟨hγ, hn⟩ => ⟨0, 1, loopRest, hγ, .base, by omega, by omega, by omega⟩)

/-- `inv ⇒ post`: Circularity postulates the claim; Abstraction opens the
∃-pack; `instF` proves every instance, using the postulated claim on the
back edge. -/
theorem fromInv (n : Int) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv n, post n) :=
  .circ (.conseq (reshape n) (.abstr (instF n)) (fun _ h => h))

/-- C23. For every `n ≥ 0`, `kb_sum_up` reaches the terminal state with
`sum ↦ n*(n+1)/2` and `i ↦ n + 1`: the one-path reachability claim
`pre n ⇒∃ post n`, derived in the OOPSLA'16 proof system over the
machine-checked execution legs of `C23KbSumUpLegs` — the Lean mirror of the
K record's kprove claim. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) :=
  .trans (toInv n) (fromInv n)

end C23KbSumUp
