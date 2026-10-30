import KMiniPy.Verification.C1Legs
import KMiniPy.RL

/-! # C1: `sum_to_n` meets the Gauss closed form — reachability-logic derivation

`gauss n : RLOne (pre n) (post n)` derives, in the OOPSLA'16 proof system
transcribed in `KMiniPy.RL`, the one-path reachability claim of C1: from
`init n` with `0 ≤ n`, the program reaches the final state with
`result = n·(n+1)/2`. The derivation mirrors the proof kprove constructs for
the K-side counterpart of this claim, and the shape of Figure 6(c) of the
OOPSLA'16 paper:

* **Transitivity** splits the run at the loop head: the prologue enters as an
  **Axiom** over `SRew` (the machine-checked `prologue_leg`, with logical
  frame `0 ≤ n`), weakened by **Consequence** into the ∃-packed loop
  invariant `inv`.
* **Circularity** postulates `inv ⇒ post`; **Abstraction** (over the witness
  type `Iter n`) opens the ∃-pack so the invariant's constraints become real
  hypotheses; then a **case split on the guard** `i ≤ n`:
  - guard true: one loop iteration by the machine-checked `body_leg`
    (Axiom over `SRew` + Transitivity), and the back edge closes with the
    now-flushed circularity as an **Axiom** of `A ∪ C`, Consequence carrying
    the arithmetic that re-establishes `inv` at `i+1`, `acc+i`;
  - guard false: the composed exit path `exit_all` (Axiom over `SRew`),
    Consequence carrying the arithmetic `i = n+1 ⊢ acc = n·(n+1)/2`.

The nil-stack refinement is forced by this semantics' while-unfolding: each
iteration leaves one emptied-block residue frame (`nilK`) on the k cell, so
the loop-head continuation is `NilStack` — `loopRest` under a stack of
residue frames — and after loop exit the frames are drained at the
`Rewrites` level by induction on that stack (`drain`, one `nil_step` per
frame). `Rewrites.trans_multi`/`drain`/`exit_all` are execution-leg gluing,
not termination arguments: the claim proved is one-path reachability
(partial correctness), per the statement taxonomy of `KMiniPy.RL` — which is
also why the former `Rewrites`-flavored `gauss_reaches` corollary is retired
in favor of this single reachability statement.

Integer binders below are declared `Int` (definitionally `SortInt`, which is
an `abbrev`) so arithmetic side conditions elaborate at `Int` and `omega`
can read them; all C1Legs lemmas accept the arguments unchanged. -/

open RLogic

/-- Glue an execution leg to a possibly-empty continuation: `MultiStep` is
the reflexive closure of `Rewrites`, and the left leg already took ≥ 1 step. -/
theorem Rewrites.trans_multi {a b c : SortGeneratedTopCell}
    (h : Rewrites a b) (h' : MultiStep b c) : Rewrites a c :=
  Or.elim h' (fun e => e ▸ h) fun r => h.tran r

namespace C1SumToN

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

/-- Drain the accumulated residue frames after loop exit: one `nil_step`
(`seqDone`) per `NilStack` layer, down to the ground continuation. -/
theorem drain (n i acc : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (loopExit n i acc rest) (loopExit n i acc loopRest) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr ((nil_step n i acc _).trans_multi ih)

/-- The composed exit path from any invariant-shaped loop-head state with the
guard false: `exit_leg`, then the residue drain, then `epilogue_leg`. -/
theorem exit_all (n i acc : Int) {rest : SortK} (h : n < i)
    (hs : NilStack rest) : Rewrites (loopCfg n i acc rest) (final (iV acc)) :=
  ((exit_leg n i acc rest h).trans_multi (drain n i acc hs)).tran
    (epilogue_leg n i acc)

/-! ## The claim -/

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 0 ≤ n

/-- Postcondition: terminated, with `result ↦ n·(n+1)/2`. -/
def post (n : Int) : Pat := pat (final (iV (n * (n + 1) / 2)))

/-- The ∃-packed loop invariant: at the loop head with counter `i`,
accumulator `acc`, a residue-stack continuation, `1 ≤ i ≤ n + 1`, and
`2·acc = (i-1)·i` (the running sum, kept division-free). -/
def inv (n : Int) : Pat := fun γ =>
  ∃ (i acc : Int) (rest : SortK), γ = loopCfg n i acc rest ∧ NilStack rest ∧
    1 ≤ i ∧ i ≤ n + 1 ∧ 2 * acc = (i - 1) * i

/-! ## The circularity body, instance by instance -/

/-- The invariant's witness data, as a first-class index for Abstraction:
counter, accumulator, continuation, plus the invariant's constraints. -/
structure Iter (n : Int) : Type where
  i : Int
  acc : Int
  rest : SortK
  hs : NilStack rest
  h1 : 1 ≤ i
  h2 : i ≤ n + 1
  h3 : 2 * acc = (i - 1) * i

/-- The invariant instance at one witness. -/
def φIter (n : Int) (v : Iter n) : Pat := pat (loopCfg n v.i v.acc v.rest)

/-- `inv` is exactly the ∃-packing of `φIter` (Consequence premise feeding
Abstraction). -/
theorem reshape (n : Int) : ∀ γ, inv n γ → ∃ v : Iter n, φIter n v γ :=
  fun _γ h => match h with
    | ⟨i, acc, rest, hγ, hs, h1, h2, h3⟩ => ⟨⟨i, acc, rest, hs, h1, h2, h3⟩, hγ⟩

/-- One derivation per invariant instance (the Abstraction premise), with the
guard case split. Guard true: `body_leg` (Axiom over `SRew`), then the
repacked invariant is the flushed circularity — an Axiom of `A ∪ C`. Guard
false: `exit_all` (Axiom over `SRew`), then `i = n + 1` forces the closed
form. -/
theorem instF (n : Int) : ∀ v : Iter n,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv n, post n) ClaimSet.empty) .one
      (φIter n v, post n)
  | ⟨i, acc, rest, hs, h1, h2, h3⟩ =>
    if hle : i ≤ n then
      .trans (RL.rw_leg (body_leg n i acc rest hle))
        (.conseq
          (fun _γ hγ =>
            ⟨i + 1, acc + i, nilK rest, hγ, hs.cons, by omega, by omega, by
              have e : i + 1 - 1 = i := by omega
              rw [e]
              rw [Int.mul_add i i 1, Int.mul_one]
              rw [Int.sub_mul, Int.one_mul] at h3
              revert h3
              generalize i * i = m
              intro h3
              omega⟩)
          (RL.axm' (c := (inv n, post n)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all n i acc (by omega) hs))
        (fun _γ hγ => by
          have hi : i = n + 1 := by omega
          rw [hi] at h3
          have e : n + 1 - 1 = n := by omega
          rw [e] at h3
          have hacc : acc = n * (n + 1) / 2 := by
            revert h3
            generalize n * (n + 1) = m
            intro h3
            omega
          exact Eq.trans hγ (congrArg (fun a => final (iV a)) hacc))

/-! ## The derivation -/

/-- `pre ⇒ inv`: the prologue leg as an Axiom over `SRew` with logical frame
`0 ≤ n`, weakened by Consequence into the invariant at `i = 1`, `acc = 0`,
ground continuation. -/
theorem toInv (n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one (pre n, inv n) :=
  .conseq (fun _ h => h)
    (RL.axm (c := (pat (init n), pat (loopCfg n 1 0 loopRest))) (0 ≤ n)
      (Or.inl ⟨init n, loopCfg n 1 0 loopRest, prologue_leg n, rfl⟩))
    (fun _γ h => match h with
      | ⟨hγ, hn⟩ => ⟨1, 0, loopRest, hγ, .base, by omega, by omega, by omega⟩)

/-- `inv ⇒ post`: Circularity postulates the claim; Abstraction opens the
∃-pack; `instF` proves every instance, using the postulated claim on the
back edge. -/
theorem fromInv (n : Int) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv n, post n) :=
  .circ (.conseq (reshape n) (.abstr (instF n)) (fun _ h => h))

/-- C1. For every `n ≥ 0`, `sum_to_n` reaches the Gauss closed form: the
one-path reachability claim `pre n ⇒∃ post n`, derived in the OOPSLA'16
proof system over the machine-checked execution legs of `C1Legs`. -/
theorem gauss (n : SortInt) : RLOne (pre n) (post n) :=
  .trans (toInv n) (fromInv n)

end C1SumToN
