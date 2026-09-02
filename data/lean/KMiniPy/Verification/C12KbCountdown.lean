import KMiniPy.Verification.C12KbCountdownLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (n : Int) parameter on the claim family

/-! # C12: `kb_countdown` — the countdown loop drains `n` to exactly 0

`spec n : RLOne (pre n) (post n)` derives, in the OOPSLA'16 proof system
transcribed in `KMiniPy.RL`, the one-path reachability claim of C12: from
`init n` with `0 ≤ n`, the program reaches the terminal state with `n ↦ 0`.
This is the first loop-program KleverBench mirror: the K-side record
data/k/verification/c12_kb_countdown proves the same claim by kprove (a
circularity anchored on the mid-execution `#while` redex); upstream problem
problems/imp/countdown (see programs/PROVENANCE.md). The derivation follows
the C1SumToN architecture, simpler: module-level (no call frame), one
variable, no accumulator arithmetic.

* **Transitivity** splits the run at the loop head: the prologue enters as an
  **Axiom** over `SRew` (the machine-checked `prologue_leg`, with logical
  frame `0 ≤ n`), weakened by **Consequence** into the ∃-packed loop
  invariant `inv` — the Lean form of the K record's circularity claim
  `n = I` with `I ≥ 0`.
* **Circularity** postulates `inv ⇒ post`; **Abstraction** (over the witness
  structure `Iter`) opens the ∃-pack so the invariant's constraints become
  real hypotheses; then a **case split on the guard** `0 < i`:
  - guard true: one loop iteration by the machine-checked `body_leg`
    (Axiom over `SRew` + Transitivity), and the back edge closes with the
    now-flushed circularity as an **Axiom** of `A ∪ C`, Consequence
    re-packing the invariant at `i - 1` (`0 ≤ i - 1` from the guard);
  - guard false: the composed exit path `exit_all` (Axiom over `SRew`);
    `0 ≤ i` and `¬(0 < i)` force `i = 0`, so the exit state IS `final 0`.

The nil-stack refinement is the same as C1's: each iteration leaves one
emptied-block residue frame (`nilK`) on the k cell, so the invariant carries
a `NilStack` continuation, and after loop exit the frames are drained at the
`Rewrites` level by induction on that stack (`drain`, one `nil_step` per
frame). `trans_multi`/`drain`/`exit_all` are execution-leg gluing, not
termination arguments: the claim proved is one-path reachability (partial
correctness), per the statement taxonomy of `KMiniPy.RL`.

Integer binders below are declared `Int` (definitionally `SortInt`, which is
an `abbrev`) so arithmetic side conditions elaborate at `Int` and `omega`
can read them; the frozen public `spec` stays at `SortInt`, and all
`C12KbCountdownLegs` lemmas accept the arguments unchanged. -/

open RLogic

namespace C12KbCountdown

open C12KbCountdownLegs

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
the reflexive closure of `Rewrites`, and the left leg already took ≥ 1 step
(namespace-local counterpart of the C1 helper). -/
theorem trans_multi {a b c : SortGeneratedTopCell}
    (h : Rewrites a b) (h' : MultiStep b c) : Rewrites a c :=
  Or.elim h' (fun e => e ▸ h) fun r => h.tran r

/-- Drain the accumulated residue frames after loop exit: one `nil_step`
(`seqDone`) per `NilStack` layer, down to the ground continuation. -/
theorem drain (n : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (loopExit n rest) (loopExit n loopRest) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step n _) ih)

/-- The composed exit path from any invariant-shaped loop-head state with the
guard false: `exit_leg`, then the residue drain, then `epilogue_leg`. -/
theorem exit_all (n : Int) {rest : SortK} (h : n ≤ 0)
    (hs : NilStack rest) : Rewrites (loopCfg n rest) (final n) :=
  (trans_multi (exit_leg n rest h) (drain n hs)).tran (epilogue_leg n)

/-! ## The claim -/

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 0 ≤ n

/-- Postcondition: terminated, with `n ↦ 0` (the K claim's `?F ==Int 0`). -/
def post (n : Int) : Pat := pat (final 0)

/-- The ∃-packed loop invariant: at the loop head with value `i ≥ 0` and a
residue-stack continuation (the K record's circularity claim `n = I ≥ 0`). -/
def inv (n : Int) : Pat := fun γ =>
  ∃ (i : Int) (rest : SortK), γ = loopCfg i rest ∧ NilStack rest ∧ 0 ≤ i

/-! ## The circularity body, instance by instance -/

/-- The invariant's witness data, as a first-class index for Abstraction:
loop value and continuation, plus the invariant's constraints. -/
structure Iter : Type where
  i : Int
  rest : SortK
  hs : NilStack rest
  h1 : 0 ≤ i

/-- The invariant instance at one witness. -/
def φIter (v : Iter) : Pat := pat (loopCfg v.i v.rest)

/-- `inv` is exactly the ∃-packing of `φIter` (Consequence premise feeding
Abstraction). -/
theorem reshape (n : Int) : ∀ γ, inv n γ → ∃ v : Iter, φIter v γ :=
  fun _γ h => match h with
    | ⟨i, rest, hγ, hs, h1⟩ => ⟨⟨i, rest, hs, h1⟩, hγ⟩

/-- One derivation per invariant instance (the Abstraction premise), with the
guard case split. Guard true: `body_leg` (Axiom over `SRew`), then the
repacked invariant is the flushed circularity — an Axiom of `A ∪ C`. Guard
false: `exit_all` (Axiom over `SRew`), with `i = 0` forced by the guard and
the invariant bound. -/
theorem instF (n : Int) : ∀ v : Iter,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv n, post n) ClaimSet.empty) .one
      (φIter v, post n)
  | ⟨i, rest, hs, h1⟩ =>
    if hlt : 0 < i then
      .trans (RL.rw_leg (body_leg i rest hlt))
        (.conseq
          (fun _γ hγ => ⟨i - 1, nilK rest, hγ, hs.cons, by omega⟩)
          (RL.axm' (c := (inv n, post n)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all i (by omega) hs))
        (fun _γ hγ => by
          have hi : i = 0 := by omega
          exact Eq.trans hγ (congrArg final hi))

/-! ## The derivation -/

/-- `pre ⇒ inv`: the prologue leg as an Axiom over `SRew` with logical frame
`0 ≤ n`, weakened by Consequence into the invariant at `i = n`, ground
continuation. -/
theorem toInv (n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one (pre n, inv n) :=
  .conseq (fun _ h => h)
    (RL.axm (c := (pat (init n), pat (loopCfg n loopRest))) (0 ≤ n)
      (Or.inl ⟨init n, loopCfg n loopRest, prologue_leg n, rfl⟩))
    (fun _γ h => match h with
      | ⟨hγ, hn⟩ => ⟨n, loopRest, hγ, .base, hn⟩)

/-- `inv ⇒ post`: Circularity postulates the claim; Abstraction opens the
∃-pack; `instF` proves every instance, using the postulated claim on the
back edge. -/
theorem fromInv (n : Int) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv n, post n) :=
  .circ (.conseq (reshape n) (.abstr (instF n)) (fun _ h => h))

/-- C12. For every `n ≥ 0`, `kb_countdown` reaches the terminal state with
`n ↦ 0`: the one-path reachability claim `pre n ⇒∃ post n`, derived in the
OOPSLA'16 proof system over the machine-checked execution legs of
`C12KbCountdownLegs` — the Lean mirror of the K record's kprove claim. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) :=
  .trans (toInv n) (fromInv n)

end C12KbCountdown
