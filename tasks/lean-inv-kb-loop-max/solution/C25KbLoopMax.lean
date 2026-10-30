import KMiniPy.Verification.C25KbLoopMaxLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (a n : Int) claim-family binders

/-! # C25: `kb_loop_max` — the loop computes `max a (n - 1)`

`spec a n : RLOne (pre a n) (post a n)` derives the one-path reachability
claim of C25: from `init a n` with `1 ≤ n`, the program reaches the
terminal state with the running max `m ↦ max a (n - 1)` and counter
`i ↦ n`. Mirrors corpus/k/verification/c25_kb_loop_max.

The derivation is the C14 architecture (precondition `1 ≤ n`, no top-level
split) with a **sub-split inside the loop body** on the conditional
`if m < i`:

* **Transitivity** splits the run at the loop head: the prologue enters as
  an **Axiom** over `SRew` with logical frame `1 ≤ n`, weakened by
  **Consequence** into the ∃-packed invariant `inv` — counter `j ≤ n` and
  running max `m` tied by the piecewise relation
  `(j = 0 ∧ m = a) ∨ (1 ≤ j ∧ m = max a (j - 1))` (the first iteration is
  the only one where `m` may still be the untouched seed `a`).
* **Circularity** postulates `inv ⇒ post`; **Abstraction** (over `Iter`)
  opens the ∃-pack; then a **case split on the guard** `j < n`:
  - guard true, `m < j`: one iteration by `body_upd_leg` (the body's `if`
    fires, the new max IS `j`), the back edge closing with the flushed
    circularity as an **Axiom** of `A ∪ C`, Consequence re-packing the
    invariant at `(j, j + 1)` — `j = max a j` because either `j = 0` with
    `a = m < 0`, or `a ≤ max a (j-1) = m < j`; `omega` reads the `max`
    atoms after `rcases` on the disjunct;
  - guard true, `j ≤ m`: `body_noupd_leg` re-packs at `(m, j + 1)` —
    `m = max a j` by the same `rcases` + `omega`;
  - guard false: the composed exit path `exit_all` (Axiom over `SRew`);
    `j ≤ n` and `¬(j < n)` force `j = n`, `1 ≤ n` kills the `j = 0`
    disjunct, so `m = max a (n - 1)` closes the slot.

Nil-stack bookkeeping, binder discipline (helpers at `Int`, public `spec`
at `SortInt`) exactly as C14. -/

open RLogic

namespace C25KbLoopMax

open C25KbLoopMaxLegs

/-! ## The loop-head continuation shape -/

/-- One block-residue frame (shape from the body legs' RHS). -/
def nilK (rest : SortK) : SortK :=
  SortK.kseq (SortKItem.inj_SortStmts SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») rest

/-- Continuations reachable at the loop head. -/
inductive NilStack : SortK → Prop
  | base : NilStack loopRest
  | cons {r : SortK} : NilStack r → NilStack (nilK r)

/-- Glue an execution leg to a possibly-empty continuation. -/
theorem trans_multi {a b c : SortGeneratedTopCell}
    (h : Rewrites a b) (h' : MultiStep b c) : Rewrites a c :=
  Or.elim h' (fun e => e ▸ h) fun r => h.tran r

/-- Drain the residue frames after loop exit, one `nil_step` per layer. -/
theorem drain (a n m i : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (loopExit a n m i rest) (loopExit a n m i loopRest) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step a n m i _) ih)

/-- Composed exit path from any invariant-shaped loop-head state with the
guard false: exit, drain, epilogue. -/
theorem exit_all (a n m i : Int) {rest : SortK} (h : n ≤ i)
    (hs : NilStack rest) : Rewrites (loopCfg a n m i rest) (final a n m i) :=
  (trans_multi (exit_leg a n m i rest h) (drain a n m i hs)).tran
    (epilogue_leg a n m i)

/-! ## The claim -/

/-- Precondition: at program start, with `1 ≤ n` as a logical constraint. -/
def pre (a n : Int) : Pat := fun γ => γ = init a n ∧ 1 ≤ n

/-- Postcondition: terminated with `m ↦ max a (n - 1)` and `i ↦ n`. -/
def post (a n : Int) : Pat := pat (final a n (max a (n - 1)) n)

/-- The ∃-packed loop invariant (`1 ≤ n` carried as a constant conjunct):
at the loop head with counter `j ≤ n` and running max `m`, either untouched
seed (`j = 0`, `m = a`) or the max over the scanned prefix
(`m = max a (j - 1)`). -/
def inv (a n : Int) : Pat := fun γ =>
  ∃ (m j : Int) (rest : SortK),
    γ = loopCfg a n m j rest ∧ NilStack rest ∧ j ≤ n ∧
      ((j = 0 ∧ m = a) ∨ (1 ≤ j ∧ m = max a (j - 1))) ∧ 1 ≤ n

/-! ## The circularity body, instance by instance -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (a n : Int) : Type where
  m : Int
  j : Int
  rest : SortK
  hs : NilStack rest
  h1 : j ≤ n
  h2 : (j = 0 ∧ m = a) ∨ (1 ≤ j ∧ m = max a (j - 1))
  hn : 1 ≤ n

/-- The invariant instance at one witness. -/
def φIter (a n : Int) (v : Iter a n) : Pat := pat (loopCfg a n v.m v.j v.rest)

/-- `inv` is exactly the ∃-packing of `φIter` (Consequence premise feeding
Abstraction). -/
theorem reshape (a n : Int) :
    ∀ γ, inv a n γ → ∃ v : Iter a n, φIter a n v γ :=
  fun _γ h => match h with
    | ⟨m, j, rest, hγ, hs, h1, h2, hn⟩ => ⟨⟨m, j, rest, hs, h1, h2, hn⟩, hγ⟩

/-- One derivation per invariant instance: guard true sub-splits on the
body's `if m < j` — `body_upd_leg` re-packs at `(j, j + 1)`,
`body_noupd_leg` at `(m, j + 1)` (both back edges close with the flushed
circularity as an Axiom of `A ∪ C`, the piecewise relation re-established
by `rcases` + `omega` over the `max` atoms); guard false exits with `j = n`
forced and `m = max a (n - 1)` from the second disjunct. -/
theorem instF (a n : Int) : ∀ v : Iter a n,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv a n, post a n) ClaimSet.empty) .one
      (φIter a n v, post a n)
  | ⟨m, j, rest, hs, h1, h2, hn⟩ =>
    if hlt : j < n then
      if hupd : m < j then
        .trans (RL.rw_leg (body_upd_leg a n m j rest hlt hupd))
          (.conseq
            (fun _γ hγ => ⟨j, j + 1, nilK rest, hγ, hs.cons, by omega,
              Or.inr ⟨by omega, by
                rcases h2 with ⟨hj, hm⟩ | ⟨hj, hm⟩ <;> omega⟩, hn⟩)
            (RL.axm' (c := (inv a n, post a n)) (Or.inr (Or.inr (Or.inl rfl))))
            (fun _ h => h))
      else
        .trans (RL.rw_leg (body_noupd_leg a n m j rest hlt
            (show j ≤ m by omega)))
          (.conseq
            (fun _γ hγ => ⟨m, j + 1, nilK rest, hγ, hs.cons, by omega,
              Or.inr ⟨by omega, by
                rcases h2 with ⟨hj, hm⟩ | ⟨hj, hm⟩ <;> omega⟩, hn⟩)
            (RL.axm' (c := (inv a n, post a n)) (Or.inr (Or.inr (Or.inl rfl))))
            (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all a n m j (by omega) hs))
        (fun _γ hγ => by
          have hj : j = n := by omega
          have hm : m = max a (n - 1) := by
            rcases h2 with ⟨hj0, hma⟩ | ⟨hj1, hmm⟩ <;> omega
          show _γ = final a n (max a (n - 1)) n
          rw [hγ, hj, hm])

/-! ## The derivation -/

/-- `pre ⇒ inv`: the prologue leg as an Axiom over `SRew` with logical frame
`1 ≤ n`, weakened by Consequence into the invariant at `m = a`, `j = 0`
(the first disjunct), ground continuation. -/
theorem toInv (a n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one (pre a n, inv a n) :=
  .conseq (fun _ h => h)
    (RL.axm (c := (pat (init a n), pat (loopCfg a n a 0 loopRest))) (1 ≤ n)
      (Or.inl ⟨init a n, loopCfg a n a 0 loopRest, prologue_leg a n, rfl⟩))
    (fun _γ h => match h with
      | ⟨hγ, hn⟩ => ⟨a, 0, loopRest, hγ, .base, by omega, Or.inl ⟨rfl, rfl⟩, hn⟩)

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (a n : Int) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv a n, post a n) :=
  .circ (.conseq (reshape a n) (.abstr (instF a n)) (fun _ h => h))

/-- C25. For every `a` and `n ≥ 1`, `kb_loop_max` reaches the terminal
state with `m ↦ max a (n - 1)` and `i ↦ n` — the K claim's ensures, derived
in the OOPSLA'16 proof system over the machine-checked execution legs of
`C25KbLoopMaxLegs`. -/
theorem spec (a n : SortInt) : RLOne (pre a n) (post a n) :=
  .trans (toInv a n) (fromInv a n)

end C25KbLoopMax
