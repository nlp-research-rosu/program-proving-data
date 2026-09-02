import KMiniPy.Verification.C24KbCountEvenLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (n : Int) claim-family binders

/-! # C24: `kb_count_even` — counting the even numbers in `[0, n)`

`spec n : RLOne (pre n) (post n)` derives the one-path reachability claim
of C24: from `init n` with `0 ≤ n`, the program reaches the terminal state
with `count ↦ (n + 1) / 2` (the number of even integers below `n`) and
`i ↦ n`. Mirrors data/k/verification/c24_kb_count_even.

The derivation is the C14 architecture (precondition `0 ≤ n`, no top-level
split), with the guard-true branch of the circularity body SUB-SPLIT on the
parity of the loop counter — the body's `if i % 2 == 0` executes along two
distinct proved legs:

* **Transitivity** splits the run at the loop head: the prologue enters as
  an **Axiom** over `SRew` with logical frame `0 ≤ n`, weakened by
  **Consequence** into the ∃-packed invariant `inv` — counter `j` and
  count `c` tied by the DOUBLED relation `2*c = j + j % 2` (kept multiplied
  through by 2 so division only appears at the exit; `omega` reads `%` and
  `/` by the literal 2 directly, no products arise).
* **Circularity** postulates `inv ⇒ post`; **Abstraction** (over `Iter`)
  opens the ∃-pack; then a **case split on the guard** `j < n`:
  - guard true, `j % 2 = 0`: one iteration by `body_even_leg` (Axiom over
    `SRew` + Transitivity), the back edge closing with the flushed
    circularity as an **Axiom** of `A ∪ C`, Consequence re-packing the
    invariant at `c + 1`, `j + 1` — `2*(c+1) = (j+1) + (j+1) % 2` by
    `omega` from the relation and the parity hypothesis;
  - guard true, `j % 2 ≠ 0` (so `= 1`, forced by `omega`): `body_odd_leg`
    leaves `c` fixed and re-packs at `c`, `j + 1`, again by `omega`;
  - guard false: the composed exit path `exit_all` (Axiom over `SRew`);
    `j ≤ n` and `¬(j < n)` force `j = n`, and the relation degenerates to
    `2*c = n + n % 2`, from which `omega` recovers `c = (n + 1) / 2`.

Nil-stack bookkeeping, binder discipline (helpers at `Int`, public `spec`
at `SortInt`) exactly as C14. -/

open RLogic

namespace C24KbCountEven

open C24KbCountEvenLegs

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
theorem drain (n c j : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (loopExit n c j rest) (loopExit n c j loopRest) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step n c j _) ih)

/-- Composed exit path from any invariant-shaped loop-head state with the
guard false: exit, drain, epilogue. -/
theorem exit_all (n c j : Int) {rest : SortK} (h : n ≤ j)
    (hs : NilStack rest) : Rewrites (loopCfg n c j rest) (final n c j) :=
  (trans_multi (exit_leg n c j rest h) (drain n c j hs)).tran (epilogue_leg n c j)

/-! ## The claim -/

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (n : Int) : Pat := fun γ => γ = init n ∧ 0 ≤ n

/-- Postcondition: terminated with `count ↦ (n + 1) / 2` — the number of
even integers in `[0, n)` — and `i ↦ n`. -/
def post (n : Int) : Pat := pat (final n ((n + 1) / 2) n)

/-- The ∃-packed loop invariant: at the loop head with counter
`0 ≤ j ≤ n` and count `c` tied by the doubled relation `2*c = j + j % 2`
(the count of evens below `j`, kept division-free). -/
def inv (n : Int) : Pat := fun γ =>
  ∃ (c j : Int) (rest : SortK),
    γ = loopCfg n c j rest ∧ NilStack rest ∧ 0 ≤ j ∧ j ≤ n ∧
      2 * c = j + j % 2

/-! ## The circularity body, instance by instance -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (n : Int) : Type where
  c : Int
  j : Int
  rest : SortK
  hs : NilStack rest
  h1 : 0 ≤ j
  h2 : j ≤ n
  h3 : 2 * c = j + j % 2

/-- The invariant instance at one witness. -/
def φIter (n : Int) (v : Iter n) : Pat := pat (loopCfg n v.c v.j v.rest)

/-- `inv` is exactly the ∃-packing of `φIter` (Consequence premise feeding
Abstraction). -/
theorem reshape (n : Int) :
    ∀ γ, inv n γ → ∃ v : Iter n, φIter n v γ :=
  fun _γ h => match h with
    | ⟨c, j, rest, hγ, hs, h1, h2, h3⟩ => ⟨⟨c, j, rest, hs, h1, h2, h3⟩, hγ⟩

/-- One derivation per invariant instance: guard true sub-splits on the
parity of `j` — `body_even_leg` re-packs at `c + 1`, `j + 1`,
`body_odd_leg` at `c`, `j + 1` (the flushed circularity as an Axiom of
`A ∪ C` in both); guard false exits with `j = n` forced and `omega`
reading `c = (n + 1) / 2` off the doubled relation. -/
theorem instF (n : Int) : ∀ v : Iter n,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv n, post n) ClaimSet.empty) .one
      (φIter n v, post n)
  | ⟨c, j, rest, hs, h1, h2, h3⟩ =>
    if hlt : j < n then
      if hpar : j % 2 = 0 then
        .trans (RL.rw_leg (body_even_leg n c j rest hlt hpar))
          (.conseq
            (fun _γ hγ => ⟨c + 1, j + 1, nilK rest, hγ, hs.cons,
              by omega, by omega, by omega⟩)
            (RL.axm' (c := (inv n, post n)) (Or.inr (Or.inr (Or.inl rfl))))
            (fun _ h => h))
      else
        .trans (RL.rw_leg (body_odd_leg n c j rest hlt (by omega : j % 2 = 1)))
          (.conseq
            (fun _γ hγ => ⟨c, j + 1, nilK rest, hγ, hs.cons,
              by omega, by omega, by omega⟩)
            (RL.axm' (c := (inv n, post n)) (Or.inr (Or.inr (Or.inl rfl))))
            (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all n c j (by omega) hs))
        (fun _γ hγ => by
          have hj : j = n := by omega
          have hc : c = (n + 1) / 2 := by omega
          show _γ = final n ((n + 1) / 2) n
          rw [hγ, hj, hc])

/-! ## The derivation -/

/-- `pre ⇒ inv`: the prologue leg as an Axiom over `SRew` with logical frame
`0 ≤ n`, weakened by Consequence into the invariant at `c = 0`, `j = 0`
(the relation is closed by `decide` there), ground continuation. -/
theorem toInv (n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one (pre n, inv n) :=
  .conseq (fun _ h => h)
    (RL.axm (c := (pat (init n), pat (loopCfg n 0 0 loopRest))) (0 ≤ n)
      (Or.inl ⟨init n, loopCfg n 0 0 loopRest, prologue_leg n, rfl⟩))
    (fun _γ h => match h with
      | ⟨hγ, hn⟩ => ⟨0, 0, loopRest, hγ, .base, by omega, hn, by decide⟩)

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (n : Int) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv n, post n) :=
  .circ (.conseq (reshape n) (.abstr (instF n)) (fun _ h => h))

/-- C24. For every `n ≥ 0`, `kb_count_even` reaches the terminal state with
`count ↦ (n + 1) / 2` — the number of even integers in `[0, n)` — and
`i ↦ n`, derived in the OOPSLA'16 proof system over the machine-checked
execution legs of `C24KbCountEvenLegs`, with the guard-true circularity
branch sub-split on the parity of the counter. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) :=
  .trans (toInv n) (fromInv n)

end C24KbCountEven
