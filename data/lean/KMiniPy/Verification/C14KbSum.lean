import KMiniPy.Verification.C14KbSumLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (n sum : Int) claim-family binders

/-! # C14: `kb_sum` — the summation loop adds `n + (n-1) + … + 1` to `sum`

`spec n sum : RLOne (pre n sum) (post n sum)` derives the one-path
reachability claim of C14: from `init n sum` with `0 ≤ n`, the program
reaches the terminal state with `n ↦ 0` and `sum ↦ sum + n*(n+1)/2` (the
Gauss closed form). Mirrors data/k/verification/c14_kb_sum; upstream
problem problems/imp/sum (programs/PROVENANCE.md).

The derivation is the C12 architecture (precondition `0 ≤ n`, no top-level
split) with C1-style accumulator arithmetic:

* **Transitivity** splits the run at the loop head: the prologue enters as
  an **Axiom** over `SRew` with logical frame `0 ≤ n`, weakened by
  **Consequence** into the ∃-packed invariant `inv` — loop counter `i` and
  accumulator `s` tied by the ADDITIVE relation
  `2*s + i*(i+1) = 2*sum + n*(n+1)` (kept multiplied through by 2 so the
  division only ever appears at the exit, and the only nonlinear atoms are
  the squares `i*i` and `n*n`).
* **Circularity** postulates `inv ⇒ post`; **Abstraction** (over `Iter`)
  opens the ∃-pack; then a **case split on the guard** `0 < i`:
  - guard true: one iteration by `body_leg` (Axiom over `SRew` +
    Transitivity), the back edge closing with the flushed circularity as
    an **Axiom** of `A ∪ C`, Consequence re-packing the invariant at
    `i - 1`, `s + i` — the relation is re-established by distributing the
    products, generalizing the squares, and `omega`;
  - guard false: the composed exit path `exit_all` (Axiom over `SRew`);
    `0 ≤ i` and `¬(0 < i)` force `i = 0`, so the relation degenerates to
    `2*s = 2*sum + n*(n+1)` and `omega` (after generalizing the product)
    recovers `s = sum + n*(n+1)/2` — evenness of `n*(n+1)` comes for free
    from the doubled equation.

Nil-stack bookkeeping, binder discipline (helpers at `Int`, public `spec`
at `SortInt`) exactly as C12. -/

open RLogic

namespace C14KbSum

open C14KbSumLegs

/-! ## The loop-head continuation shape -/

/-- One block-residue frame (shape from `body_leg`'s RHS). -/
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
theorem drain (n s : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (loopExit n s rest) (loopExit n s loopRest) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step n s _) ih)

/-- Composed exit path from any invariant-shaped loop-head state with the
guard false: exit, drain, epilogue. -/
theorem exit_all (n s : Int) {rest : SortK} (h : n ≤ 0)
    (hs : NilStack rest) : Rewrites (loopCfg n s rest) (final n s) :=
  (trans_multi (exit_leg n s rest h) (drain n s hs)).tran (epilogue_leg n s)

/-! ## The claim -/

/-- Precondition: at program start, with `0 ≤ n` as a logical constraint. -/
def pre (n sum : Int) : Pat := fun γ => γ = init n sum ∧ 0 ≤ n

/-- Postcondition: terminated with `n ↦ 0` and the Gauss closed form
`sum ↦ sum + n*(n+1)/2` (the K claim's ensures; `/` is Int ediv, exact here
because `n*(n+1)` is even). -/
def post (n sum : Int) : Pat := pat (final 0 (sum + (n * (n + 1)) / 2))

/-- The ∃-packed loop invariant: at the loop head with counter `i ≥ 0` and
accumulator `s`, tied by the doubled additive relation (only the squares
`i*i`, `n*n` are nonlinear once distributed). -/
def inv (n sum : Int) : Pat := fun γ =>
  ∃ (i s : Int) (rest : SortK),
    γ = loopCfg i s rest ∧ NilStack rest ∧ 0 ≤ i ∧
      2 * s + i * (i + 1) = 2 * sum + n * (n + 1)

/-! ## The circularity body, instance by instance -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (n sum : Int) : Type where
  i : Int
  s : Int
  rest : SortK
  hs : NilStack rest
  h1 : 0 ≤ i
  h2 : 2 * s + i * (i + 1) = 2 * sum + n * (n + 1)

/-- The invariant instance at one witness. -/
def φIter (n sum : Int) (v : Iter n sum) : Pat := pat (loopCfg v.i v.s v.rest)

/-- `inv` is exactly the ∃-packing of `φIter` (Consequence premise feeding
Abstraction). -/
theorem reshape (n sum : Int) :
    ∀ γ, inv n sum γ → ∃ v : Iter n sum, φIter n sum v γ :=
  fun _γ h => match h with
    | ⟨i, s, rest, hγ, hs, h1, h2⟩ => ⟨⟨i, s, rest, hs, h1, h2⟩, hγ⟩

/-- One derivation per invariant instance: guard true takes `body_leg` and
re-packs at `i - 1`, `s + i` (the flushed circularity as an Axiom of
`A ∪ C`); guard false exits with `i = 0` forced and the Gauss slot closed
by generalize-the-product + `omega`. -/
theorem instF (n sum : Int) : ∀ v : Iter n sum,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv n sum, post n sum) ClaimSet.empty) .one
      (φIter n sum v, post n sum)
  | ⟨i, s, rest, hs, h1, h2⟩ =>
    if hlt : 0 < i then
      .trans (RL.rw_leg (body_leg i s rest hlt))
        (.conseq
          (fun _γ hγ => ⟨i - 1, s + i, nilK rest, hγ, hs.cons, by omega, by
            simp only [Int.mul_add, Int.mul_sub, Int.sub_mul,
              Int.mul_one, Int.one_mul] at h2 ⊢
            generalize hii : i * i = a at h2 ⊢
            generalize hnn : n * n = b at h2 ⊢
            omega⟩)
          (RL.axm' (c := (inv n sum, post n sum)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all i s (by omega) hs))
        (fun _γ hγ => by
          have hi : i = 0 := by omega
          have hsum : s = sum + (n * (n + 1)) / 2 := by
            subst hi
            simp only [Int.zero_add, Int.zero_mul, Int.add_zero] at h2
            generalize hp : n * (n + 1) = p at h2 ⊢
            omega
          show _γ = final 0 (sum + (n * (n + 1)) / 2)
          rw [hγ, hi, hsum])

/-! ## The derivation -/

/-- `pre ⇒ inv`: the prologue leg as an Axiom over `SRew` with logical frame
`0 ≤ n`, weakened by Consequence into the invariant at `i = n`, `s = sum`
(the relation is `rfl`-true there), ground continuation. -/
theorem toInv (n sum : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one (pre n sum, inv n sum) :=
  .conseq (fun _ h => h)
    (RL.axm (c := (pat (init n sum), pat (loopCfg n sum loopRest))) (0 ≤ n)
      (Or.inl ⟨init n sum, loopCfg n sum loopRest, prologue_leg n sum, rfl⟩))
    (fun _γ h => match h with
      | ⟨hγ, hn⟩ => ⟨n, sum, loopRest, hγ, .base, hn, rfl⟩)

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (n sum : Int) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv n sum, post n sum) :=
  .circ (.conseq (reshape n sum) (.abstr (instF n sum)) (fun _ h => h))

/-- C14. For every `n ≥ 0` and any `sum`, `kb_sum` reaches the terminal
state with `n ↦ 0` and `sum ↦ sum + n*(n+1)/2` — the K claim's Gauss-form
ensures, derived in the OOPSLA'16 proof system over the machine-checked
execution legs of `C14KbSumLegs`. -/
theorem spec (n sum : SortInt) : RLOne (pre n sum) (post n sum) :=
  .trans (toInv n sum) (fromInv n sum)

end C14KbSum
