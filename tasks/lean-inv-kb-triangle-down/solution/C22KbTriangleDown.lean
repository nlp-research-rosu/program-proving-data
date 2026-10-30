import KMiniPy.Verification.C22KbTriangleDownLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (n : Int) parameter on the claim family

/-! # C22: `kb_triangle_down` — the descending triangle sum reaches Gauss

`spec n : RLOne (pre n) (post n)` derives the one-path reachability claim of
C22: from `init n` for an ARBITRARY integer (the program itself seeds
`sum = 0`), the program reaches the terminal state with `n ↦ min n 0` and
`sum ↦ (max n 0 * (max n 0 + 1)) / 2` — the descending accumulation
`n + (n-1) + ⋯ + 1` written as a piecewise closed form that is total in `n`.
Mirrors the K record corpus/k/verification/c22_kb_triangle_down; upstream
problem problems/imp/triangle-down (programs/PROVENANCE.md).

Like C13, the piecewise closed form calls for a top-level **Case Analysis**
on whether the loop runs at all:

* `n ≤ 0` (no iterations): the guard is false on arrival, so the whole run
  is one composed `Rewrites` leg (prologue, exit at the ground continuation,
  epilogue) entering as an **Axiom** over `SRew`; `min n 0 = n` and
  `max n 0 = 0` (so the sum slot is `(0 * (0 + 1)) / 2 = 0`, the seeded
  accumulator) close the slots.
* `0 < n` (the loop runs): Transitivity through the ∃-packed invariant
  `inv` — loop value `i ≥ 0`, accumulator `s` with the descending-sum
  relation `2*s + i*(i+1) = n*(n+1)`, and the side condition `0 < n`
  carried as a constant conjunct — then **Circularity**: guard true takes
  `body_leg` (`sum += n; n -= 1`) and re-packs at `(i - 1, s + i)`; guard
  false forces `i = 0`, so `2*s = n*(n+1)` yields the Gauss slot
  `s = (n*(n+1))/2` (Int `ediv` by the literal 2, discharged by
  generalizing the product for `omega`), and `min n 0 = 0`,
  `max n 0 = n` close the piecewise form.

Nil-stack bookkeeping, binder discipline (helpers at `Int`, public `spec`
at `SortInt`) exactly as C12/C13. -/

open RLogic

namespace C22KbTriangleDown

open C22KbTriangleDownLegs

/-- One block-residue frame (shape from `body_leg`'s RHS). -/
def nilK (rest : SortK) : SortK :=
  SortK.kseq (SortKItem.inj_SortStmts SortStmts.«.List{"___MINIPY-LEAN-SYNTAX_Stmts_Stmt_Stmts"}_Stmts») rest

/-- Continuations reachable at the loop head. -/
inductive NilStack : SortK → Prop
  | base : NilStack loopRest
  | cons {r : SortK} : NilStack r → NilStack (nilK r)

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

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (n : Int) : Pat := pat (init n)

/-- Postcondition: terminated with `n ↦ min n 0` and the descending
triangle sum `sum ↦ (max n 0 * (max n 0 + 1)) / 2`. -/
def post (n : Int) : Pat := pat (final (min n 0) ((max n 0 * (max n 0 + 1)) / 2))

/-- The ∃-packed loop invariant (loop side, `0 < n` carried as a constant
conjunct): at the loop head with value `i ≥ 0` and the descending-sum
relation `2*s + i*(i+1) = n*(n+1)`. -/
def inv (n : Int) : Pat := fun γ =>
  ∃ (i s : Int) (rest : SortK),
    γ = loopCfg i s rest ∧ NilStack rest ∧ 0 ≤ i ∧
      2*s + i*(i+1) = n*(n+1) ∧ 0 < n

/-! ## The loop side: Circularity -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (n : Int) : Type where
  i : Int
  s : Int
  rest : SortK
  hs : NilStack rest
  h1 : 0 ≤ i
  h2 : 2*s + i*(i+1) = n*(n+1)
  h3 : 0 < n

def φIter (n : Int) (v : Iter n) : Pat := pat (loopCfg v.i v.s v.rest)

theorem reshape (n : Int) : ∀ γ, inv n γ → ∃ v : Iter n, φIter n v γ :=
  fun _γ h => match h with
    | ⟨i, s, rest, hγ, hs, h1, h2, h3⟩ => ⟨⟨i, s, rest, hs, h1, h2, h3⟩, hγ⟩

/-- One derivation per invariant instance: guard true takes `body_leg` and
the flushed circularity (Axiom of `A ∪ C`), re-packing at `(i - 1, s + i)`
(distribute, generalize `i*i` and `n*(n+1)`, `omega`); guard false exits
with `i = 0` forced, so `2*s = n*(n+1)` gives the Gauss slot and the
carried `0 < n` resolves the piecewise `min`/`max`. -/
theorem instF (n : Int) : ∀ v : Iter n,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv n, post n) ClaimSet.empty) .one
      (φIter n v, post n)
  | ⟨i, s, rest, hs, h1, h2, h3⟩ =>
    if hlt : 0 < i then
      .trans (RL.rw_leg (body_leg i s rest hlt))
        (.conseq
          (fun _γ hγ =>
            ⟨i - 1, s + i, nilK rest, hγ, hs.cons, by omega, by
              have e : i - 1 + 1 = i := by omega
              rw [e, Int.mul_add, Int.sub_mul, Int.one_mul]
              rw [Int.mul_add, Int.mul_one] at h2
              revert h2
              generalize i * i = m
              generalize n * (n + 1) = w
              intro h2
              omega, h3⟩)
          (RL.axm' (c := (inv n, post n)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all i s (by omega) hs))
        (fun _γ hγ => by
          have hi : i = 0 := by omega
          rw [hi] at h2
          have hgauss : s = (n * (n + 1)) / 2 := by
            revert h2
            generalize n * (n + 1) = w
            intro h2
            omega
          have hmin : min n 0 = 0 := by omega
          have hmax : max n 0 = n := by omega
          show _γ = final (min n 0) ((max n 0 * (max n 0 + 1)) / 2)
          rw [hγ, hi, hmin, hmax, ← hgauss])

/-- `pre ∧ 0 < n ⇒ inv`: the prologue leg as an Axiom with the side
condition as logical frame, Consequence packing the invariant at
`(i, s) = (n, 0)`. -/
theorem toInv (n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre n γ ∧ 0 < n, inv n) :=
  .conseq (fun _ h => h)
    (RL.axm (c := (pat (init n), pat (loopCfg n 0 loopRest))) (0 < n)
      (Or.inl ⟨init n, loopCfg n 0 loopRest, prologue_leg n, rfl⟩))
    (fun _γ h => match h with
      | ⟨hγ, hn⟩ => ⟨n, 0, loopRest, hγ, .base, by omega, by
          generalize n * (n + 1) = w
          omega, hn⟩)

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (n : Int) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv n, post n) :=
  .circ (.conseq (reshape n) (.abstr (instF n)) (fun _ h => h))

/-- The loop side of the split. -/
theorem loopSide (n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre n γ ∧ 0 < n, post n) :=
  .trans (toInv n) (fromInv n)

/-! ## The no-loop side: one composed leg -/

/-- `n ≤ 0`: the guard is false on arrival — prologue, exit at the ground
continuation, epilogue, all at the `Rewrites` level; `min n 0 = n` and
the sum slot stays at the seeded `0` (`max n 0 = 0`). -/
theorem noloopSide (n : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre n γ ∧ n ≤ 0, post n) :=
  if h : n ≤ 0 then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg ((prologue_leg n).tran (exit_all n 0 h .base)))
      (fun _γ hγ => by
        have hmin : min n 0 = n := by omega
        have hmax : max n 0 = 0 := by omega
        have hz : ((0 * (0 + 1)) / 2 : Int) = 0 := by decide
        show _γ = final (min n 0) ((max n 0 * (max n 0 + 1)) / 2)
        rw [hγ, hmin, hmax, hz])
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Every pre-state satisfies one of the two sides. -/
theorem split (n : Int) : ∀ γ, pre n γ →
    (pre n γ ∧ 0 < n) ∨ (pre n γ ∧ n ≤ 0) :=
  fun _γ hγ => if h : 0 < n then Or.inl ⟨hγ, h⟩ else Or.inr ⟨hγ, by omega⟩

/-- C22. For every integer `n`, `kb_triangle_down` reaches the terminal
state with `n ↦ min n 0` and `sum ↦ (max n 0 * (max n 0 + 1)) / 2` — the
descending triangle sum's piecewise Gauss closed form, derived with Case
Analysis over loop-runs/no-op plus Circularity. -/
theorem spec (n : SortInt) : RLOne (pre n) (post n) :=
  .conseq (split n) (.caseA (loopSide n) (noloopSide n)) (fun _ h => h)

end C22KbTriangleDown
