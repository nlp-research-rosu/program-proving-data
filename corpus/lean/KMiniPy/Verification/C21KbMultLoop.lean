import KMiniPy.Verification.C21KbMultLoopLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (n a : Int) claim-family binders

/-! # C21: `kb_mult_loop` — repeated addition computes `a * max n 0`

`spec n a : RLOne (pre n a) (post n a)` derives the one-path reachability
claim of C21: from `init n a` for ARBITRARY integers, the program reaches
the terminal state with `res ↦ a * max n 0`, `n` drained to `min n 0`, and
`a` unchanged. Mirrors corpus/k/verification/c21_kb_mult_loop; upstream
problem problems/imp/mult-loop (programs/PROVENANCE.md).

The program seeds `res = 0` itself and has NO precondition, so the
derivation follows the C13 architecture: a top-level **Case Analysis** on
whether the loop runs at all — the piecewise `min`/`max` closed form
splits into two linear sides:

* `n ≤ 0` (no iterations): the guard is false on arrival, so the whole run
  is one composed `Rewrites` leg (prologue, exit at the ground
  continuation, epilogue) entering as an **Axiom** over `SRew`;
  `min n 0 = n` and `a * max n 0 = a * 0 = 0` close the slots.
* `0 < n` (the loop runs): Transitivity through the ∃-packed invariant
  `inv` — loop counter `i ≥ 0` with accumulator relation
  `r + a * i = a * n` and the side condition `0 < n` carried as a constant
  conjunct — then **Circularity**: guard true takes `body_leg` and
  re-packs at `(i - 1, r + a)`; guard false forces `i = 0` (so
  `r = a * n`), and `min n 0 = 0`, `max n 0 = n` close the slots.

Nil-stack bookkeeping, binder discipline (helpers at `Int`, public `spec`
at `SortInt`) exactly as C12/C13. -/

open RLogic

namespace C21KbMultLoop

open C21KbMultLoopLegs

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
theorem drain (n a res : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (loopExit n a res rest) (loopExit n a res loopRest) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step n a res _) ih)

/-- Composed exit path from any invariant-shaped loop-head state with the
guard false: exit, drain, epilogue. -/
theorem exit_all (n a res : Int) {rest : SortK} (h : n ≤ 0)
    (hs : NilStack rest) : Rewrites (loopCfg n a res rest) (final n a res) :=
  (trans_multi (exit_leg n a res rest h) (drain n a res hs)).tran
    (epilogue_leg n a res)

/-! ## The claim -/

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (n a : Int) : Pat := pat (init n a)

/-- Postcondition: terminated with `n ↦ min n 0`, `a` unchanged, and
`res ↦ a * max n 0` — the piecewise closed form of the counting loop. -/
def post (n a : Int) : Pat := pat (final (min n 0) a (a * max n 0))

/-- The ∃-packed loop invariant (loop side, `0 < n` carried as a constant
conjunct): at the loop head with counter `i ≥ 0` and accumulator relation
`r + a * i = a * n` (the remaining iterations complete the product). -/
def inv (n a : Int) : Pat := fun γ =>
  ∃ (i r : Int) (rest : SortK),
    γ = loopCfg i a r rest ∧ NilStack rest ∧ 0 ≤ i ∧ r + a * i = a * n ∧ 0 < n

/-! ## The loop side: Circularity -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (n a : Int) : Type where
  i : Int
  r : Int
  rest : SortK
  hs : NilStack rest
  h0 : 0 ≤ i
  h1 : r + a * i = a * n
  h2 : 0 < n

def φIter (n a : Int) (v : Iter n a) : Pat := pat (loopCfg v.i a v.r v.rest)

theorem reshape (n a : Int) : ∀ γ, inv n a γ → ∃ v : Iter n a, φIter n a v γ :=
  fun _γ h => match h with
    | ⟨i, r, rest, hγ, hs, h0, h1, h2⟩ => ⟨⟨i, r, rest, hs, h0, h1, h2⟩, hγ⟩

/-- One derivation per invariant instance: guard true takes `body_leg` and
the flushed circularity (Axiom of `A ∪ C`), re-packing at `(i - 1, r + a)`
(`(r + a) + a * (i - 1) = a * n` by distributing and generalizing the
products); guard false forces `i = 0`, so `r = a * n`, and the carried
`0 < n` collapses `min`/`max` to close the slots. -/
theorem instF (n a : Int) : ∀ v : Iter n a,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv n a, post n a) ClaimSet.empty) .one
      (φIter n a v, post n a)
  | ⟨i, r, rest, hs, h0, h1, h2⟩ =>
    if hlt : 0 < i then
      .trans (RL.rw_leg (body_leg i a r rest hlt))
        (.conseq
          (fun _γ hγ =>
            ⟨i - 1, r + a, nilK rest, hγ, hs.cons, by omega, by
              rw [Int.mul_sub, Int.mul_one]
              revert h1
              generalize a * i = p
              generalize a * n = q
              intro h1
              omega, h2⟩)
          (RL.axm' (c := (inv n a, post n a)) (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all i a r (by omega) hs))
        (fun _γ hγ => by
          have hi : i = 0 := by omega
          rw [hi, Int.mul_zero, Int.add_zero] at h1
          have hmin : min n 0 = 0 := by omega
          have hmax : max n 0 = n := by omega
          show _γ = final (min n 0) a (a * max n 0)
          rw [hγ, hi, hmin, hmax, ← h1])

/-- `pre ∧ 0 < n ⇒ inv`: the prologue leg as an Axiom with the side
condition as logical frame, Consequence packing the invariant at
`i = n`, `r = 0` (`0 + a * n = a * n`). -/
theorem toInv (n a : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre n a γ ∧ 0 < n, inv n a) :=
  .conseq (fun _ h => h)
    (RL.axm (c := (pat (init n a), pat (loopCfg n a 0 loopRest))) (0 < n)
      (Or.inl ⟨init n a, loopCfg n a 0 loopRest, prologue_leg n a, rfl⟩))
    (fun _γ h => match h with
      | ⟨hγ, hn⟩ => ⟨n, 0, loopRest, hγ, .base, by omega, Int.zero_add _, hn⟩)

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (n a : Int) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv n a, post n a) :=
  .circ (.conseq (reshape n a) (.abstr (instF n a)) (fun _ h => h))

/-- The loop side of the split. -/
theorem loopSide (n a : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre n a γ ∧ 0 < n, post n a) :=
  .trans (toInv n a) (fromInv n a)

/-! ## The no-loop side: one composed leg -/

/-- `n ≤ 0`: the guard is false on arrival — prologue, exit at the ground
continuation, epilogue, all at the `Rewrites` level; `min n 0 = n` and
`a * max n 0 = a * 0 = 0` are the seeded `res`. -/
theorem noloopSide (n a : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre n a γ ∧ n ≤ 0, post n a) :=
  if h : n ≤ 0 then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg ((prologue_leg n a).tran (exit_all n a 0 h .base)))
      (fun _γ hγ => by
        have hmin : min n 0 = n := by omega
        have hmax : max n 0 = 0 := by omega
        show _γ = final (min n 0) a (a * max n 0)
        rw [hγ, hmin, hmax, Int.mul_zero])
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Every pre-state satisfies one of the two sides. -/
theorem split (n a : Int) : ∀ γ, pre n a γ →
    (pre n a γ ∧ 0 < n) ∨ (pre n a γ ∧ n ≤ 0) :=
  fun _γ hγ => if h : 0 < n then Or.inl ⟨hγ, h⟩ else Or.inr ⟨hγ, by omega⟩

/-- C21. For all integers `n`, `a`, `kb_mult_loop` reaches the terminal
state with `res ↦ a * max n 0` (multiplication by repeated addition), `n`
drained to `min n 0`, and `a` unchanged — derived with Case Analysis over
loop-runs/no-op plus Circularity. -/
theorem spec (n a : SortInt) : RLOne (pre n a) (post n a) :=
  .conseq (split n a) (.caseA (loopSide n a) (noloopSide n a)) (fun _ h => h)

end C21KbMultLoop
