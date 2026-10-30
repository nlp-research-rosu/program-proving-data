import KMiniPy.Verification.C15KbAddLoopLegs
import KMiniPy.RL

set_option linter.unusedVariables false  -- uniform (n res a : Int) claim-family binders

/-! # C15: `kb_add_loop` — `res` accumulates `a * max n 0`, with NO precondition

`spec n res a : RLOne (pre n res a) (post n res a)` derives the one-path
reachability claim of C15: from `init n res a` for ARBITRARY integers, the
program reaches the terminal state with `n ↦ min n 0`, `res ↦ res + a * max n 0`
and `a` unchanged. Mirrors corpus/k/verification/c15_kb_add_loop; upstream
problem problems/imp/add-loop (programs/PROVENANCE.md).

The derivation extends the C12 architecture with a top-level **Case
Analysis** on whether the loop runs at all — the piecewise `min`/`max`
closed form splits into two linear sides:

* `n ≤ 0` (no iterations): the guard is false on arrival, so the whole run
  is one composed `Rewrites` leg (prologue, exit at the ground continuation,
  epilogue); `min n 0 = n` and `max n 0 = 0` close the slots.
* `0 < n` (the loop runs): Transitivity through the ∃-packed invariant
  `inv` — counter `i ≥ 0` and accumulator `r` tied by the linear relation
  `r + a*i = res + a*n`, with the side condition `0 < n` carried as a
  constant conjunct — then **Circularity**: guard true takes `body_leg` and
  re-packs at `i - 1`, `r + a`; guard false forces `i = 0`, the relation
  degenerates to `r = res + a*n`, and `min n 0 = 0`, `max n 0 = n` close
  the slots.

Nil-stack bookkeeping, binder discipline (helpers at `Int`, public `spec`
at `SortInt`) exactly as C12. -/

open RLogic

namespace C15KbAddLoop

open C15KbAddLoopLegs

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
theorem drain (n res a : Int) {rest : SortK} (hs : NilStack rest) :
    MultiStep (loopExit n res a rest) (loopExit n res a loopRest) := by
  induction hs with
  | base => exact Or.inl rfl
  | cons _ ih => exact Or.inr (trans_multi (nil_step n res a _) ih)

/-- Composed exit path from any invariant-shaped loop-head state with the
guard false: exit, drain, epilogue. -/
theorem exit_all (n res a : Int) {rest : SortK} (h : n ≤ 0)
    (hs : NilStack rest) : Rewrites (loopCfg n res a rest) (final n res a) :=
  (trans_multi (exit_leg n res a rest h) (drain n res a hs)).tran
    (epilogue_leg n res a)

/-! ## The claim -/

/-- Precondition: at program start; the spec is total (no constraint). -/
def pre (n res a : Int) : Pat := pat (init n res a)

/-- Postcondition: terminated with `n ↦ min n 0`, `res ↦ res + a * max n 0`
and `a` unchanged. -/
def post (n res a : Int) : Pat := pat (final (min n 0) (res + a * max n 0) a)

/-- The ∃-packed loop invariant (loop side, `0 < n` carried as a constant
conjunct): at the loop head with counter `i ≥ 0` and accumulator `r` on the
line `r + a*i = res + a*n`. -/
def inv (n res a : Int) : Pat := fun γ =>
  ∃ (i r : Int) (rest : SortK),
    γ = loopCfg i r a rest ∧ NilStack rest ∧ 0 ≤ i ∧
      r + a * i = res + a * n ∧ 0 < n

/-! ## The loop side: Circularity -/

/-- Invariant witness data (Abstraction index). -/
structure Iter (n res a : Int) : Type where
  i : Int
  r : Int
  rest : SortK
  hs : NilStack rest
  h0 : 0 ≤ i
  hrel : r + a * i = res + a * n
  hn : 0 < n

def φIter (n res a : Int) (v : Iter n res a) : Pat :=
  pat (loopCfg v.i v.r a v.rest)

theorem reshape (n res a : Int) :
    ∀ γ, inv n res a γ → ∃ v : Iter n res a, φIter n res a v γ :=
  fun _γ h => match h with
    | ⟨i, r, rest, hγ, hs, h0, hrel, hn⟩ => ⟨⟨i, r, rest, hs, h0, hrel, hn⟩, hγ⟩

/-- One derivation per invariant instance: guard true takes `body_leg` and
re-packs at `i - 1`, `r + a` — the flushed circularity (Axiom of `A ∪ C`);
guard false exits with `i = 0` forced, the relation collapses to
`r = res + a*n`, and `0 < n` closes the `min`/`max` slots. -/
theorem instF (n res a : Int) : ∀ v : Iter n res a,
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty)
      (ClaimSet.insert (inv n res a, post n res a) ClaimSet.empty) .one
      (φIter n res a v, post n res a)
  | ⟨i, r, rest, hs, h0, hrel, hn⟩ =>
    if hlt : 0 < i then
      .trans (RL.rw_leg (body_leg i r a rest hlt))
        (.conseq
          (fun _γ hγ =>
            ⟨i - 1, r + a, nilK rest, hγ, hs.cons, by omega, by
              rw [Int.mul_sub, Int.mul_one]
              revert hrel
              generalize a * i = w
              generalize a * n = u
              intro hrel
              omega, hn⟩)
          (RL.axm' (c := (inv n res a, post n res a))
            (Or.inr (Or.inr (Or.inl rfl))))
          (fun _ h => h))
    else
      .conseq (fun _ h => h)
        (RL.rw_leg (exit_all i r a (by omega) hs))
        (fun _γ hγ => by
          have hi : i = 0 := by omega
          rw [hi] at hrel
          simp only [Int.mul_zero, Int.add_zero] at hrel
          have hmin : min n 0 = 0 := by omega
          have hmax : max n 0 = n := by omega
          show _γ = final (min n 0) (res + a * max n 0) a
          rw [hγ, hi, hmin, hmax, hrel])

/-- `pre ∧ 0 < n ⇒ inv`: the prologue leg as an Axiom with the side
condition as logical frame, Consequence packing the invariant at `i = n`,
`r = res` (the relation holds by `rfl`). -/
theorem toInv (n res a : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre n res a γ ∧ 0 < n, inv n res a) :=
  .conseq (fun _ h => h)
    (RL.axm (c := (pat (init n res a), pat (loopCfg n res a loopRest))) (0 < n)
      (Or.inl ⟨init n res a, loopCfg n res a loopRest, prologue_leg n res a, rfl⟩))
    (fun _γ h => match h with
      | ⟨hγ, hn⟩ => ⟨n, res, loopRest, hγ, .base, by omega, rfl, hn⟩)

/-- `inv ⇒ post`: Circularity + Abstraction over `Iter`. -/
theorem fromInv (n res a : Int) :
    RL SRew (ClaimSet.union ClaimSet.empty ClaimSet.empty) ClaimSet.empty
      .one (inv n res a, post n res a) :=
  .circ (.conseq (reshape n res a) (.abstr (instF n res a)) (fun _ h => h))

/-- The loop side of the split. -/
theorem loopSide (n res a : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre n res a γ ∧ 0 < n, post n res a) :=
  .trans (toInv n res a) (fromInv n res a)

/-! ## The no-loop side: one composed leg -/

/-- `n ≤ 0`: the guard is false on arrival — prologue, exit at the ground
continuation, epilogue, all at the `Rewrites` level; `min n 0 = n` and
`max n 0 = 0` close the slots. -/
theorem noloopSide (n res a : Int) :
    RL SRew ClaimSet.empty ClaimSet.empty .one
      (fun γ => pre n res a γ ∧ n ≤ 0, post n res a) :=
  if h : n ≤ 0 then
    .conseq (fun _ hp => hp.1)
      (RL.rw_leg ((prologue_leg n res a).tran (exit_all n res a h .base)))
      (fun _γ hγ => by
        have hmin : min n 0 = n := by omega
        have hmax : max n 0 = 0 := by omega
        show _γ = final (min n 0) (res + a * max n 0) a
        rw [hγ, hmin, hmax, Int.mul_zero, Int.add_zero])
  else
    .conseq (fun _ hp => absurd hp.2 h)
      (.refl (φ := fun _ => False))
      (fun _ f => f.elim)

/-- Every pre-state satisfies one of the two sides. -/
theorem split (n res a : Int) : ∀ γ, pre n res a γ →
    (pre n res a γ ∧ 0 < n) ∨ (pre n res a γ ∧ n ≤ 0) :=
  fun _γ hγ => if h : 0 < n then Or.inl ⟨hγ, h⟩ else Or.inr ⟨hγ, by omega⟩

/-- C15. For all integers `n`, `res`, `a`, `kb_add_loop` reaches the terminal
state with `n ↦ min n 0`, `res ↦ res + a * max n 0` and `a` unchanged — the
K claim's piecewise ensures, derived with Case Analysis over
loop-runs/no-op plus Circularity. -/
theorem spec (n res a : SortInt) : RLOne (pre n res a) (post n res a) :=
  .conseq (split n res a)
    (.caseA (loopSide n res a) (noloopSide n res a)) (fun _ h => h)

end C15KbAddLoop
